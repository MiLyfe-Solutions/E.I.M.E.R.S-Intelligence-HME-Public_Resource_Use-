import V185TrunkScan23Chunk1414

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8381784 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_8381784 : Nat := 118140960795 + 8381784 * 2 ^ 59
def prefixEnd_8381784 : Nat := 4983230072969 + 3 ^ 40 * 8381784 * 2
def baseEnd_8381784 : Nat := 1434627978054979821750961

theorem tailTrace_8381784 : CollatzResearch.WordTrace tailWord_8381784 prefixEnd_8381784 1434627978054979821750961 := by
  unfold tailWord_8381784
  simp only [CollatzResearch.WordTrace]
  refine ⟨152854388733117768792596203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203805851644157025056794937 152854388733117768792596203)
  ·
    refine ⟨229281583099676653188894305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152854388733117768792596203 229281583099676653188894305)
    ·
      refine ⟨171961187324757489891670729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229281583099676653188894305 171961187324757489891670729)
      ·
        refine ⟨128970890493568117418753047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171961187324757489891670729 128970890493568117418753047)
        ·
          refine ⟨193456335740352176128129571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128970890493568117418753047 193456335740352176128129571)
          ·
            refine ⟨290184503610528264192194357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193456335740352176128129571 290184503610528264192194357)
            ·
              refine ⟨27204797213487024768018221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290184503610528264192194357 27204797213487024768018221)
              ·
                refine ⟨10201798955057634288006833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27204797213487024768018221 10201798955057634288006833)
                ·
                  refine ⟨7651349216293225716005125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10201798955057634288006833 7651349216293225716005125)
                  ·
                    refine ⟨1434627978054979821750961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7651349216293225716005125 1434627978054979821750961)
                    ·
                      rfl

theorem cell23_8381784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_8381784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381784 prefixEnd_8381784 := by exact prefixLift 8381784
  have htrace : WordTrace (prefixWord ++ tailWord_8381784) baseStart_8381784 baseEnd_8381784 := by
    simpa [prefixWord, tailWord_8381784, baseEnd_8381784] using wordTrace_append hprefix tailTrace_8381784
  have hstable : (prefixWord ++ tailWord_8381784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381784).length < 2 ^ (prefixWord ++ tailWord_8381784).sum := by decide
  have hdescent : baseEnd_8381784 < baseStart_8381784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381804 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 4]
def baseStart_8381804 : Nat := 118140960795 + 8381804 * 2 ^ 59
def prefixEnd_8381804 : Nat := 4983230072969 + 3 ^ 40 * 8381804 * 2
def baseEnd_8381804 : Nat := 4303894203778029387002791

theorem tailTrace_8381804 : CollatzResearch.WordTrace tailWord_8381804 prefixEnd_8381804 4303894203778029387002791 := by
  unfold tailWord_8381804
  simp only [CollatzResearch.WordTrace]
  refine ⟨152854753463081540500460233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203806337950775387333946977 152854753463081540500460233)
  ·
    refine ⟨114641065097311155375345175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152854753463081540500460233 114641065097311155375345175)
    ·
      refine ⟨171961597645966733063017763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114641065097311155375345175 171961597645966733063017763)
      ·
        refine ⟨257942396468950099594526645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171961597645966733063017763 257942396468950099594526645)
        ·
          refine ⟨24182099668964071836986873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257942396468950099594526645 24182099668964071836986873)
          ·
            refine ⟨18136574751723053877740155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24182099668964071836986873 18136574751723053877740155)
            ·
              refine ⟨27204862127584580816610233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18136574751723053877740155 27204862127584580816610233)
              ·
                refine ⟨20403646595688435612457675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27204862127584580816610233 20403646595688435612457675)
                ·
                  refine ⟨30605469893532653418686513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20403646595688435612457675 30605469893532653418686513)
                  ·
                    refine ⟨22954102420149490064014885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30605469893532653418686513 22954102420149490064014885)
                    ·
                      refine ⟨4303894203778029387002791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22954102420149490064014885 4303894203778029387002791)
                      ·
                        rfl

theorem cell23_8381804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_8381804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381804 prefixEnd_8381804 := by exact prefixLift 8381804
  have htrace : WordTrace (prefixWord ++ tailWord_8381804) baseStart_8381804 baseEnd_8381804 := by
    simpa [prefixWord, tailWord_8381804, baseEnd_8381804] using wordTrace_append hprefix tailTrace_8381804
  have hstable : (prefixWord ++ tailWord_8381804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381804).length < 2 ^ (prefixWord ++ tailWord_8381804).sum := by decide
  have hdescent : baseEnd_8381804 < baseStart_8381804 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381808 : List Nat := [2, 1, 1, 1, 4, 2, 2, 5, 1, 2, 2]
def baseStart_8381808 : Nat := 118140960795 + 8381808 * 2 ^ 59
def prefixEnd_8381808 : Nat := 4983230072969 + 3 ^ 40 * 8381808 * 2
def baseEnd_8381808 : Nat := 4303896257700647371352773

theorem tailTrace_8381808 : CollatzResearch.WordTrace tailWord_8381808 prefixEnd_8381808 4303896257700647371352773 := by
  unfold tailWord_8381808
  simp only [CollatzResearch.WordTrace]
  refine ⟨152854826409074294842033039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203806435212099059789377385 152854826409074294842033039)
  ·
    refine ⟨229282239613611442263049559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152854826409074294842033039 229282239613611442263049559)
    ·
      refine ⟨343923359420417163394574339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229282239613611442263049559 343923359420417163394574339)
      ·
        refine ⟨515885039130625745091861509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343923359420417163394574339 515885039130625745091861509)
        ·
          refine ⟨96728444836992327204724033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 515885039130625745091861509 96728444836992327204724033)
          ·
            refine ⟨72546333627744245403543025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96728444836992327204724033 72546333627744245403543025)
            ·
              refine ⟨54409750220808184052657269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72546333627744245403543025 54409750220808184052657269)
              ·
                refine ⟨5100914083200767254936619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54409750220808184052657269 5100914083200767254936619)
                ·
                  refine ⟨7651371124801150882404929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100914083200767254936619 7651371124801150882404929)
                  ·
                    refine ⟨5738528343600863161803697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7651371124801150882404929 5738528343600863161803697)
                    ·
                      refine ⟨4303896257700647371352773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738528343600863161803697 4303896257700647371352773)
                      ·
                        rfl

theorem cell23_8381808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 5, 1, 2, 2].length) (baseStart_8381808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381808 prefixEnd_8381808 := by exact prefixLift 8381808
  have htrace : WordTrace (prefixWord ++ tailWord_8381808) baseStart_8381808 baseEnd_8381808 := by
    simpa [prefixWord, tailWord_8381808, baseEnd_8381808] using wordTrace_append hprefix tailTrace_8381808
  have hstable : (prefixWord ++ tailWord_8381808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381808).length < 2 ^ (prefixWord ++ tailWord_8381808).sum := by decide
  have hdescent : baseEnd_8381808 < baseStart_8381808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381824 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3]
def baseStart_8381824 : Nat := 118140960795 + 8381824 * 2 ^ 59
def prefixEnd_8381824 : Nat := 4983230072969 + 3 ^ 40 * 8381824 * 2
def baseEnd_8381824 : Nat := 4303904473391119308752699

theorem tailTrace_8381824 : CollatzResearch.WordTrace tailWord_8381824 prefixEnd_8381824 4303904473391119308752699 := by
  unfold tailWord_8381824
  simp only [CollatzResearch.WordTrace]
  refine ⟨152855118193045312208324263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203806824257393749611099017 152855118193045312208324263)
  ·
    refine ⟨229282677289567968312486395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152855118193045312208324263 229282677289567968312486395)
    ·
      refine ⟨343924015934351952468729593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229282677289567968312486395 343924015934351952468729593)
      ·
        refine ⟨257943011950763964351547195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343924015934351952468729593 257943011950763964351547195)
        ·
          refine ⟨386914517926145946527320793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257943011950763964351547195 386914517926145946527320793)
          ·
            refine ⟨290185888444609459895490595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386914517926145946527320793 290185888444609459895490595)
            ·
              refine ⟨435278832666914189843235893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290185888444609459895490595 435278832666914189843235893)
              ·
                refine ⟨40807390562523205297803365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435278832666914189843235893 40807390562523205297803365)
                ·
                  refine ⟨7651385730473100993338131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40807390562523205297803365 7651385730473100993338131)
                  ·
                    refine ⟨11477078595709651490007197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7651385730473100993338131 11477078595709651490007197)
                    ·
                      refine ⟨4303904473391119308752699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11477078595709651490007197 4303904473391119308752699)
                      ·
                        rfl

theorem cell23_8381824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_8381824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381824 prefixEnd_8381824 := by exact prefixLift 8381824
  have htrace : WordTrace (prefixWord ++ tailWord_8381824) baseStart_8381824 baseEnd_8381824 := by
    simpa [prefixWord, tailWord_8381824, baseEnd_8381824] using wordTrace_append hprefix tailTrace_8381824
  have hstable : (prefixWord ++ tailWord_8381824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381824).length < 2 ^ (prefixWord ++ tailWord_8381824).sum := by decide
  have hdescent : baseEnd_8381824 < baseStart_8381824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381827 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 2, 7]
def baseStart_8381827 : Nat := 118140960795 + 8381827 * 2 ^ 59
def prefixEnd_8381827 : Nat := 4983230072969 + 3 ^ 40 * 8381827 * 2
def baseEnd_8381827 : Nat := 1434635337944360932338395

theorem tailTrace_8381827 : CollatzResearch.WordTrace tailWord_8381827 prefixEnd_8381827 1434635337944360932338395 := by
  unfold tailWord_8381827
  simp only [CollatzResearch.WordTrace]
  refine ⟨305710345805079755929007735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203806897203386503952671823 305710345805079755929007735)
  ·
    refine ⟨458565518707619633893511603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305710345805079755929007735 458565518707619633893511603)
    ·
      refine ⟨687848278061429450840267405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458565518707619633893511603 687848278061429450840267405)
      ·
        refine ⟨257943104273036044065100277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687848278061429450840267405 257943104273036044065100277)
        ·
          refine ⟨24182166025597129131103151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257943104273036044065100277 24182166025597129131103151)
          ·
            refine ⟨36273249038395693696654727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24182166025597129131103151 36273249038395693696654727)
            ·
              refine ⟨54409873557593540544982091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36273249038395693696654727 54409873557593540544982091)
              ·
                refine ⟨81614810336390310817473137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54409873557593540544982091 81614810336390310817473137)
                ·
                  refine ⟨61211107752292733113104853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81614810336390310817473137 61211107752292733113104853)
                  ·
                    refine ⟨1434635337944360932338395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61211107752292733113104853 1434635337944360932338395)
                    ·
                      rfl

theorem cell23_8381827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 7].length) (baseStart_8381827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381827 prefixEnd_8381827 := by exact prefixLift 8381827
  have htrace : WordTrace (prefixWord ++ tailWord_8381827) baseStart_8381827 baseEnd_8381827 := by
    simpa [prefixWord, tailWord_8381827, baseEnd_8381827] using wordTrace_append hprefix tailTrace_8381827
  have hstable : (prefixWord ++ tailWord_8381827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381827).length < 2 ^ (prefixWord ++ tailWord_8381827).sum := by decide
  have hdescent : baseEnd_8381827 < baseStart_8381827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381847 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4]
def baseStart_8381847 : Nat := 118140960795 + 8381847 * 2 ^ 59
def prefixEnd_8381847 : Nat := 4983230072969 + 3 ^ 40 * 8381847 * 2
def baseEnd_8381847 : Nat := 4303916283446172718765093

theorem tailTrace_8381847 : CollatzResearch.WordTrace tailWord_8381847 prefixEnd_8381847 4303916283446172718765093 := by
  unfold tailWord_8381847
  simp only [CollatzResearch.WordTrace]
  refine ⟨305711075265007299344735795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203807383510004866229823863 305711075265007299344735795)
  ·
    refine ⟨458566612897510949017103693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305711075265007299344735795 458566612897510949017103693)
    ·
      refine ⟨171962479836566605881413885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458566612897510949017103693 171962479836566605881413885)
      ·
        refine ⟨64485929938712477205530207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 171962479836566605881413885 64485929938712477205530207)
        ·
          refine ⟨96728894908068715808295311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64485929938712477205530207 96728894908068715808295311)
          ·
            refine ⟨145093342362103073712442967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96728894908068715808295311 145093342362103073712442967)
            ·
              refine ⟨217640013543154610568664451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145093342362103073712442967 217640013543154610568664451)
              ·
                refine ⟨326460020314731915852996677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217640013543154610568664451 326460020314731915852996677)
                ·
                  refine ⟨61211253809012234222436877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326460020314731915852996677 61211253809012234222436877)
                  ·
                    refine ⟨22954220178379587833413829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61211253809012234222436877 22954220178379587833413829)
                    ·
                      refine ⟨4303916283446172718765093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22954220178379587833413829 4303916283446172718765093)
                      ·
                        rfl

theorem cell23_8381847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_8381847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381847 prefixEnd_8381847 := by exact prefixLift 8381847
  have htrace : WordTrace (prefixWord ++ tailWord_8381847) baseStart_8381847 baseEnd_8381847 := by
    simpa [prefixWord, tailWord_8381847, baseEnd_8381847] using wordTrace_append hprefix tailTrace_8381847
  have hstable : (prefixWord ++ tailWord_8381847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381847).length < 2 ^ (prefixWord ++ tailWord_8381847).sum := by decide
  have hdescent : baseEnd_8381847 < baseStart_8381847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381868 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 1, 3, 2]
def baseStart_8381868 : Nat := 118140960795 + 8381868 * 2 ^ 59
def prefixEnd_8381868 : Nat := 4983230072969 + 3 ^ 40 * 8381868 * 2
def baseEnd_8381868 : Nat := 4303927066539917136602497

theorem tailTrace_8381868 : CollatzResearch.WordTrace tailWord_8381868 prefixEnd_8381868 4303927066539917136602497 := by
  unfold tailWord_8381868
  simp only [CollatzResearch.WordTrace]
  refine ⟨152855920598965609965625129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203807894131954146620833505 152855920598965609965625129)
  ·
    refine ⟨114641940449224207474218847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152855920598965609965625129 114641940449224207474218847)
    ·
      refine ⟨171962910673836311211328271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114641940449224207474218847 171962910673836311211328271)
      ·
        refine ⟨257944366010754466816992407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171962910673836311211328271 257944366010754466816992407)
        ·
          refine ⟨386916549016131700225488611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257944366010754466816992407 386916549016131700225488611)
          ·
            refine ⟨580374823524197550338232917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386916549016131700225488611 580374823524197550338232917)
            ·
              refine ⟨6801267463174190043026167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 580374823524197550338232917 6801267463174190043026167)
              ·
                refine ⟨10201901194761285064539251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801267463174190043026167 10201901194761285064539251)
                ·
                  refine ⟨15302851792141927596808877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201901194761285064539251 15302851792141927596808877)
                  ·
                    refine ⟨5738569422053222848803329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15302851792141927596808877 5738569422053222848803329)
                    ·
                      refine ⟨4303927066539917136602497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738569422053222848803329 4303927066539917136602497)
                      ·
                        rfl

theorem cell23_8381868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 3, 2].length) (baseStart_8381868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381868 prefixEnd_8381868 := by exact prefixLift 8381868
  have htrace : WordTrace (prefixWord ++ tailWord_8381868) baseStart_8381868 baseEnd_8381868 := by
    simpa [prefixWord, tailWord_8381868, baseEnd_8381868] using wordTrace_append hprefix tailTrace_8381868
  have hstable : (prefixWord ++ tailWord_8381868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381868).length < 2 ^ (prefixWord ++ tailWord_8381868).sum := by decide
  have hdescent : baseEnd_8381868 < baseStart_8381868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381898 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_8381898 : Nat := 118140960795 + 8381898 * 2 ^ 59
def prefixEnd_8381898 : Nat := 4983230072969 + 3 ^ 40 * 8381898 * 2
def baseEnd_8381898 : Nat := 4303942470959552019227359

theorem tailTrace_8381898 : CollatzResearch.WordTrace tailWord_8381898 prefixEnd_8381898 4303942470959552019227359 := by
  unfold tailWord_8381898
  simp only [CollatzResearch.WordTrace]
  refine ⟨76428233846955633763710587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203808623591881690036561565 76428233846955633763710587)
  ·
    refine ⟨114642350770433450645565881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76428233846955633763710587 114642350770433450645565881)
    ·
      refine ⟨85981763077825087984174411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114642350770433450645565881 85981763077825087984174411)
      ·
        refine ⟨128972644616737631976261617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85981763077825087984174411 128972644616737631976261617)
        ·
          refine ⟨96729483462553223982196213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128972644616737631976261617 96729483462553223982196213)
          ·
            refine ⟨9068389074614364748330895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96729483462553223982196213 9068389074614364748330895)
            ·
              refine ⟨13602583611921547122496343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068389074614364748330895 13602583611921547122496343)
              ·
                refine ⟨20403875417882320683744515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602583611921547122496343 20403875417882320683744515)
                ·
                  refine ⟨30605813126823481025616773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20403875417882320683744515 30605813126823481025616773)
                  ·
                    refine ⟨5738589961279402692303145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30605813126823481025616773 5738589961279402692303145)
                    ·
                      refine ⟨4303942470959552019227359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738589961279402692303145 4303942470959552019227359)
                      ·
                        rfl

theorem cell23_8381898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_8381898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381898 prefixEnd_8381898 := by exact prefixLift 8381898
  have htrace : WordTrace (prefixWord ++ tailWord_8381898) baseStart_8381898 baseEnd_8381898 := by
    simpa [prefixWord, tailWord_8381898, baseEnd_8381898] using wordTrace_append hprefix tailTrace_8381898
  have hstable : (prefixWord ++ tailWord_8381898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381898).length < 2 ^ (prefixWord ++ tailWord_8381898).sum := by decide
  have hdescent : baseEnd_8381898 < baseStart_8381898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381921 : List Nat := [1, 2, 3, 1, 2, 3, 3, 3, 5]
def baseStart_8381921 : Nat := 118140960795 + 8381921 * 2 ^ 59
def prefixEnd_8381921 : Nat := 4983230072969 + 3 ^ 40 * 8381921 * 2
def baseEnd_8381921 : Nat := 478217142334956158804417

theorem tailTrace_8381921 : CollatzResearch.WordTrace tailWord_8381921 prefixEnd_8381921 478217142334956158804417 := by
  unfold tailWord_8381921
  simp only [CollatzResearch.WordTrace]
  refine ⟨305713774266739209982929617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203809182844492806655286411 305713774266739209982929617)
  ·
    refine ⟨229285330700054407487197213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305713774266739209982929617 229285330700054407487197213)
    ·
      refine ⟨85981999012520402807698955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229285330700054407487197213 85981999012520402807698955)
      ·
        refine ⟨128972998518780604211548433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85981999012520402807698955 128972998518780604211548433)
        ·
          refine ⟨96729748889085453158661325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128972998518780604211548433 96729748889085453158661325)
          ·
            refine ⟨36273655833407044934497997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96729748889085453158661325 36273655833407044934497997)
            ·
              refine ⟨13602620937527641850436749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36273655833407044934497997 13602620937527641850436749)
              ·
                refine ⟨5100982851572865693913781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13602620937527641850436749 5100982851572865693913781)
                ·
                  refine ⟨478217142334956158804417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5100982851572865693913781 478217142334956158804417)
                  ·
                    rfl

theorem cell23_8381921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 3, 5].length) (baseStart_8381921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381921 prefixEnd_8381921 := by exact prefixLift 8381921
  have htrace : WordTrace (prefixWord ++ tailWord_8381921) baseStart_8381921 baseEnd_8381921 := by
    simpa [prefixWord, tailWord_8381921, baseEnd_8381921] using wordTrace_append hprefix tailTrace_8381921
  have hstable : (prefixWord ++ tailWord_8381921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381921).length < 2 ^ (prefixWord ++ tailWord_8381921).sum := by decide
  have hdescent : baseEnd_8381921 < baseStart_8381921 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381944 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_8381944 : Nat := 118140960795 + 8381944 * 2 ^ 59
def prefixEnd_8381944 : Nat := 4983230072969 + 3 ^ 40 * 8381944 * 2
def baseEnd_8381944 : Nat := 4303966091069658839252147

theorem tailTrace_8381944 : CollatzResearch.WordTrace tailWord_8381944 prefixEnd_8381944 4303966091069658839252147 := by
  unfold tailWord_8381944
  simp only [CollatzResearch.WordTrace]
  refine ⟨152857306572827942455508443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203809742097103923274011257 152857306572827942455508443)
  ·
    refine ⟨229285959859241913683262665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152857306572827942455508443 229285959859241913683262665)
    ·
      refine ⟨171964469894431435262446999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229285959859241913683262665 171964469894431435262446999)
      ·
        refine ⟨257946704841647152893670499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171964469894431435262446999 257946704841647152893670499)
        ·
          refine ⟨386920057262470729340505749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257946704841647152893670499 386920057262470729340505749)
          ·
            refine ⟨18136877684178315437836207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 386920057262470729340505749 18136877684178315437836207)
            ·
              refine ⟨27205316526267473156754311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18136877684178315437836207 27205316526267473156754311)
              ·
                refine ⟨40807974789401209735131467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27205316526267473156754311 40807974789401209735131467)
                ·
                  refine ⟨61211962184101814602697201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40807974789401209735131467 61211962184101814602697201)
                  ·
                    refine ⟨45908971638076360952022901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61211962184101814602697201 45908971638076360952022901)
                    ·
                      refine ⟨4303966091069658839252147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45908971638076360952022901 4303966091069658839252147)
                      ·
                        rfl

theorem cell23_8381944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_8381944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381944 prefixEnd_8381944 := by exact prefixLift 8381944
  have htrace : WordTrace (prefixWord ++ tailWord_8381944) baseStart_8381944 baseEnd_8381944 := by
    simpa [prefixWord, tailWord_8381944, baseEnd_8381944] using wordTrace_append hprefix tailTrace_8381944
  have hstable : (prefixWord ++ tailWord_8381944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381944).length < 2 ^ (prefixWord ++ tailWord_8381944).sum := by decide
  have hdescent : baseEnd_8381944 < baseStart_8381944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8381971 : List Nat := [1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4]
def baseStart_8381971 : Nat := 118140960795 + 8381971 * 2 ^ 59
def prefixEnd_8381971 : Nat := 4983230072969 + 3 ^ 40 * 8381971 * 2
def baseEnd_8381971 : Nat := 4303979955047330233614523

theorem tailTrace_8381971 : CollatzResearch.WordTrace tailWord_8381971 prefixEnd_8381971 4303979955047330233614523 := by
  unfold tailWord_8381971
  simp only [CollatzResearch.WordTrace]
  refine ⟨305715597916558068522249767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203810398611038712348166511 305715597916558068522249767)
  ·
    refine ⟨458573396874837102783374651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305715597916558068522249767 458573396874837102783374651)
    ·
      refine ⟨687860095312255654175061977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458573396874837102783374651 687860095312255654175061977)
      ·
        refine ⟨515895071484191740631296483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687860095312255654175061977 515895071484191740631296483)
        ·
          refine ⟨773842607226287610946944725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515895071484191740631296483 773842607226287610946944725)
          ·
            refine ⟨18136936106866115881569017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 773842607226287610946944725 18136936106866115881569017)
            ·
              refine ⟨13602702080149586911176763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18136936106866115881569017 13602702080149586911176763)
              ·
                refine ⟨20404053120224380366765145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602702080149586911176763 20404053120224380366765145)
                ·
                  refine ⟨15303039840168285275073859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20404053120224380366765145 15303039840168285275073859)
                  ·
                    refine ⟨22954559760252427912610789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15303039840168285275073859 22954559760252427912610789)
                    ·
                      refine ⟨4303979955047330233614523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22954559760252427912610789 4303979955047330233614523)
                      ·
                        rfl

theorem cell23_8381971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_8381971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8381971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8381971 prefixEnd_8381971 := by exact prefixLift 8381971
  have htrace : WordTrace (prefixWord ++ tailWord_8381971) baseStart_8381971 baseEnd_8381971 := by
    simpa [prefixWord, tailWord_8381971, baseEnd_8381971] using wordTrace_append hprefix tailTrace_8381971
  have hstable : (prefixWord ++ tailWord_8381971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8381971).length < 2 ^ (prefixWord ++ tailWord_8381971).sum := by decide
  have hdescent : baseEnd_8381971 < baseStart_8381971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8381971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382022 : List Nat := [6, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_8382022 : Nat := 118140960795 + 8382022 * 2 ^ 59
def prefixEnd_8382022 : Nat := 4983230072969 + 3 ^ 40 * 8382022 * 2
def baseEnd_8382022 : Nat := 4304006142560709534076789

theorem tailTrace_8382022 : CollatzResearch.WordTrace tailWord_8382022 prefixEnd_8382022 4304006142560709534076789 := by
  unfold tailWord_8382022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9553670563730415757261135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203811638692915536154904213 9553670563730415757261135)
  ·
    refine ⟨14330505845595623635891703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9553670563730415757261135 14330505845595623635891703)
    ·
      refine ⟨21495758768393435453837555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14330505845595623635891703 21495758768393435453837555)
      ·
        refine ⟨32243638152590153180756333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21495758768393435453837555 32243638152590153180756333)
        ·
          refine ⟨12091364307221307442783625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32243638152590153180756333 12091364307221307442783625)
          ·
            refine ⟨9068523230415980582087719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091364307221307442783625 9068523230415980582087719)
            ·
              refine ⟨13602784845623970873131579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068523230415980582087719 13602784845623970873131579)
              ·
                refine ⟨20404177268435956309697369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602784845623970873131579 20404177268435956309697369)
                ·
                  refine ⟨15303132951326967232273027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20404177268435956309697369 15303132951326967232273027)
                  ·
                    refine ⟨22954699426990450848409541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15303132951326967232273027 22954699426990450848409541)
                    ·
                      refine ⟨4304006142560709534076789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22954699426990450848409541 4304006142560709534076789)
                      ·
                        rfl

theorem cell23_8382022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_8382022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382022 prefixEnd_8382022 := by exact prefixLift 8382022
  have htrace : WordTrace (prefixWord ++ tailWord_8382022) baseStart_8382022 baseEnd_8382022 := by
    simpa [prefixWord, tailWord_8382022, baseEnd_8382022] using wordTrace_append hprefix tailTrace_8382022
  have hstable : (prefixWord ++ tailWord_8382022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382022).length < 2 ^ (prefixWord ++ tailWord_8382022).sum := by decide
  have hdescent : baseEnd_8382022 < baseStart_8382022 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382055 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_8382055 : Nat := 118140960795 + 8382055 * 2 ^ 59
def prefixEnd_8382055 : Nat := 4983230072969 + 3 ^ 40 * 8382055 * 2
def baseEnd_8382055 : Nat := 4304023087422307904964137

theorem tailTrace_8382055 : CollatzResearch.WordTrace tailWord_8382055 prefixEnd_8382055 4304023087422307904964137 := by
  unfold tailWord_8382055
  simp only [CollatzResearch.WordTrace]
  refine ⟨305718661648253750868307619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203812441098835833912205079 305718661648253750868307619)
  ·
    refine ⟨458577992472380626302461429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305718661648253750868307619 458577992472380626302461429)
    ·
      refine ⟨42991686794285683715855759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458577992472380626302461429 42991686794285683715855759)
      ·
        refine ⟨64487530191428525573783639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42991686794285683715855759 64487530191428525573783639)
        ·
          refine ⟨96731295287142788360675459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64487530191428525573783639 96731295287142788360675459)
          ·
            refine ⟨145096942930714182541013189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96731295287142788360675459 145096942930714182541013189)
            ·
              refine ⟨27205676799508909226439973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145096942930714182541013189 27205676799508909226439973)
              ·
                refine ⟨5101064399907920479957495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27205676799508909226439973 5101064399907920479957495)
                ·
                  refine ⟨7651596599861880719936243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101064399907920479957495 7651596599861880719936243)
                  ·
                    refine ⟨11477394899792821079904365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7651596599861880719936243 11477394899792821079904365)
                    ·
                      refine ⟨4304023087422307904964137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11477394899792821079904365 4304023087422307904964137)
                      ·
                        rfl

theorem cell23_8382055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_8382055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382055 prefixEnd_8382055 := by exact prefixLift 8382055
  have htrace : WordTrace (prefixWord ++ tailWord_8382055) baseStart_8382055 baseEnd_8382055 := by
    simpa [prefixWord, tailWord_8382055, baseEnd_8382055] using wordTrace_append hprefix tailTrace_8382055
  have hstable : (prefixWord ++ tailWord_8382055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382055).length < 2 ^ (prefixWord ++ tailWord_8382055).sum := by decide
  have hdescent : baseEnd_8382055 < baseStart_8382055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382112 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2]
def baseStart_8382112 : Nat := 118140960795 + 8382112 * 2 ^ 59
def prefixEnd_8382112 : Nat := 4983230072969 + 3 ^ 40 * 8382112 * 2
def baseEnd_8382112 : Nat := 4304052355819614181951375

theorem tailTrace_8382112 : CollatzResearch.WordTrace tailWord_8382112 prefixEnd_8382112 4304052355819614181951375 := by
  unfold tailWord_8382112
  simp only [CollatzResearch.WordTrace]
  refine ⟨152860370304523624801566295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203813827072698166402088393 152860370304523624801566295)
  ·
    refine ⟨229290555456785437202349443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152860370304523624801566295 229290555456785437202349443)
    ·
      refine ⟨343935833185178155803524165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229290555456785437202349443 343935833185178155803524165)
      ·
        refine ⟨64487968722220904213160781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343935833185178155803524165 64487968722220904213160781)
        ·
          refine ⟨24182988270832839079935293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64487968722220904213160781 24182988270832839079935293)
          ·
            refine ⟨9068620601562314654975735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24182988270832839079935293 9068620601562314654975735)
            ·
              refine ⟨13602930902343471982463603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068620601562314654975735 13602930902343471982463603)
              ·
                refine ⟨20404396353515207973695405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602930902343471982463603 20404396353515207973695405)
                ·
                  refine ⟨7651648632568202990135777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20404396353515207973695405 7651648632568202990135777)
                  ·
                    refine ⟨5738736474426152242601833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7651648632568202990135777 5738736474426152242601833)
                    ·
                      refine ⟨4304052355819614181951375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738736474426152242601833 4304052355819614181951375)
                      ·
                        rfl

theorem cell23_8382112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_8382112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382112 prefixEnd_8382112 := by exact prefixLift 8382112
  have htrace : WordTrace (prefixWord ++ tailWord_8382112) baseStart_8382112 baseEnd_8382112 := by
    simpa [prefixWord, tailWord_8382112, baseEnd_8382112] using wordTrace_append hprefix tailTrace_8382112
  have hstable : (prefixWord ++ tailWord_8382112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382112).length < 2 ^ (prefixWord ++ tailWord_8382112).sum := by decide
  have hdescent : baseEnd_8382112 < baseStart_8382112 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382146 : List Nat := [3, 5, 1, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_8382146 : Nat := 118140960795 + 8382146 * 2 ^ 59
def prefixEnd_8382146 : Nat := 4983230072969 + 3 ^ 40 * 8382146 * 2
def baseEnd_8382146 : Nat := 4304069814161867048926219

theorem tailTrace_8382146 : CollatzResearch.WordTrace tailWord_8382146 prefixEnd_8382146 4304069814161867048926219 := by
  unfold tailWord_8382146
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430495172731018352467573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203814653793949382273246861 76430495172731018352467573)
  ·
    refine ⟨7165358922443532970543835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76430495172731018352467573 7165358922443532970543835)
    ·
      refine ⟨10748038383665299455815753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165358922443532970543835 10748038383665299455815753)
      ·
        refine ⟨8061028787748974591861815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10748038383665299455815753 8061028787748974591861815)
        ·
          refine ⟨12091543181623461887792723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061028787748974591861815 12091543181623461887792723)
          ·
            refine ⟨18137314772435192831689085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12091543181623461887792723 18137314772435192831689085)
            ·
              refine ⟨6801493039663197311883407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18137314772435192831689085 6801493039663197311883407)
              ·
                refine ⟨10202239559494795967825111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801493039663197311883407 10202239559494795967825111)
                ·
                  refine ⟨15303359339242193951737667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202239559494795967825111 15303359339242193951737667)
                  ·
                    refine ⟨22955039008863290927606501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15303359339242193951737667 22955039008863290927606501)
                    ·
                      refine ⟨4304069814161867048926219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22955039008863290927606501 4304069814161867048926219)
                      ·
                        rfl

theorem cell23_8382146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_8382146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382146 prefixEnd_8382146 := by exact prefixLift 8382146
  have htrace : WordTrace (prefixWord ++ tailWord_8382146) baseStart_8382146 baseEnd_8382146 := by
    simpa [prefixWord, tailWord_8382146, baseEnd_8382146] using wordTrace_append hprefix tailTrace_8382146
  have hstable : (prefixWord ++ tailWord_8382146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382146).length < 2 ^ (prefixWord ++ tailWord_8382146).sum := by decide
  have hdescent : baseEnd_8382146 < baseStart_8382146 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382162 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_8382162 : Nat := 118140960795 + 8382162 * 2 ^ 59
def prefixEnd_8382162 : Nat := 4983230072969 + 3 ^ 40 * 8382162 * 2
def baseEnd_8382162 : Nat := 4304078029852338986326145

theorem tailTrace_8382162 : CollatzResearch.WordTrace tailWord_8382162 prefixEnd_8382162 4304078029852338986326145 := by
  unfold tailWord_8382162
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430641064716527035613185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203815042839244072094968493 76430641064716527035613185)
  ·
    refine ⟨57322980798537395276709889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76430641064716527035613185 57322980798537395276709889)
    ·
      refine ⟨42992235598903046457532417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57322980798537395276709889 42992235598903046457532417)
      ·
        refine ⟨32244176699177284843149313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42992235598903046457532417 32244176699177284843149313)
        ·
          refine ⟨24183132524382963632361985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32244176699177284843149313 24183132524382963632361985)
          ·
            refine ⟨18137349393287222724271489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24183132524382963632361985 18137349393287222724271489)
            ·
              refine ⟨13603012044965417043203617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18137349393287222724271489 13603012044965417043203617)
              ·
                refine ⟨10202259033724062782402713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13603012044965417043203617 10202259033724062782402713)
                ·
                  refine ⟨7651694275293047086802035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10202259033724062782402713 7651694275293047086802035)
                  ·
                    refine ⟨11477541412939570630203053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7651694275293047086802035 11477541412939570630203053)
                    ·
                      refine ⟨4304078029852338986326145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11477541412939570630203053 4304078029852338986326145)
                      ·
                        rfl

theorem cell23_8382162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_8382162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382162 prefixEnd_8382162 := by exact prefixLift 8382162
  have htrace : WordTrace (prefixWord ++ tailWord_8382162) baseStart_8382162 baseEnd_8382162 := by
    simpa [prefixWord, tailWord_8382162, baseEnd_8382162] using wordTrace_append hprefix tailTrace_8382162
  have hstable : (prefixWord ++ tailWord_8382162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382162).length < 2 ^ (prefixWord ++ tailWord_8382162).sum := by decide
  have hdescent : baseEnd_8382162 < baseStart_8382162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382168 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_8382168 : Nat := 118140960795 + 8382168 * 2 ^ 59
def prefixEnd_8382168 : Nat := 4983230072969 + 3 ^ 40 * 8382168 * 2
def baseEnd_8382168 : Nat := 4304081110736265962851117

theorem tailTrace_8382168 : CollatzResearch.WordTrace tailWord_8382168 prefixEnd_8382168 4304081110736265962851117 := by
  unfold tailWord_8382168
  simp only [CollatzResearch.WordTrace]
  refine ⟨152861391548422185583585579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203815188731229580778114105 152861391548422185583585579)
  ·
    refine ⟨229292087322633278375378369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152861391548422185583585579 229292087322633278375378369)
    ·
      refine ⟨171969065491974958781533777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229292087322633278375378369 171969065491974958781533777)
      ·
        refine ⟨128976799118981219086150333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171969065491974958781533777 128976799118981219086150333)
        ·
          refine ⟨48366299669617957157306375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128976799118981219086150333 48366299669617957157306375)
          ·
            refine ⟨72549449504426935735959563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48366299669617957157306375 72549449504426935735959563)
            ·
              refine ⟨108824174256640403603939345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72549449504426935735959563 108824174256640403603939345)
              ·
                refine ⟨81618130692480302702954509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108824174256640403603939345 81618130692480302702954509)
                ·
                  refine ⟨30606799009680113513607941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81618130692480302702954509 30606799009680113513607941)
                  ·
                    refine ⟨5738774814315021283801489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30606799009680113513607941 5738774814315021283801489)
                    ·
                      refine ⟨4304081110736265962851117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738774814315021283801489 4304081110736265962851117)
                      ·
                        rfl

theorem cell23_8382168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_8382168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382168 prefixEnd_8382168 := by exact prefixLift 8382168
  have htrace : WordTrace (prefixWord ++ tailWord_8382168) baseStart_8382168 baseEnd_8382168 := by
    simpa [prefixWord, tailWord_8382168, baseEnd_8382168] using wordTrace_append hprefix tailTrace_8382168
  have hstable : (prefixWord ++ tailWord_8382168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382168).length < 2 ^ (prefixWord ++ tailWord_8382168).sum := by decide
  have hdescent : baseEnd_8382168 < baseStart_8382168 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382191 : List Nat := [1, 1, 2, 1, 5, 1, 3, 2, 7]
def baseStart_8382191 : Nat := 118140960795 + 8382191 * 2 ^ 59
def prefixEnd_8382191 : Nat := 4983230072969 + 3 ^ 40 * 8382191 * 2
def baseEnd_8382191 : Nat := 478232546754591041429279

theorem tailTrace_8382191 : CollatzResearch.WordTrace tailWord_8382191 prefixEnd_8382191 478232546754591041429279 := by
  unfold tailWord_8382191
  simp only [CollatzResearch.WordTrace]
  refine ⟨305723621975761046095258427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203815747983840697396838951 305723621975761046095258427)
  ·
    refine ⟨458585432963641569142887641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305723621975761046095258427 458585432963641569142887641)
    ·
      refine ⟨343939074722731176857165731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458585432963641569142887641 343939074722731176857165731)
      ·
        refine ⟨515908612084096765285748597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343939074722731176857165731 515908612084096765285748597)
        ·
          refine ⟨48366432382884071745538931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 515908612084096765285748597 48366432382884071745538931)
          ·
            refine ⟨72549648574326107618308397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48366432382884071745538931 72549648574326107618308397)
            ·
              refine ⟨27206118215372290356865649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72549648574326107618308397 27206118215372290356865649)
              ·
                refine ⟨20404588661529217767649237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27206118215372290356865649 20404588661529217767649237)
                ·
                  refine ⟨478232546754591041429279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20404588661529217767649237 478232546754591041429279)
                  ·
                    rfl

theorem cell23_8382191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 7].length) (baseStart_8382191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382191 prefixEnd_8382191 := by exact prefixLift 8382191
  have htrace : WordTrace (prefixWord ++ tailWord_8382191) baseStart_8382191 baseEnd_8382191 := by
    simpa [prefixWord, tailWord_8382191, baseEnd_8382191] using wordTrace_append hprefix tailTrace_8382191
  have hstable : (prefixWord ++ tailWord_8382191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382191).length < 2 ^ (prefixWord ++ tailWord_8382191).sum := by decide
  have hdescent : baseEnd_8382191 < baseStart_8382191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382206 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_8382206 : Nat := 118140960795 + 8382206 * 2 ^ 59
def prefixEnd_8382206 : Nat := 4983230072969 + 3 ^ 40 * 8382206 * 2
def baseEnd_8382206 : Nat := 4304100623001136814175943

theorem tailTrace_8382206 : CollatzResearch.WordTrace tailWord_8382206 prefixEnd_8382206 4304100623001136814175943 := by
  unfold tailWord_8382206
  simp only [CollatzResearch.WordTrace]
  refine ⟨38215521133838337957131809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203816112713804469104702981 38215521133838337957131809)
  ·
    refine ⟨28661640850378753467848857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38215521133838337957131809 28661640850378753467848857)
    ·
      refine ⟨21496230637784065100886643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28661640850378753467848857 21496230637784065100886643)
      ·
        refine ⟨32244345956676097651329965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21496230637784065100886643 32244345956676097651329965)
        ·
          refine ⟨12091629733753536619248737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32244345956676097651329965 12091629733753536619248737)
          ·
            refine ⟨9068722300315152464436553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091629733753536619248737 9068722300315152464436553)
            ·
              refine ⟨6801541725236364348327415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9068722300315152464436553 6801541725236364348327415)
              ·
                refine ⟨10202312587854546522491123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801541725236364348327415 10202312587854546522491123)
                ·
                  refine ⟨15303468881781819783736685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202312587854546522491123 15303468881781819783736685)
                  ·
                    refine ⟨5738800830668182418901257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15303468881781819783736685 5738800830668182418901257)
                    ·
                      refine ⟨4304100623001136814175943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738800830668182418901257 4304100623001136814175943)
                      ·
                        rfl

theorem cell23_8382206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_8382206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382206 prefixEnd_8382206 := by exact prefixLift 8382206
  have htrace : WordTrace (prefixWord ++ tailWord_8382206) baseStart_8382206 baseEnd_8382206 := by
    simpa [prefixWord, tailWord_8382206, baseEnd_8382206] using wordTrace_append hprefix tailTrace_8382206
  have hstable : (prefixWord ++ tailWord_8382206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382206).length < 2 ^ (prefixWord ++ tailWord_8382206).sum := by decide
  have hdescent : baseEnd_8382206 < baseStart_8382206 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382218 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_8382218 : Nat := 118140960795 + 8382218 * 2 ^ 59
def prefixEnd_8382218 : Nat := 4983230072969 + 3 ^ 40 * 8382218 * 2
def baseEnd_8382218 : Nat := 4304106784768990767225887

theorem tailTrace_8382218 : CollatzResearch.WordTrace tailWord_8382218 prefixEnd_8382218 4304106784768990767225887 := by
  unfold tailWord_8382218
  simp only [CollatzResearch.WordTrace]
  refine ⟨76431151686665807426622827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203816404497775486470994205 76431151686665807426622827)
  ·
    refine ⟨114646727529998711139934241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76431151686665807426622827 114646727529998711139934241)
    ·
      refine ⟨85985045647499033354950681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114646727529998711139934241 85985045647499033354950681)
      ·
        refine ⟨64488784235624275016213011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85985045647499033354950681 64488784235624275016213011)
        ·
          refine ⟨96733176353436412524319517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64488784235624275016213011 96733176353436412524319517)
          ·
            refine ⟨36274941132538654696619819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96733176353436412524319517 36274941132538654696619819)
            ·
              refine ⟨54412411698807982044929729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36274941132538654696619819 54412411698807982044929729)
              ·
                refine ⟨40809308774105986533697297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54412411698807982044929729 40809308774105986533697297)
                ·
                  refine ⟨30606981580579489900272973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40809308774105986533697297 30606981580579489900272973)
                  ·
                    refine ⟨11477618092717308712602365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30606981580579489900272973 11477618092717308712602365)
                    ·
                      refine ⟨4304106784768990767225887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11477618092717308712602365 4304106784768990767225887)
                      ·
                        rfl

theorem cell23_8382218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_8382218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382218 prefixEnd_8382218 := by exact prefixLift 8382218
  have htrace : WordTrace (prefixWord ++ tailWord_8382218) baseStart_8382218 baseEnd_8382218 := by
    simpa [prefixWord, tailWord_8382218, baseEnd_8382218] using wordTrace_append hprefix tailTrace_8382218
  have hstable : (prefixWord ++ tailWord_8382218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382218).length < 2 ^ (prefixWord ++ tailWord_8382218).sum := by decide
  have hdescent : baseEnd_8382218 < baseStart_8382218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382258 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_8382258 : Nat := 118140960795 + 8382258 * 2 ^ 59
def prefixEnd_8382258 : Nat := 4983230072969 + 3 ^ 40 * 8382258 * 2
def baseEnd_8382258 : Nat := 4304127323995170610725703

theorem tailTrace_8382258 : CollatzResearch.WordTrace tailWord_8382258 prefixEnd_8382258 4304127323995170610725703 := by
  unfold tailWord_8382258
  simp only [CollatzResearch.WordTrace]
  refine ⟨76431516416629579134486857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203817377111012211025298285 76431516416629579134486857)
  ·
    refine ⟨57323637312472184350865143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76431516416629579134486857 57323637312472184350865143)
    ·
      refine ⟨85985455968708276526297715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57323637312472184350865143 85985455968708276526297715)
      ·
        refine ⟨128978183953062414789446573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85985455968708276526297715 128978183953062414789446573)
        ·
          refine ⟨48366818982398405546042465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128978183953062414789446573 48366818982398405546042465)
          ·
            refine ⟨36275114236798804159531849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48366818982398405546042465 36275114236798804159531849)
            ·
              refine ⟨27206335677599103119648887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36275114236798804159531849 27206335677599103119648887)
              ·
                refine ⟨40809503516398654679473331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27206335677599103119648887 40809503516398654679473331)
                ·
                  refine ⟨61214255274597982019209997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40809503516398654679473331 61214255274597982019209997)
                  ·
                    refine ⟨22955345727974243257203749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61214255274597982019209997 22955345727974243257203749)
                    ·
                      refine ⟨4304127323995170610725703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22955345727974243257203749 4304127323995170610725703)
                      ·
                        rfl

theorem cell23_8382258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_8382258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382258 prefixEnd_8382258 := by exact prefixLift 8382258
  have htrace : WordTrace (prefixWord ++ tailWord_8382258) baseStart_8382258 baseEnd_8382258 := by
    simpa [prefixWord, tailWord_8382258, baseEnd_8382258] using wordTrace_append hprefix tailTrace_8382258
  have hstable : (prefixWord ++ tailWord_8382258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382258).length < 2 ^ (prefixWord ++ tailWord_8382258).sum := by decide
  have hdescent : baseEnd_8382258 < baseStart_8382258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382268 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 5, 4]
def baseStart_8382268 : Nat := 118140960795 + 8382268 * 2 ^ 59
def prefixEnd_8382268 : Nat := 4983230072969 + 3 ^ 40 * 8382268 * 2
def baseEnd_8382268 : Nat := 1434710819600571857200219

theorem tailTrace_8382268 : CollatzResearch.WordTrace tailWord_8382268 prefixEnd_8382268 1434710819600571857200219 := by
  unfold tailWord_8382268
  simp only [CollatzResearch.WordTrace]
  refine ⟨152863215198241044122905729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203817620264321392163874305 152863215198241044122905729)
  ·
    refine ⟨114647411398680783092179297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152863215198241044122905729 114647411398680783092179297)
    ·
      refine ⟨85985558549010587319134473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114647411398680783092179297 85985558549010587319134473)
      ·
        refine ⟨64489168911757940489350855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85985558549010587319134473 64489168911757940489350855)
        ·
          refine ⟨96733753367636910734026283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64489168911757940489350855 96733753367636910734026283)
          ·
            refine ⟨145100630051455366101039425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96733753367636910734026283 145100630051455366101039425)
            ·
              refine ⟨108825472538591524575779569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145100630051455366101039425 108825472538591524575779569)
              ·
                refine ⟨81619104403943643431834677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108825472538591524575779569 81619104403943643431834677)
                ·
                  refine ⟨7651791037869716571734501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81619104403943643431834677 7651791037869716571734501)
                  ·
                    refine ⟨1434710819600571857200219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7651791037869716571734501 1434710819600571857200219)
                    ·
                      rfl

theorem cell23_8382268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_8382268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382268 prefixEnd_8382268 := by exact prefixLift 8382268
  have htrace : WordTrace (prefixWord ++ tailWord_8382268) baseStart_8382268 baseEnd_8382268 := by
    simpa [prefixWord, tailWord_8382268, baseEnd_8382268] using wordTrace_append hprefix tailTrace_8382268
  have hstable : (prefixWord ++ tailWord_8382268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382268).length < 2 ^ (prefixWord ++ tailWord_8382268).sum := by decide
  have hdescent : baseEnd_8382268 < baseStart_8382268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382281 : List Nat := [1, 2, 1, 1, 2, 4, 1, 3, 8]
def baseStart_8382281 : Nat := 118140960795 + 8382281 * 2 ^ 59
def prefixEnd_8382281 : Nat := 4983230072969 + 3 ^ 40 * 8382281 * 2
def baseEnd_8382281 : Nat := 478237681561136002304233

theorem tailTrace_8382281 : CollatzResearch.WordTrace tailWord_8382281 prefixEnd_8382281 478237681561136002304233 := by
  unfold tailWord_8382281
  simp only [CollatzResearch.WordTrace]
  refine ⟨305726904545434991466034697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203817936363623327644023131 305726904545434991466034697)
  ·
    refine ⟨229295178409076243599526023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305726904545434991466034697 229295178409076243599526023)
    ·
      refine ⟨343942767613614365399289035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229295178409076243599526023 343942767613614365399289035)
      ·
        refine ⟨515914151420421548098933553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343942767613614365399289035 515914151420421548098933553)
        ·
          refine ⟨386935613565316161074200165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515914151420421548098933553 386935613565316161074200165)
          ·
            refine ⟨72550427543496780201412531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386935613565316161074200165 72550427543496780201412531)
            ·
              refine ⟨108825641315245170302118797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72550427543496780201412531 108825641315245170302118797)
              ·
                refine ⟨40809615493216938863294549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108825641315245170302118797 40809615493216938863294549)
                ·
                  refine ⟨478237681561136002304233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40809615493216938863294549 478237681561136002304233)
                  ·
                    rfl

theorem cell23_8382281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_8382281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382281 prefixEnd_8382281 := by exact prefixLift 8382281
  have htrace : WordTrace (prefixWord ++ tailWord_8382281) baseStart_8382281 baseEnd_8382281 := by
    simpa [prefixWord, tailWord_8382281, baseEnd_8382281] using wordTrace_append hprefix tailTrace_8382281
  have hstable : (prefixWord ++ tailWord_8382281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382281).length < 2 ^ (prefixWord ++ tailWord_8382281).sum := by decide
  have hdescent : baseEnd_8382281 < baseStart_8382281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382298 : List Nat := [3, 1, 1, 2, 1, 3, 3, 3, 6]
def baseStart_8382298 : Nat := 118140960795 + 8382298 * 2 ^ 59
def prefixEnd_8382298 : Nat := 4983230072969 + 3 ^ 40 * 8382298 * 2
def baseEnd_8382298 : Nat := 478238651469038939358391

theorem tailTrace_8382298 : CollatzResearch.WordTrace tailWord_8382298 prefixEnd_8382298 478238651469038939358391 := by
  unfold tailWord_8382298
  simp only [CollatzResearch.WordTrace]
  refine ⟨76431881146593350842350887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203818349724248935579602365 76431881146593350842350887)
  ·
    refine ⟨114647821719890026263526331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76431881146593350842350887 114647821719890026263526331)
    ·
      refine ⟨171971732579835039395289497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114647821719890026263526331 171971732579835039395289497)
      ·
        refine ⟨128978799434876279546467123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171971732579835039395289497 128978799434876279546467123)
        ·
          refine ⟨193468199152314419319700685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128978799434876279546467123 193468199152314419319700685)
          ·
            refine ⟨72550574682117907244887757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193468199152314419319700685 72550574682117907244887757)
            ·
              refine ⟨27206465505794215216832909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72550574682117907244887757 27206465505794215216832909)
              ·
                refine ⟨10202424564672830706312341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27206465505794215216832909 10202424564672830706312341)
                ·
                  refine ⟨478238651469038939358391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10202424564672830706312341 478238651469038939358391)
                  ·
                    rfl

theorem cell23_8382298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_8382298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382298 prefixEnd_8382298 := by exact prefixLift 8382298
  have htrace : WordTrace (prefixWord ++ tailWord_8382298) baseStart_8382298 baseEnd_8382298 := by
    simpa [prefixWord, tailWord_8382298, baseEnd_8382298] using wordTrace_append hprefix tailTrace_8382298
  have hstable : (prefixWord ++ tailWord_8382298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382298).length < 2 ^ (prefixWord ++ tailWord_8382298).sum := by decide
  have hdescent : baseEnd_8382298 < baseStart_8382298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382365 : List Nat := [1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_8382365 : Nat := 118140960795 + 8382365 * 2 ^ 59
def prefixEnd_8382365 : Nat := 4983230072969 + 3 ^ 40 * 8382365 * 2
def baseEnd_8382365 : Nat := 4304182266425201692087711

theorem tailTrace_8382365 : CollatzResearch.WordTrace tailWord_8382365 prefixEnd_8382365 4304182266425201692087711 := by
  unfold tailWord_8382365
  simp only [CollatzResearch.WordTrace]
  refine ⟨305729968277130673812092549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203819978851420449208061699 305729968277130673812092549)
  ·
    refine ⟨57324369051962001339767353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305729968277130673812092549 57324369051962001339767353)
    ·
      refine ⟨42993276788971501004825515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57324369051962001339767353 42993276788971501004825515)
      ·
        refine ⟨64489915183457251507238273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42993276788971501004825515 64489915183457251507238273)
        ·
          refine ⟨48367436387592938630428705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64489915183457251507238273 48367436387592938630428705)
          ·
            refine ⟨36275577290694703972821529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48367436387592938630428705 36275577290694703972821529)
            ·
              refine ⟨27206682968021027979616147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36275577290694703972821529 27206682968021027979616147)
              ·
                refine ⟨40810024452031541969424221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27206682968021027979616147 40810024452031541969424221)
                ·
                  refine ⟨15303759169511828238534083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40810024452031541969424221 15303759169511828238534083)
                  ·
                    refine ⟨22955638754267742357801125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15303759169511828238534083 22955638754267742357801125)
                    ·
                      refine ⟨4304182266425201692087711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22955638754267742357801125 4304182266425201692087711)
                      ·
                        rfl

theorem cell23_8382365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_8382365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382365 prefixEnd_8382365 := by exact prefixLift 8382365
  have htrace : WordTrace (prefixWord ++ tailWord_8382365) baseStart_8382365 baseEnd_8382365 := by
    simpa [prefixWord, tailWord_8382365, baseEnd_8382365] using wordTrace_append hprefix tailTrace_8382365
  have hstable : (prefixWord ++ tailWord_8382365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382365).length < 2 ^ (prefixWord ++ tailWord_8382365).sum := by decide
  have hdescent : baseEnd_8382365 < baseStart_8382365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382375 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 1, 6]
def baseStart_8382375 : Nat := 118140960795 + 8382375 * 2 ^ 59
def prefixEnd_8382375 : Nat := 4983230072969 + 3 ^ 40 * 8382375 * 2
def baseEnd_8382375 : Nat := 1434729133743915550987555

theorem tailTrace_8382375 : CollatzResearch.WordTrace tailWord_8382375 prefixEnd_8382375 1434729133743915550987555 := by
  unfold tailWord_8382375
  simp only [CollatzResearch.WordTrace]
  refine ⟨305730333007094445519956579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203820222004729630346637719 305730333007094445519956579)
  ·
    refine ⟨458595499510641668279934869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305730333007094445519956579 458595499510641668279934869)
    ·
      refine ⟨21496664039561328200621947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 458595499510641668279934869 21496664039561328200621947)
      ·
        refine ⟨32244996059341992300932921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21496664039561328200621947 32244996059341992300932921)
        ·
          refine ⟨24183747044506494225699691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32244996059341992300932921 24183747044506494225699691)
          ·
            refine ⟨36275620566759741338549537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24183747044506494225699691 36275620566759741338549537)
            ·
              refine ⟨27206715425069806003912153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36275620566759741338549537 27206715425069806003912153)
              ·
                refine ⟨20405036568802354502934115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27206715425069806003912153 20405036568802354502934115)
                ·
                  refine ⟨30607554853203531754401173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20405036568802354502934115 30607554853203531754401173)
                  ·
                    refine ⟨1434729133743915550987555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30607554853203531754401173 1434729133743915550987555)
                    ·
                      rfl

theorem cell23_8382375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_8382375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382375 prefixEnd_8382375 := by exact prefixLift 8382375
  have htrace : WordTrace (prefixWord ++ tailWord_8382375) baseStart_8382375 baseEnd_8382375 := by
    simpa [prefixWord, tailWord_8382375, baseEnd_8382375] using wordTrace_append hprefix tailTrace_8382375
  have hstable : (prefixWord ++ tailWord_8382375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382375).length < 2 ^ (prefixWord ++ tailWord_8382375).sum := by decide
  have hdescent : baseEnd_8382375 < baseStart_8382375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382399 : List Nat := [1, 1, 2, 2, 2, 1, 3, 6, 1, 2, 2]
def baseStart_8382399 : Nat := 118140960795 + 8382399 * 2 ^ 59
def prefixEnd_8382399 : Nat := 4983230072969 + 3 ^ 40 * 8382399 * 2
def baseEnd_8382399 : Nat := 4304199724767454559062555

theorem tailTrace_8382399 : CollatzResearch.WordTrace tailWord_8382399 prefixEnd_8382399 4304199724767454559062555 := by
  unfold tailWord_8382399
  simp only [CollatzResearch.WordTrace]
  refine ⟨305731208359007497618830251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203820805572671665079220167 305731208359007497618830251)
  ·
    refine ⟨458596812538511246428245377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305731208359007497618830251 458596812538511246428245377)
    ·
      refine ⟨343947609403883434821184033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458596812538511246428245377 343947609403883434821184033)
      ·
        refine ⟨257960707052912576115888025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343947609403883434821184033 257960707052912576115888025)
        ·
          refine ⟨193470530289684432086916019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257960707052912576115888025 193470530289684432086916019)
          ·
            refine ⟨290205795434526648130374029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193470530289684432086916019 290205795434526648130374029)
            ·
              refine ⟨108827173287947493048890261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290205795434526648130374029 108827173287947493048890261)
              ·
                refine ⟨5101273747872538736666731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108827173287947493048890261 5101273747872538736666731)
                ·
                  refine ⟨7651910621808808105000097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101273747872538736666731 7651910621808808105000097)
                  ·
                    refine ⟨5738932966356606078750073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7651910621808808105000097 5738932966356606078750073)
                    ·
                      refine ⟨4304199724767454559062555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738932966356606078750073 4304199724767454559062555)
                      ·
                        rfl

theorem cell23_8382399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_8382399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382399 prefixEnd_8382399 := by exact prefixLift 8382399
  have htrace : WordTrace (prefixWord ++ tailWord_8382399) baseStart_8382399 baseEnd_8382399 := by
    simpa [prefixWord, tailWord_8382399, baseEnd_8382399] using wordTrace_append hprefix tailTrace_8382399
  have hstable : (prefixWord ++ tailWord_8382399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382399).length < 2 ^ (prefixWord ++ tailWord_8382399).sum := by decide
  have hdescent : baseEnd_8382399 < baseStart_8382399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382412 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 1, 2, 4]
def baseStart_8382412 : Nat := 118140960795 + 8382412 * 2 ^ 59
def prefixEnd_8382412 : Nat := 4983230072969 + 3 ^ 40 * 8382412 * 2
def baseEnd_8382412 : Nat := 4304206400015963008199995

theorem tailTrace_8382412 : CollatzResearch.WordTrace tailWord_8382412 prefixEnd_8382412 4304206400015963008199995 := by
  unfold tailWord_8382412
  simp only [CollatzResearch.WordTrace]
  refine ⟨152865841253980200419526745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203821121671973600559368993 152865841253980200419526745)
  ·
    refine ⟨114649380940485150314645059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152865841253980200419526745 114649380940485150314645059)
    ·
      refine ⟨171974071410727725471967589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114649380940485150314645059 171974071410727725471967589)
      ·
        refine ⟨32245138389511448525993923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 171974071410727725471967589 32245138389511448525993923)
        ·
          refine ⟨48367707584267172788990885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32245138389511448525993923 48367707584267172788990885)
          ·
            refine ⟨9068945172050094897935791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48367707584267172788990885 9068945172050094897935791)
            ·
              refine ⟨13603417758075142346903687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068945172050094897935791 13603417758075142346903687)
              ·
                refine ⟨20405126637112713520355531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13603417758075142346903687 20405126637112713520355531)
                ·
                  refine ⟨30607689955669070280533297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20405126637112713520355531 30607689955669070280533297)
                  ·
                    refine ⟨22955767466751802710399973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30607689955669070280533297 22955767466751802710399973)
                    ·
                      refine ⟨4304206400015963008199995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22955767466751802710399973 4304206400015963008199995)
                      ·
                        rfl

theorem cell23_8382412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_8382412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382412 prefixEnd_8382412 := by exact prefixLift 8382412
  have htrace : WordTrace (prefixWord ++ tailWord_8382412) baseStart_8382412 baseEnd_8382412 := by
    simpa [prefixWord, tailWord_8382412, baseEnd_8382412] using wordTrace_append hprefix tailTrace_8382412
  have hstable : (prefixWord ++ tailWord_8382412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382412).length < 2 ^ (prefixWord ++ tailWord_8382412).sum := by decide
  have hdescent : baseEnd_8382412 < baseStart_8382412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382422 : List Nat := [5, 2, 1, 1, 3, 1, 1, 9]
def baseStart_8382422 : Nat := 118140960795 + 8382422 * 2 ^ 59
def prefixEnd_8382422 : Nat := 4983230072969 + 3 ^ 40 * 8382422 * 2
def baseEnd_8382422 : Nat := 159415242030463258113887

theorem tailTrace_8382422 : CollatzResearch.WordTrace tailWord_8382422 prefixEnd_8382422 159415242030463258113887 := by
  unfold tailWord_8382422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108252952370260784182345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203821364825282781697945013 19108252952370260784182345)
  ·
    refine ⟨14331189714277695588136759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19108252952370260784182345 14331189714277695588136759)
    ·
      refine ⟨21496784571416543382205139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331189714277695588136759 21496784571416543382205139)
      ·
        refine ⟨32245176857124815073307709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21496784571416543382205139 32245176857124815073307709)
        ·
          refine ⟨12091941321421805652490391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32245176857124815073307709 12091941321421805652490391)
          ·
            refine ⟨18137911982132708478735587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12091941321421805652490391 18137911982132708478735587)
            ·
              refine ⟨27206867973199062718103381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18137911982132708478735587 27206867973199062718103381)
              ·
                refine ⟨159415242030463258113887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27206867973199062718103381 159415242030463258113887)
                ·
                  rfl

theorem cell23_8382422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_8382422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382422 prefixEnd_8382422 := by exact prefixLift 8382422
  have htrace : WordTrace (prefixWord ++ tailWord_8382422) baseStart_8382422 baseEnd_8382422 := by
    simpa [prefixWord, tailWord_8382422, baseEnd_8382422] using wordTrace_append hprefix tailTrace_8382422
  have hstable : (prefixWord ++ tailWord_8382422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382422).length < 2 ^ (prefixWord ++ tailWord_8382422).sum := by decide
  have hdescent : baseEnd_8382422 < baseStart_8382422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382448 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_8382448 : Nat := 118140960795 + 8382448 * 2 ^ 59
def prefixEnd_8382448 : Nat := 4983230072969 + 3 ^ 40 * 8382448 * 2
def baseEnd_8382448 : Nat := 1434741628439841622449943

theorem tailTrace_8382448 : CollatzResearch.WordTrace tailWord_8382448 prefixEnd_8382448 1434741628439841622449943 := by
  unfold tailWord_8382448
  simp only [CollatzResearch.WordTrace]
  refine ⟨152866497767914989493681999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203821997023886652658242665 152866497767914989493681999)
  ·
    refine ⟨229299746651872484240522999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152866497767914989493681999 229299746651872484240522999)
    ·
      refine ⟨343949619977808726360784499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229299746651872484240522999 343949619977808726360784499)
      ·
        refine ⟨515924429966713089541176749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343949619977808726360784499 515924429966713089541176749)
        ·
          refine ⟨193471661237517408577941281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515924429966713089541176749 193471661237517408577941281)
          ·
            refine ⟨145103745928138056433455961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193471661237517408577941281 145103745928138056433455961)
            ·
              refine ⟨108827809446103542325091971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145103745928138056433455961 108827809446103542325091971)
              ·
                refine ⟨163241714169155313487637957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108827809446103542325091971 163241714169155313487637957)
                ·
                  refine ⟨30607821406716621278932117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163241714169155313487637957 30607821406716621278932117)
                  ·
                    refine ⟨1434741628439841622449943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30607821406716621278932117 1434741628439841622449943)
                    ·
                      rfl

theorem cell23_8382448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_8382448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382448 prefixEnd_8382448 := by exact prefixLift 8382448
  have htrace : WordTrace (prefixWord ++ tailWord_8382448) baseStart_8382448 baseEnd_8382448 := by
    simpa [prefixWord, tailWord_8382448, baseEnd_8382448] using wordTrace_append hprefix tailTrace_8382448
  have hstable : (prefixWord ++ tailWord_8382448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382448).length < 2 ^ (prefixWord ++ tailWord_8382448).sum := by decide
  have hdescent : baseEnd_8382448 < baseStart_8382448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382472 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_8382472 : Nat := 118140960795 + 8382472 * 2 ^ 59
def prefixEnd_8382472 : Nat := 4983230072969 + 3 ^ 40 * 8382472 * 2
def baseEnd_8382472 : Nat := 4304237208855232773449719

theorem tailTrace_8382472 : CollatzResearch.WordTrace tailWord_8382472 prefixEnd_8382472 4304237208855232773449719 := by
  unfold tailWord_8382472
  simp only [CollatzResearch.WordTrace]
  refine ⟨152866935443871515543118835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203822580591828687390825113 152866935443871515543118835)
  ·
    refine ⟨229300403165807273314678253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152866935443871515543118835 229300403165807273314678253)
    ·
      refine ⟨85987651187177727493004345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229300403165807273314678253 85987651187177727493004345)
      ·
        refine ⟨64490738390383295619753259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85987651187177727493004345 64490738390383295619753259)
        ·
          refine ⟨96736107585574943429629889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64490738390383295619753259 96736107585574943429629889)
          ·
            refine ⟨72552080689181207572222417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96736107585574943429629889 72552080689181207572222417)
            ·
              refine ⟨54414060516885905679166813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72552080689181207572222417 54414060516885905679166813)
              ·
                refine ⟨20405272693832214629687555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54414060516885905679166813 20405272693832214629687555)
                ·
                  refine ⟨30607909040748321944531333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20405272693832214629687555 30607909040748321944531333)
                  ·
                    refine ⟨5738982945140310364599625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30607909040748321944531333 5738982945140310364599625)
                    ·
                      refine ⟨4304237208855232773449719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5738982945140310364599625 4304237208855232773449719)
                      ·
                        rfl

theorem cell23_8382472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_8382472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382472 prefixEnd_8382472 := by exact prefixLift 8382472
  have htrace : WordTrace (prefixWord ++ tailWord_8382472) baseStart_8382472 baseEnd_8382472 := by
    simpa [prefixWord, tailWord_8382472, baseEnd_8382472] using wordTrace_append hprefix tailTrace_8382472
  have hstable : (prefixWord ++ tailWord_8382472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382472).length < 2 ^ (prefixWord ++ tailWord_8382472).sum := by decide
  have hdescent : baseEnd_8382472 < baseStart_8382472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382506 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_8382506 : Nat := 118140960795 + 8382506 * 2 ^ 59
def prefixEnd_8382506 : Nat := 4983230072969 + 3 ^ 40 * 8382506 * 2
def baseEnd_8382506 : Nat := 4304254667197485640424563

theorem tailTrace_8382506 : CollatzResearch.WordTrace tailWord_8382506 prefixEnd_8382506 4304254667197485640424563 := by
  unfold tailWord_8382506
  simp only [CollatzResearch.WordTrace]
  refine ⟨76433777742404963723243843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203823407313079903261983581 76433777742404963723243843)
  ·
    refine ⟨114650666613607445584865765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76433777742404963723243843 114650666613607445584865765)
    ·
      refine ⟨21496999990051396047162331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114650666613607445584865765 21496999990051396047162331)
      ·
        refine ⟨32245499985077094070743497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21496999990051396047162331 32245499985077094070743497)
        ·
          refine ⟨24184124988807820553057623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32245499985077094070743497 24184124988807820553057623)
          ·
            refine ⟨36276187483211730829586435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24184124988807820553057623 36276187483211730829586435)
            ·
              refine ⟨54414281224817596244379653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36276187483211730829586435 54414281224817596244379653)
              ·
                refine ⟨10202677729653299295821185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54414281224817596244379653 10202677729653299295821185)
                ·
                  refine ⟨7652008297239974471865889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10202677729653299295821185 7652008297239974471865889)
                  ·
                    refine ⟨5739006222929980853899417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7652008297239974471865889 5739006222929980853899417)
                    ·
                      refine ⟨4304254667197485640424563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739006222929980853899417 4304254667197485640424563)
                      ·
                        rfl

theorem cell23_8382506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_8382506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382506 prefixEnd_8382506 := by exact prefixLift 8382506
  have htrace : WordTrace (prefixWord ++ tailWord_8382506) baseStart_8382506 baseEnd_8382506 := by
    simpa [prefixWord, tailWord_8382506, baseEnd_8382506] using wordTrace_append hprefix tailTrace_8382506
  have hstable : (prefixWord ++ tailWord_8382506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382506).length < 2 ^ (prefixWord ++ tailWord_8382506).sum := by decide
  have hdescent : baseEnd_8382506 < baseStart_8382506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382512 : List Nat := [2, 1, 1, 1, 2, 6, 1, 4, 5]
def baseStart_8382512 : Nat := 118140960795 + 8382512 * 2 ^ 59
def prefixEnd_8382512 : Nat := 4983230072969 + 3 ^ 40 * 8382512 * 2
def baseEnd_8382512 : Nat := 478250860897934735216615

theorem tailTrace_8382512 : CollatzResearch.WordTrace tailWord_8382512 prefixEnd_8382512 478250860897934735216615 := by
  unfold tailWord_8382512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152867664903799058958846895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203823553205065411945129193 152867664903799058958846895)
  ·
    refine ⟨229301497355698588438270343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152867664903799058958846895 229301497355698588438270343)
    ·
      refine ⟨343952246033547882657405515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229301497355698588438270343 343952246033547882657405515)
      ·
        refine ⟨515928369050321823986108273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343952246033547882657405515 515928369050321823986108273)
        ·
          refine ⟨386946276787741367989581205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515928369050321823986108273 386946276787741367989581205)
          ·
            refine ⟨18138106724425376624511619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 386946276787741367989581205 18138106724425376624511619)
            ·
              refine ⟨27207160086638064936767429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138106724425376624511619 27207160086638064936767429)
              ·
                refine ⟨5101342516244637175643893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27207160086638064936767429 5101342516244637175643893)
                ·
                  refine ⟨478250860897934735216615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101342516244637175643893 478250860897934735216615)
                  ·
                    rfl

theorem cell23_8382512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 4, 5].length) (baseStart_8382512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382512 prefixEnd_8382512 := by exact prefixLift 8382512
  have htrace : WordTrace (prefixWord ++ tailWord_8382512) baseStart_8382512 baseEnd_8382512 := by
    simpa [prefixWord, tailWord_8382512, baseEnd_8382512] using wordTrace_append hprefix tailTrace_8382512
  have hstable : (prefixWord ++ tailWord_8382512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382512).length < 2 ^ (prefixWord ++ tailWord_8382512).sum := by decide
  have hdescent : baseEnd_8382512 < baseStart_8382512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382525 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_8382525 : Nat := 118140960795 + 8382525 * 2 ^ 59
def prefixEnd_8382525 : Nat := 4983230072969 + 3 ^ 40 * 8382525 * 2
def baseEnd_8382525 : Nat := 1434754807776640355362325

theorem tailTrace_8382525 : CollatzResearch.WordTrace tailWord_8382525 prefixEnd_8382525 1434754807776640355362325 := by
  unfold tailWord_8382525
  simp only [CollatzResearch.WordTrace]
  refine ⟨305735803956551021137917029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203823869304367347425278019 305735803956551021137917029)
  ·
    refine ⟨57325463241853316463359443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305735803956551021137917029 57325463241853316463359443)
    ·
      refine ⟨85988194862779974695039165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57325463241853316463359443 85988194862779974695039165)
      ·
        refine ⟨32245573073542490510639687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85988194862779974695039165 32245573073542490510639687)
        ·
          refine ⟨48368359610313735765959531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32245573073542490510639687 48368359610313735765959531)
          ·
            refine ⟨72552539415470603648939297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48368359610313735765959531 72552539415470603648939297)
            ·
              refine ⟨54414404561602952736704473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72552539415470603648939297 54414404561602952736704473)
              ·
                refine ⟨40810803421202214552528355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54414404561602952736704473 40810803421202214552528355)
                ·
                  refine ⟨61216205131803321828792533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40810803421202214552528355 61216205131803321828792533)
                  ·
                    refine ⟨1434754807776640355362325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61216205131803321828792533 1434754807776640355362325)
                    ·
                      rfl

theorem cell23_8382525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_8382525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382525 prefixEnd_8382525 := by exact prefixLift 8382525
  have htrace : WordTrace (prefixWord ++ tailWord_8382525) baseStart_8382525 baseEnd_8382525 := by
    simpa [prefixWord, tailWord_8382525, baseEnd_8382525] using wordTrace_append hprefix tailTrace_8382525
  have hstable : (prefixWord ++ tailWord_8382525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382525).length < 2 ^ (prefixWord ++ tailWord_8382525).sum := by decide
  have hdescent : baseEnd_8382525 < baseStart_8382525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382542 : List Nat := [4, 1, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_8382542 : Nat := 118140960795 + 8382542 * 2 ^ 59
def prefixEnd_8382542 : Nat := 4983230072969 + 3 ^ 40 * 8382542 * 2
def baseEnd_8382542 : Nat := 1434757717500349166524799

theorem tailTrace_8382542 : CollatzResearch.WordTrace tailWord_8382542 prefixEnd_8382542 1434757717500349166524799 := by
  unfold tailWord_8382542
  simp only [CollatzResearch.WordTrace]
  refine ⟨38217052999686179130160735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203824282664992955360857253 38217052999686179130160735)
  ·
    refine ⟨57325579499529268695241103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38217052999686179130160735 57325579499529268695241103)
    ·
      refine ⟨85988369249293903042861655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57325579499529268695241103 85988369249293903042861655)
      ·
        refine ⟨128982553873940854564292483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85988369249293903042861655 128982553873940854564292483)
        ·
          refine ⟨193473830810911281846438725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128982553873940854564292483 193473830810911281846438725)
          ·
            refine ⟨36276343277045865346207261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193473830810911281846438725 36276343277045865346207261)
            ·
              refine ⟨13603628728892199504827723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36276343277045865346207261 13603628728892199504827723)
              ·
                refine ⟨20405443093338299257241585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13603628728892199504827723 20405443093338299257241585)
                ·
                  refine ⟨15304082320003724442931189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20405443093338299257241585 15304082320003724442931189)
                  ·
                    refine ⟨1434757717500349166524799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15304082320003724442931189 1434757717500349166524799)
                    ·
                      rfl

theorem cell23_8382542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_8382542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382542 prefixEnd_8382542 := by exact prefixLift 8382542
  have htrace : WordTrace (prefixWord ++ tailWord_8382542) baseStart_8382542 baseEnd_8382542 := by
    simpa [prefixWord, tailWord_8382542, baseEnd_8382542] using wordTrace_append hprefix tailTrace_8382542
  have hstable : (prefixWord ++ tailWord_8382542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382542).length < 2 ^ (prefixWord ++ tailWord_8382542).sum := by decide
  have hdescent : baseEnd_8382542 < baseStart_8382542 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382572 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 3, 4]
def baseStart_8382572 : Nat := 118140960795 + 8382572 * 2 ^ 59
def prefixEnd_8382572 : Nat := 4983230072969 + 3 ^ 40 * 8382572 * 2
def baseEnd_8382572 : Nat := 1434762852306894127399753

theorem tailTrace_8382572 : CollatzResearch.WordTrace tailWord_8382572 prefixEnd_8382572 1434762852306894127399753 := by
  unfold tailWord_8382572
  simp only [CollatzResearch.WordTrace]
  refine ⟨152868759093690374082438985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203825012124920498776585313 152868759093690374082438985)
  ·
    refine ⟨114651569320267780561829239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152868759093690374082438985 114651569320267780561829239)
    ·
      refine ⟨171977353980401670842743859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114651569320267780561829239 171977353980401670842743859)
      ·
        refine ⟨257966030970602506264115789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171977353980401670842743859 257966030970602506264115789)
        ·
          refine ⟨96737261613975939849043421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257966030970602506264115789 96737261613975939849043421)
          ·
            refine ⟨36276473105240977443391283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96737261613975939849043421 36276473105240977443391283)
            ·
              refine ⟨54414709657861466165086925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36276473105240977443391283 54414709657861466165086925)
              ·
                refine ⟨20405516121698049811907597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54414709657861466165086925 20405516121698049811907597)
                ·
                  refine ⟨7652068545636768679465349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20405516121698049811907597 7652068545636768679465349)
                  ·
                    refine ⟨1434762852306894127399753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7652068545636768679465349 1434762852306894127399753)
                    ·
                      rfl

theorem cell23_8382572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 4].length) (baseStart_8382572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382572 prefixEnd_8382572 := by exact prefixLift 8382572
  have htrace : WordTrace (prefixWord ++ tailWord_8382572) baseStart_8382572 baseEnd_8382572 := by
    simpa [prefixWord, tailWord_8382572, baseEnd_8382572] using wordTrace_append hprefix tailTrace_8382572
  have hstable : (prefixWord ++ tailWord_8382572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382572).length < 2 ^ (prefixWord ++ tailWord_8382572).sum := by decide
  have hdescent : baseEnd_8382572 < baseStart_8382572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382623 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 1, 4]
def baseStart_8382623 : Nat := 118140960795 + 8382623 * 2 ^ 59
def prefixEnd_8382623 : Nat := 4983230072969 + 3 ^ 40 * 8382623 * 2
def baseEnd_8382623 : Nat := 1434771581478020560887175

theorem tailTrace_8382623 : CollatzResearch.WordTrace tailWord_8382623 prefixEnd_8382623 1434771581478020560887175 := by
  unfold tailWord_8382623
  simp only [CollatzResearch.WordTrace]
  refine ⟨305739378310195983874984523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203826252206797322583323015 305739378310195983874984523)
  ·
    refine ⟨458609067465293975812476785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305739378310195983874984523 458609067465293975812476785)
    ·
      refine ⟨343956800598970481859357589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458609067465293975812476785 343956800598970481859357589)
      ·
        refine ⟨16122975028076741337157387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 343956800598970481859357589 16122975028076741337157387)
        ·
          refine ⟨24184462542115112005736081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16122975028076741337157387 24184462542115112005736081)
          ·
            refine ⟨18138346906586334004302061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184462542115112005736081 18138346906586334004302061)
            ·
              refine ⟨6801880089969875251613273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18138346906586334004302061 6801880089969875251613273)
              ·
                refine ⟨5101410067477406438709955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801880089969875251613273 5101410067477406438709955)
                ·
                  refine ⟨7652115101216109658064933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101410067477406438709955 7652115101216109658064933)
                  ·
                    refine ⟨1434771581478020560887175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7652115101216109658064933 1434771581478020560887175)
                    ·
                      rfl

theorem cell23_8382623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 1, 4].length) (baseStart_8382623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382623 prefixEnd_8382623 := by exact prefixLift 8382623
  have htrace : WordTrace (prefixWord ++ tailWord_8382623) baseStart_8382623 baseEnd_8382623 := by
    simpa [prefixWord, tailWord_8382623, baseEnd_8382623] using wordTrace_append hprefix tailTrace_8382623
  have hstable : (prefixWord ++ tailWord_8382623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382623).length < 2 ^ (prefixWord ++ tailWord_8382623).sum := by decide
  have hdescent : baseEnd_8382623 < baseStart_8382623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382656 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2]
def baseStart_8382656 : Nat := 118140960795 + 8382656 * 2 ^ 59
def prefixEnd_8382656 : Nat := 4983230072969 + 3 ^ 40 * 8382656 * 2
def baseEnd_8382656 : Nat := 4304331689295660053548873

theorem tailTrace_8382656 : CollatzResearch.WordTrace tailWord_8382656 prefixEnd_8382656 4304331689295660053548873 := by
  unfold tailWord_8382656
  simp only [CollatzResearch.WordTrace]
  refine ⟨152870290959538215255467911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203827054612717620340623881 152870290959538215255467911)
  ·
    refine ⟨229305436439307322883201867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152870290959538215255467911 229305436439307322883201867)
    ·
      refine ⟨343958154658960984324802801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229305436439307322883201867 343958154658960984324802801)
      ·
        refine ⟨257968615994220738243602101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343958154658960984324802801 257968615994220738243602101)
        ·
          refine ⟨24184557749458194210337697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257968615994220738243602101 24184557749458194210337697)
          ·
            refine ⟨18138418312093645657753273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184557749458194210337697 18138418312093645657753273)
            ·
              refine ⟨13603813734070234243314955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18138418312093645657753273 13603813734070234243314955)
              ·
                refine ⟨20405720601105351364972433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13603813734070234243314955 20405720601105351364972433)
                ·
                  refine ⟨15304290450829013523729325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20405720601105351364972433 15304290450829013523729325)
                  ·
                    refine ⟨5739108919060880071398497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15304290450829013523729325 5739108919060880071398497)
                    ·
                      refine ⟨4304331689295660053548873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739108919060880071398497 4304331689295660053548873)
                      ·
                        rfl

theorem cell23_8382656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_8382656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382656 prefixEnd_8382656 := by exact prefixLift 8382656
  have htrace : WordTrace (prefixWord ++ tailWord_8382656) baseStart_8382656 baseEnd_8382656 := by
    simpa [prefixWord, tailWord_8382656, baseEnd_8382656] using wordTrace_append hprefix tailTrace_8382656
  have hstable : (prefixWord ++ tailWord_8382656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382656).length < 2 ^ (prefixWord ++ tailWord_8382656).sum := by decide
  have hdescent : baseEnd_8382656 < baseStart_8382656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382665 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_8382665 : Nat := 118140960795 + 8382665 * 2 ^ 59
def prefixEnd_8382665 : Nat := 4983230072969 + 3 ^ 40 * 8382665 * 2
def baseEnd_8382665 : Nat := 4304336310621550518336331

theorem tailTrace_8382665 : CollatzResearch.WordTrace tailWord_8382665 prefixEnd_8382665 4304336310621550518336331 := by
  unfold tailWord_8382665
  simp only [CollatzResearch.WordTrace]
  refine ⟨305740910176043825048013449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203827273450695883365342299 305740910176043825048013449)
  ·
    refine ⟨229305682632032868786010087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305740910176043825048013449 229305682632032868786010087)
    ·
      refine ⟨343958523948049303179015131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229305682632032868786010087 343958523948049303179015131)
      ·
        refine ⟨515937785922073954768522697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343958523948049303179015131 515937785922073954768522697)
        ·
          refine ⟨386953339441555466076392023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515937785922073954768522697 386953339441555466076392023)
          ·
            refine ⟨580430009162333199114588035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386953339441555466076392023 580430009162333199114588035)
            ·
              refine ⟨870645013743499798671882053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580430009162333199114588035 870645013743499798671882053)
              ·
                refine ⟨163245940076906212250977885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 870645013743499798671882053 163245940076906212250977885)
                ·
                  refine ⟨61217227528839829594116707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163245940076906212250977885 61217227528839829594116707)
                  ·
                    refine ⟨91825841293259744391175061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61217227528839829594116707 91825841293259744391175061)
                    ·
                      refine ⟨4304336310621550518336331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91825841293259744391175061 4304336310621550518336331)
                      ·
                        rfl

theorem cell23_8382665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_8382665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382665 prefixEnd_8382665 := by exact prefixLift 8382665
  have htrace : WordTrace (prefixWord ++ tailWord_8382665) baseStart_8382665 baseEnd_8382665 := by
    simpa [prefixWord, tailWord_8382665, baseEnd_8382665] using wordTrace_append hprefix tailTrace_8382665
  have hstable : (prefixWord ++ tailWord_8382665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382665).length < 2 ^ (prefixWord ++ tailWord_8382665).sum := by decide
  have hdescent : baseEnd_8382665 < baseStart_8382665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382680 : List Nat := [2, 1, 2, 2, 4, 3, 2, 2, 1, 1, 3]
def baseStart_8382680 : Nat := 118140960795 + 8382680 * 2 ^ 59
def prefixEnd_8382680 : Nat := 4983230072969 + 3 ^ 40 * 8382680 * 2
def baseEnd_8382680 : Nat := 4304344012831367959648763

theorem tailTrace_8382680 : CollatzResearch.WordTrace tailWord_8382680 prefixEnd_8382680 4304344012831367959648763 := by
  unfold tailWord_8382680
  simp only [CollatzResearch.WordTrace]
  refine ⟨152870728635494741304904747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203827638180659655073206329 152870728635494741304904747)
  ·
    refine ⟨229306092953242111957357121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152870728635494741304904747 229306092953242111957357121)
    ·
      refine ⟨171979569714931583968017841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229306092953242111957357121 171979569714931583968017841)
      ·
        refine ⟨128984677286198687976013381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171979569714931583968017841 128984677286198687976013381)
        ·
          refine ⟨24184626991162253995502509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 128984677286198687976013381 24184626991162253995502509)
          ·
            refine ⟨9069235121685845248313441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24184626991162253995502509 9069235121685845248313441)
            ·
              refine ⟨6801926341264383936235081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069235121685845248313441 6801926341264383936235081)
              ·
                refine ⟨5101444755948287952176311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801926341264383936235081 5101444755948287952176311)
                ·
                  refine ⟨7652167133922431928264467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101444755948287952176311 7652167133922431928264467)
                  ·
                    refine ⟨11478250700883647892396701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652167133922431928264467 11478250700883647892396701)
                    ·
                      refine ⟨4304344012831367959648763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11478250700883647892396701 4304344012831367959648763)
                      ·
                        rfl

theorem cell23_8382680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_8382680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382680 prefixEnd_8382680 := by exact prefixLift 8382680
  have htrace : WordTrace (prefixWord ++ tailWord_8382680) baseStart_8382680 baseEnd_8382680 := by
    simpa [prefixWord, tailWord_8382680, baseEnd_8382680] using wordTrace_append hprefix tailTrace_8382680
  have hstable : (prefixWord ++ tailWord_8382680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382680).length < 2 ^ (prefixWord ++ tailWord_8382680).sum := by decide
  have hdescent : baseEnd_8382680 < baseStart_8382680 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382719 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 3]
def baseStart_8382719 : Nat := 118140960795 + 8382719 * 2 ^ 59
def prefixEnd_8382719 : Nat := 4983230072969 + 3 ^ 40 * 8382719 * 2
def baseEnd_8382719 : Nat := 4304364038576893307061083

theorem tailTrace_8382719 : CollatzResearch.WordTrace tailWord_8382719 prefixEnd_8382719 4304364038576893307061083 := by
  unfold tailWord_8382719
  simp only [CollatzResearch.WordTrace]
  refine ⟨305742879717848192270479211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203828586478565461513652807 305742879717848192270479211)
  ·
    refine ⟨458614319576772288405718817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305742879717848192270479211 458614319576772288405718817)
    ·
      refine ⟨343960739682579216304289113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458614319576772288405718817 343960739682579216304289113)
      ·
        refine ⟨257970554761934412228216835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343960739682579216304289113 257970554761934412228216835)
        ·
          refine ⟨386955832142901618342325253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257970554761934412228216835 386955832142901618342325253)
          ·
            refine ⟨72554218526794053439185985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 386955832142901618342325253 72554218526794053439185985)
            ·
              refine ⟨54415663895095540079389489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72554218526794053439185985 54415663895095540079389489)
              ·
                refine ⟨40811747921321655059542117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54415663895095540079389489 40811747921321655059542117)
                ·
                  refine ⟨7652202735247810323664147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40811747921321655059542117 7652202735247810323664147)
                  ·
                    refine ⟨11478304102871715485496221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652202735247810323664147 11478304102871715485496221)
                    ·
                      refine ⟨4304364038576893307061083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11478304102871715485496221 4304364038576893307061083)
                      ·
                        rfl

theorem cell23_8382719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_8382719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382719 prefixEnd_8382719 := by exact prefixLift 8382719
  have htrace : WordTrace (prefixWord ++ tailWord_8382719) baseStart_8382719 baseEnd_8382719 := by
    simpa [prefixWord, tailWord_8382719, baseEnd_8382719] using wordTrace_append hprefix tailTrace_8382719
  have hstable : (prefixWord ++ tailWord_8382719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382719).length < 2 ^ (prefixWord ++ tailWord_8382719).sum := by decide
  have hdescent : baseEnd_8382719 < baseStart_8382719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382776 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_8382776 : Nat := 118140960795 + 8382776 * 2 ^ 59
def prefixEnd_8382776 : Nat := 4983230072969 + 3 ^ 40 * 8382776 * 2
def baseEnd_8382776 : Nat := 4304393306974199584048321

theorem tailTrace_8382776 : CollatzResearch.WordTrace tailWord_8382776 prefixEnd_8382776 4304393306974199584048321 := by
  unfold tailWord_8382776
  simp only [CollatzResearch.WordTrace]
  refine ⟨152872479339320845502652091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203829972452427794003536121 152872479339320845502652091)
  ·
    refine ⟨229308719008981268253978137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152872479339320845502652091 229308719008981268253978137)
    ·
      refine ⟨171981539256735951190483603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229308719008981268253978137 171981539256735951190483603)
      ·
        refine ⟨257972308885103926785725405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171981539256735951190483603 257972308885103926785725405)
        ·
          refine ⟨96739615831913972544647027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257972308885103926785725405 96739615831913972544647027)
          ·
            refine ⟨145109423747870958816970541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96739615831913972544647027 145109423747870958816970541)
            ·
              refine ⟨54416033905451609556363953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145109423747870958816970541 54416033905451609556363953)
              ·
                refine ⟨40812025429088707167272965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54416033905451609556363953 40812025429088707167272965)
                ·
                  refine ⟨7652254767954132593863681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40812025429088707167272965 7652254767954132593863681)
                  ·
                    refine ⟨5739191075965599445397761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7652254767954132593863681 5739191075965599445397761)
                    ·
                      refine ⟨4304393306974199584048321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739191075965599445397761 4304393306974199584048321)
                      ·
                        rfl

theorem cell23_8382776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_8382776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382776 prefixEnd_8382776 := by exact prefixLift 8382776
  have htrace : WordTrace (prefixWord ++ tailWord_8382776) baseStart_8382776 baseEnd_8382776 := by
    simpa [prefixWord, tailWord_8382776, baseEnd_8382776] using wordTrace_append hprefix tailTrace_8382776
  have hstable : (prefixWord ++ tailWord_8382776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382776).length < 2 ^ (prefixWord ++ tailWord_8382776).sum := by decide
  have hdescent : baseEnd_8382776 < baseStart_8382776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382814 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_8382814 : Nat := 118140960795 + 8382814 * 2 ^ 59
def prefixEnd_8382814 : Nat := 4983230072969 + 3 ^ 40 * 8382814 * 2
def baseEnd_8382814 : Nat := 4304412819239070435373147

theorem tailTrace_8382814 : CollatzResearch.WordTrace tailWord_8382814 prefixEnd_8382814 4304412819239070435373147 := by
  unfold tailWord_8382814
  simp only [CollatzResearch.WordTrace]
  refine ⟨38218293081563002936898437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203830896435002682330124997 38218293081563002936898437)
  ·
    refine ⟨7165929952793063050668457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38218293081563002936898437 7165929952793063050668457)
    ·
      refine ⟨5374447464594797288001343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7165929952793063050668457 5374447464594797288001343)
      ·
        refine ⟨8061671196892195932002015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374447464594797288001343 8061671196892195932002015)
        ·
          refine ⟨12092506795338293898003023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061671196892195932002015 12092506795338293898003023)
          ·
            refine ⟨18138760193007440847004535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092506795338293898003023 18138760193007440847004535)
            ·
              refine ⟨27208140289511161270506803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138760193007440847004535 27208140289511161270506803)
              ·
                refine ⟨40812210434266741905760205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27208140289511161270506803 40812210434266741905760205)
                ·
                  refine ⟨15304578912850028214660077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40812210434266741905760205 15304578912850028214660077)
                  ·
                    refine ⟨5739217092318760580497529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15304578912850028214660077 5739217092318760580497529)
                    ·
                      refine ⟨4304412819239070435373147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739217092318760580497529 4304412819239070435373147)
                      ·
                        rfl

theorem cell23_8382814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_8382814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382814 prefixEnd_8382814 := by exact prefixLift 8382814
  have htrace : WordTrace (prefixWord ++ tailWord_8382814) baseStart_8382814 baseEnd_8382814 := by
    simpa [prefixWord, tailWord_8382814, baseEnd_8382814] using wordTrace_append hprefix tailTrace_8382814
  have hstable : (prefixWord ++ tailWord_8382814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382814).length < 2 ^ (prefixWord ++ tailWord_8382814).sum := by decide
  have hdescent : baseEnd_8382814 < baseStart_8382814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382850 : List Nat := [3, 4, 2, 1, 2, 1, 1, 4, 5]
def baseStart_8382850 : Nat := 118140960795 + 8382850 * 2 ^ 59
def prefixEnd_8382850 : Nat := 4983230072969 + 3 ^ 40 * 8382850 * 2
def baseEnd_8382850 : Nat := 478270144949181366058109

theorem tailTrace_8382850 : CollatzResearch.WordTrace tailWord_8382850 prefixEnd_8382850 478270144949181366058109 := by
  unfold tailWord_8382850
  simp only [CollatzResearch.WordTrace]
  refine ⟨76436914420093400410874501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203831771786915734428998669 76436914420093400410874501)
  ·
    refine ⟨14331921453767512577038969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76436914420093400410874501 14331921453767512577038969)
    ·
      refine ⟨10748941090325634432779227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14331921453767512577038969 10748941090325634432779227)
      ·
        refine ⟨16123411635488451649168841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10748941090325634432779227 16123411635488451649168841)
        ·
          refine ⟨12092558726616338736876631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16123411635488451649168841 12092558726616338736876631)
          ·
            refine ⟨18138838089924508105314947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092558726616338736876631 18138838089924508105314947)
            ·
              refine ⟨27208257134886762157972421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138838089924508105314947 27208257134886762157972421)
              ·
                refine ⟨5101548212791267904619829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27208257134886762157972421 5101548212791267904619829)
                ·
                  refine ⟨478270144949181366058109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101548212791267904619829 478270144949181366058109)
                  ·
                    rfl

theorem cell23_8382850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_8382850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382850 prefixEnd_8382850 := by exact prefixLift 8382850
  have htrace : WordTrace (prefixWord ++ tailWord_8382850) baseStart_8382850 baseEnd_8382850 := by
    simpa [prefixWord, tailWord_8382850, baseEnd_8382850] using wordTrace_append hprefix tailTrace_8382850
  have hstable : (prefixWord ++ tailWord_8382850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382850).length < 2 ^ (prefixWord ++ tailWord_8382850).sum := by decide
  have hdescent : baseEnd_8382850 < baseStart_8382850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382869 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_8382869 : Nat := 118140960795 + 8382869 * 2 ^ 59
def prefixEnd_8382869 : Nat := 4983230072969 + 3 ^ 40 * 8382869 * 2
def baseEnd_8382869 : Nat := 4304441060675067720185393

theorem tailTrace_8382869 : CollatzResearch.WordTrace tailWord_8382869 prefixEnd_8382869 4304441060675067720185393 := by
  unfold tailWord_8382869
  simp only [CollatzResearch.WordTrace]
  refine ⟨305748350667304767888439661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203832233778203178592293107 305748350667304767888439661)
  ·
    refine ⟨114655631500239287958164873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305748350667304767888439661 114655631500239287958164873)
    ·
      refine ⟨85991723625179465968623655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114655631500239287958164873 85991723625179465968623655)
      ·
        refine ⟨128987585437769198952935483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85991723625179465968623655 128987585437769198952935483)
        ·
          refine ⟨193481378156653798429403225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128987585437769198952935483 193481378156653798429403225)
          ·
            refine ⟨145111033617490348822052419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193481378156653798429403225 145111033617490348822052419)
            ·
              refine ⟨217666550426235523233078629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145111033617490348822052419 217666550426235523233078629)
              ·
                refine ⟨40812478204919160606202243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217666550426235523233078629 40812478204919160606202243)
                ·
                  refine ⟨61218717307378740909303365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40812478204919160606202243 61218717307378740909303365)
                  ·
                    refine ⟨11478509495133513920494381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61218717307378740909303365 11478509495133513920494381)
                    ·
                      refine ⟨4304441060675067720185393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11478509495133513920494381 4304441060675067720185393)
                      ·
                        rfl

theorem cell23_8382869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_8382869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382869 prefixEnd_8382869 := by exact prefixLift 8382869
  have htrace : WordTrace (prefixWord ++ tailWord_8382869) baseStart_8382869 baseEnd_8382869 := by
    simpa [prefixWord, tailWord_8382869, baseEnd_8382869] using wordTrace_append hprefix tailTrace_8382869
  have hstable : (prefixWord ++ tailWord_8382869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382869).length < 2 ^ (prefixWord ++ tailWord_8382869).sum := by decide
  have hdescent : baseEnd_8382869 < baseStart_8382869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382909 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_8382909 : Nat := 118140960795 + 8382909 * 2 ^ 59
def prefixEnd_8382909 : Nat := 4983230072969 + 3 ^ 40 * 8382909 * 2
def baseEnd_8382909 : Nat := 4304461599901247563685209

theorem tailTrace_8382909 : CollatzResearch.WordTrace tailWord_8382909 prefixEnd_8382909 4304461599901247563685209 := by
  unfold tailWord_8382909
  simp only [CollatzResearch.WordTrace]
  refine ⟨305749809587159854719895781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203833206391439903146597187 305749809587159854719895781)
  ·
    refine ⟨57328089297592472759980459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305749809587159854719895781 57328089297592472759980459)
    ·
      refine ⟨85992133946388709139970689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57328089297592472759980459 85992133946388709139970689)
      ·
        refine ⟨64494100459791531854978017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85992133946388709139970689 64494100459791531854978017)
        ·
          refine ⟨48370575344843648891233513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64494100459791531854978017 48370575344843648891233513)
          ·
            refine ⟨36277931508632736668425135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48370575344843648891233513 36277931508632736668425135)
            ·
              refine ⟨54416897262949105002637703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36277931508632736668425135 54416897262949105002637703)
              ·
                refine ⟨81625345894423657503956555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54416897262949105002637703 81625345894423657503956555)
                ·
                  refine ⟨122438018841635486255934833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81625345894423657503956555 122438018841635486255934833)
                  ·
                    refine ⟨91828514131226614691951125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122438018841635486255934833 91828514131226614691951125)
                    ·
                      refine ⟨4304461599901247563685209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91828514131226614691951125 4304461599901247563685209)
                      ·
                        rfl

theorem cell23_8382909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_8382909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382909 prefixEnd_8382909 := by exact prefixLift 8382909
  have htrace : WordTrace (prefixWord ++ tailWord_8382909) baseStart_8382909 baseEnd_8382909 := by
    simpa [prefixWord, tailWord_8382909, baseEnd_8382909] using wordTrace_append hprefix tailTrace_8382909
  have hstable : (prefixWord ++ tailWord_8382909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382909).length < 2 ^ (prefixWord ++ tailWord_8382909).sum := by decide
  have hdescent : baseEnd_8382909 < baseStart_8382909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382933 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_8382933 : Nat := 118140960795 + 8382933 * 2 ^ 59
def prefixEnd_8382933 : Nat := 4983230072969 + 3 ^ 40 * 8382933 * 2
def baseEnd_8382933 : Nat := 4304473923436955469785099

theorem tailTrace_8382933 : CollatzResearch.WordTrace tailWord_8382933 prefixEnd_8382933 4304473923436955469785099 := by
  unfold tailWord_8382933
  simp only [CollatzResearch.WordTrace]
  refine ⟨305750684939072906818769453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203833789959381937879179635 305750684939072906818769453)
  ·
    refine ⟨114656506852152340057038545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305750684939072906818769453 114656506852152340057038545)
    ·
      refine ⟨85992380139114255042778909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114656506852152340057038545 85992380139114255042778909)
      ·
        refine ⟨32247142552167845641042091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85992380139114255042778909 32247142552167845641042091)
        ·
          refine ⟨48370713828251768461563137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32247142552167845641042091 48370713828251768461563137)
          ·
            refine ⟨36278035371188826346172353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48370713828251768461563137 36278035371188826346172353)
            ·
              refine ⟨27208526528391619759629265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36278035371188826346172353 27208526528391619759629265)
              ·
                refine ⟨20406394896293714819721949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27208526528391619759629265 20406394896293714819721949)
                ·
                  refine ⟨7652398086110143057395731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20406394896293714819721949 7652398086110143057395731)
                  ·
                    refine ⟨11478597129165214586093597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652398086110143057395731 11478597129165214586093597)
                    ·
                      refine ⟨4304473923436955469785099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11478597129165214586093597 4304473923436955469785099)
                      ·
                        rfl

theorem cell23_8382933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_8382933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382933 prefixEnd_8382933 := by exact prefixLift 8382933
  have htrace : WordTrace (prefixWord ++ tailWord_8382933) baseStart_8382933 baseEnd_8382933 := by
    simpa [prefixWord, tailWord_8382933, baseEnd_8382933] using wordTrace_append hprefix tailTrace_8382933
  have hstable : (prefixWord ++ tailWord_8382933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382933).length < 2 ^ (prefixWord ++ tailWord_8382933).sum := by decide
  have hdescent : baseEnd_8382933 < baseStart_8382933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382956 : List Nat := [2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 4]
def baseStart_8382956 : Nat := 118140960795 + 8382956 * 2 ^ 59
def prefixEnd_8382956 : Nat := 4983230072969 + 3 ^ 40 * 8382956 * 2
def baseEnd_8382956 : Nat := 4304485733492008879797493

theorem tailTrace_8382956 : CollatzResearch.WordTrace tailWord_8382956 prefixEnd_8382956 4304485733492008879797493 := by
  unfold tailWord_8382956
  simp only [CollatzResearch.WordTrace]
  refine ⟨152875761908994790873428361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203834349211993054497904481 152875761908994790873428361)
  ·
    refine ⟨114656821431746093155071271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152875761908994790873428361 114656821431746093155071271)
    ·
      refine ⟨171985232147619139732606907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114656821431746093155071271 171985232147619139732606907)
      ·
        refine ⟨257977848221428709598910361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171985232147619139732606907 257977848221428709598910361)
        ·
          refine ⟨193483386166071532199182771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257977848221428709598910361 193483386166071532199182771)
          ·
            refine ⟨290225079249107298298774157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193483386166071532199182771 290225079249107298298774157)
            ·
              refine ⟨108834404718415236862040309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290225079249107298298774157 108834404718415236862040309)
              ·
                refine ⟨10203225442351428455816279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108834404718415236862040309 10203225442351428455816279)
                ·
                  refine ⟨15304838163527142683724419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203225442351428455816279 15304838163527142683724419)
                  ·
                    refine ⟨22957257245290714025586629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15304838163527142683724419 22957257245290714025586629)
                    ·
                      refine ⟨4304485733492008879797493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22957257245290714025586629 4304485733492008879797493)
                      ·
                        rfl

theorem cell23_8382956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_8382956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382956 prefixEnd_8382956 := by exact prefixLift 8382956
  have htrace : WordTrace (prefixWord ++ tailWord_8382956) baseStart_8382956 baseEnd_8382956 := by
    simpa [prefixWord, tailWord_8382956, baseEnd_8382956] using wordTrace_append hprefix tailTrace_8382956
  have hstable : (prefixWord ++ tailWord_8382956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382956).length < 2 ^ (prefixWord ++ tailWord_8382956).sum := by decide
  have hdescent : baseEnd_8382956 < baseStart_8382956 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382969 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_8382969 : Nat := 118140960795 + 8382969 * 2 ^ 59
def prefixEnd_8382969 : Nat := 4983230072969 + 3 ^ 40 * 8382969 * 2
def baseEnd_8382969 : Nat := 4304492408740517328934933

theorem tailTrace_8382969 : CollatzResearch.WordTrace tailWord_8382969 prefixEnd_8382969 4304492408740517328934933 := by
  unfold tailWord_8382969
  simp only [CollatzResearch.WordTrace]
  refine ⟨305751997966942484967079961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203834665311294989978053307 305751997966942484967079961)
  ·
    refine ⟨229313998475206863725309971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305751997966942484967079961 229313998475206863725309971)
    ·
      refine ⟨343970997712810295587964957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229313998475206863725309971 343970997712810295587964957)
      ·
        refine ⟨128989124142303860845486859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343970997712810295587964957 128989124142303860845486859)
        ·
          refine ⟨193483686213455791268230289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128989124142303860845486859 193483686213455791268230289)
          ·
            refine ⟨145112764660091843451172717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193483686213455791268230289 145112764660091843451172717)
            ·
              refine ⟨54417286747534441294189769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145112764660091843451172717 54417286747534441294189769)
              ·
                refine ⟨40812965060650830970642327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54417286747534441294189769 40812965060650830970642327)
                ·
                  refine ⟨61219447590976246455963491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40812965060650830970642327 61219447590976246455963491)
                  ·
                    refine ⟨91829171386464369683945237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61219447590976246455963491 91829171386464369683945237)
                    ·
                      refine ⟨4304492408740517328934933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91829171386464369683945237 4304492408740517328934933)
                      ·
                        rfl

theorem cell23_8382969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_8382969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382969 prefixEnd_8382969 := by exact prefixLift 8382969
  have htrace : WordTrace (prefixWord ++ tailWord_8382969) baseStart_8382969 baseEnd_8382969 := by
    simpa [prefixWord, tailWord_8382969, baseEnd_8382969] using wordTrace_append hprefix tailTrace_8382969
  have hstable : (prefixWord ++ tailWord_8382969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382969).length < 2 ^ (prefixWord ++ tailWord_8382969).sum := by decide
  have hdescent : baseEnd_8382969 < baseStart_8382969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382979 : List Nat := [1, 1, 1, 3, 2, 1, 6, 8]
def baseStart_8382979 : Nat := 118140960795 + 8382979 * 2 ^ 59
def prefixEnd_8382979 : Nat := 4983230072969 + 3 ^ 40 * 8382979 * 2
def baseEnd_8382979 : Nat := 159425834946187492215181

theorem tailTrace_8382979 : CollatzResearch.WordTrace tailWord_8382979 prefixEnd_8382979 159425834946187492215181 := by
  unfold tailWord_8382979
  simp only [CollatzResearch.WordTrace]
  refine ⟨305752362696906256674943991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203834908464604171116629327 305752362696906256674943991)
  ·
    refine ⟨458628544045359385012415987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305752362696906256674943991 458628544045359385012415987)
    ·
      refine ⟨687942816068039077518623981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458628544045359385012415987 687942816068039077518623981)
      ·
        refine ⟨257978556025514654069483993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 687942816068039077518623981 257978556025514654069483993)
        ·
          refine ⟨193483917019135990552112995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257978556025514654069483993 193483917019135990552112995)
          ·
            refine ⟨290225875528703985828169493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193483917019135990552112995 290225875528703985828169493)
            ·
              refine ⟨13604337915407999335695445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290225875528703985828169493 13604337915407999335695445)
              ·
                refine ⟨159425834946187492215181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13604337915407999335695445 159425834946187492215181)
                ·
                  rfl

theorem cell23_8382979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 8].length) (baseStart_8382979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382979 prefixEnd_8382979 := by exact prefixLift 8382979
  have htrace : WordTrace (prefixWord ++ tailWord_8382979) baseStart_8382979 baseEnd_8382979 := by
    simpa [prefixWord, tailWord_8382979, baseEnd_8382979] using wordTrace_append hprefix tailTrace_8382979
  have hstable : (prefixWord ++ tailWord_8382979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382979).length < 2 ^ (prefixWord ++ tailWord_8382979).sum := by decide
  have hdescent : baseEnd_8382979 < baseStart_8382979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382986 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_8382986 : Nat := 118140960795 + 8382986 * 2 ^ 59
def prefixEnd_8382986 : Nat := 4983230072969 + 3 ^ 40 * 8382986 * 2
def baseEnd_8382986 : Nat := 4304501137911643762422355

theorem tailTrace_8382986 : CollatzResearch.WordTrace tailWord_8382986 prefixEnd_8382986 4304501137911643762422355 := by
  unfold tailWord_8382986
  simp only [CollatzResearch.WordTrace]
  refine ⟨76438154501970224217612203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203835078671920597913632541 76438154501970224217612203)
  ·
    refine ⟨114657231752955336326418305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76438154501970224217612203 114657231752955336326418305)
    ·
      refine ⟨85992923814716502244813729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114657231752955336326418305 85992923814716502244813729)
      ·
        refine ⟨64494692861037376683610297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85992923814716502244813729 64494692861037376683610297)
        ·
          refine ⟨48371019645778032512707723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64494692861037376683610297 48371019645778032512707723)
          ·
            refine ⟨72556529468667048769061585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48371019645778032512707723 72556529468667048769061585)
            ·
              refine ⟨54417397101500286576796189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72556529468667048769061585 54417397101500286576796189)
              ·
                refine ⟨20406523913062607466298571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54417397101500286576796189 20406523913062607466298571)
                ·
                  refine ⟨30609785869593911199447857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20406523913062607466298571 30609785869593911199447857)
                  ·
                    refine ⟨22957339402195433399585893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30609785869593911199447857 22957339402195433399585893)
                    ·
                      refine ⟨4304501137911643762422355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22957339402195433399585893 4304501137911643762422355)
                      ·
                        rfl

theorem cell23_8382986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_8382986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382986 prefixEnd_8382986 := by exact prefixLift 8382986
  have htrace : WordTrace (prefixWord ++ tailWord_8382986) baseStart_8382986 baseEnd_8382986 := by
    simpa [prefixWord, tailWord_8382986, baseEnd_8382986] using wordTrace_append hprefix tailTrace_8382986
  have hstable : (prefixWord ++ tailWord_8382986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382986).length < 2 ^ (prefixWord ++ tailWord_8382986).sum := by decide
  have hdescent : baseEnd_8382986 < baseStart_8382986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8382990 : List Nat := [4, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_8382990 : Nat := 118140960795 + 8382990 * 2 ^ 59
def prefixEnd_8382990 : Nat := 4983230072969 + 3 ^ 40 * 8382990 * 2
def baseEnd_8382990 : Nat := 4304503191834261746772337

theorem tailTrace_8382990 : CollatzResearch.WordTrace tailWord_8382990 prefixEnd_8382990 4304503191834261746772337 := by
  unfold tailWord_8382990
  simp only [CollatzResearch.WordTrace]
  refine ⟨38219095487483300694199303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203835175933244270369062949 38219095487483300694199303)
  ·
    refine ⟨57328643231224951041298955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38219095487483300694199303 57328643231224951041298955)
    ·
      refine ⟨85992964846837426561948433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57328643231224951041298955 85992964846837426561948433)
      ·
        refine ⟨64494723635128069921461325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85992964846837426561948433 64494723635128069921461325)
        ·
          refine ⟨24185521363173026220547997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64494723635128069921461325 24185521363173026220547997)
          ·
            refine ⟨9069570511189884832705499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24185521363173026220547997 9069570511189884832705499)
            ·
              refine ⟨13604355766784827249058249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069570511189884832705499 13604355766784827249058249)
              ·
                refine ⟨10203266825088620436793687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13604355766784827249058249 10203266825088620436793687)
                ·
                  refine ⟨15304900237632930655190531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203266825088620436793687 15304900237632930655190531)
                  ·
                    refine ⟨22957350356449395982785797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15304900237632930655190531 22957350356449395982785797)
                    ·
                      refine ⟨4304503191834261746772337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22957350356449395982785797 4304503191834261746772337)
                      ·
                        rfl

theorem cell23_8382990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_8382990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8382990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8382990 prefixEnd_8382990 := by exact prefixLift 8382990
  have htrace : WordTrace (prefixWord ++ tailWord_8382990) baseStart_8382990 baseEnd_8382990 := by
    simpa [prefixWord, tailWord_8382990, baseEnd_8382990] using wordTrace_append hprefix tailTrace_8382990
  have hstable : (prefixWord ++ tailWord_8382990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8382990).length < 2 ^ (prefixWord ++ tailWord_8382990).sum := by decide
  have hdescent : baseEnd_8382990 < baseStart_8382990 := by decide
  rcases family_descends (prefixWord ++ tailWord_8382990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383019 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5]
def baseStart_8383019 : Nat := 118140960795 + 8383019 * 2 ^ 59
def prefixEnd_8383019 : Nat := 4983230072969 + 3 ^ 40 * 8383019 * 2
def baseEnd_8383019 : Nat := 4304518082773242133309703

theorem tailTrace_8383019 : CollatzResearch.WordTrace tailWord_8383019 prefixEnd_8383019 4304518082773242133309703 := by
  unfold tailWord_8383019
  simp only [CollatzResearch.WordTrace]
  refine ⟨305753821616761343506400111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203835881077840895670933407 305753821616761343506400111)
  ·
    refine ⟨458630732425142015259600167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305753821616761343506400111 458630732425142015259600167)
    ·
      refine ⟨687946098637713022889400251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458630732425142015259600167 687946098637713022889400251)
      ·
        refine ⟨1031919147956569534334100377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687946098637713022889400251 1031919147956569534334100377)
        ·
          refine ⟨773939360967427150750575283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031919147956569534334100377 773939360967427150750575283)
          ·
            refine ⟨1160909041451140726125862925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773939360967427150750575283 1160909041451140726125862925)
            ·
              refine ⟨435340890544177772297198597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1160909041451140726125862925 435340890544177772297198597)
              ·
                refine ⟨81626416977033332305724737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435340890544177772297198597 81626416977033332305724737)
                ·
                  refine ⟨61219812732774999229293553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81626416977033332305724737 61219812732774999229293553)
                  ·
                    refine ⟨45914859549581249421970165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61219812732774999229293553 45914859549581249421970165)
                    ·
                      refine ⟨4304518082773242133309703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45914859549581249421970165 4304518082773242133309703)
                      ·
                        rfl

theorem cell23_8383019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_8383019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383019 prefixEnd_8383019 := by exact prefixLift 8383019
  have htrace : WordTrace (prefixWord ++ tailWord_8383019) baseStart_8383019 baseEnd_8383019 := by
    simpa [prefixWord, tailWord_8383019, baseEnd_8383019] using wordTrace_append hprefix tailTrace_8383019
  have hstable : (prefixWord ++ tailWord_8383019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383019).length < 2 ^ (prefixWord ++ tailWord_8383019).sum := by decide
  have hdescent : baseEnd_8383019 < baseStart_8383019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383033 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 5, 3, 2]
def baseStart_8383033 : Nat := 118140960795 + 8383033 * 2 ^ 59
def prefixEnd_8383033 : Nat := 4983230072969 + 3 ^ 40 * 8383033 * 2
def baseEnd_8383033 : Nat := 4304525271502405078534639

theorem tailTrace_8383033 : CollatzResearch.WordTrace tailWord_8383033 prefixEnd_8383033 4304525271502405078534639 := by
  unfold tailWord_8383033
  simp only [CollatzResearch.WordTrace]
  refine ⟨305754332238710623897409753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203836221492473749264939835 305754332238710623897409753)
  ·
    refine ⟨229315749179032967923057315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305754332238710623897409753 229315749179032967923057315)
    ·
      refine ⟨343973623768549451884585973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229315749179032967923057315 343973623768549451884585973)
      ·
        refine ⟨32247527228301511114179935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 343973623768549451884585973 32247527228301511114179935)
        ·
          refine ⟨48371290842452266671269903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32247527228301511114179935 48371290842452266671269903)
          ·
            refine ⟨72556936263678400006904855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48371290842452266671269903 72556936263678400006904855)
            ·
              refine ⟨108835404395517600010357283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72556936263678400006904855 108835404395517600010357283)
              ·
                refine ⟨163253106593276400015535925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108835404395517600010357283 163253106593276400015535925)
                ·
                  refine ⟨15304978743119662501456493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163253106593276400015535925 15304978743119662501456493)
                  ·
                    refine ⟨5739367028669873438046185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15304978743119662501456493 5739367028669873438046185)
                    ·
                      refine ⟨4304525271502405078534639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739367028669873438046185 4304525271502405078534639)
                      ·
                        rfl

theorem cell23_8383033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_8383033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383033 prefixEnd_8383033 := by exact prefixLift 8383033
  have htrace : WordTrace (prefixWord ++ tailWord_8383033) baseStart_8383033 baseEnd_8383033 := by
    simpa [prefixWord, tailWord_8383033, baseEnd_8383033] using wordTrace_append hprefix tailTrace_8383033
  have hstable : (prefixWord ++ tailWord_8383033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383033).length < 2 ^ (prefixWord ++ tailWord_8383033).sum := by decide
  have hdescent : baseEnd_8383033 < baseStart_8383033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383063 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 1, 4, 2]
def baseStart_8383063 : Nat := 118140960795 + 8383063 * 2 ^ 59
def prefixEnd_8383063 : Nat := 4983230072969 + 3 ^ 40 * 8383063 * 2
def baseEnd_8383063 : Nat := 4304540675922039961159501

theorem tailTrace_8383063 : CollatzResearch.WordTrace tailWord_8383063 prefixEnd_8383063 4304540675922039961159501 := by
  unfold tailWord_8383063
  simp only [CollatzResearch.WordTrace]
  refine ⟨305755426428601939021001843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203836950952401292680667895 305755426428601939021001843)
  ·
    refine ⟨458633139642902908531502765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305755426428601939021001843 458633139642902908531502765)
    ·
      refine ⟨171987427366088590699313537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458633139642902908531502765 171987427366088590699313537)
      ·
        refine ⟨128990570524566443024485153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 171987427366088590699313537 128990570524566443024485153)
        ·
          refine ⟨96742927893424832268363865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128990570524566443024485153 96742927893424832268363865)
          ·
            refine ⟨72557195920068624201272899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96742927893424832268363865 72557195920068624201272899)
            ·
              refine ⟨108835793880102936301909349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72557195920068624201272899 108835793880102936301909349)
              ·
                refine ⟨20406711352519300556608003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108835793880102936301909349 20406711352519300556608003)
                ·
                  refine ⟨30610067028778950834912005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20406711352519300556608003 30610067028778950834912005)
                  ·
                    refine ⟨5739387567896053281546001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30610067028778950834912005 5739387567896053281546001)
                    ·
                      refine ⟨4304540675922039961159501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739387567896053281546001 4304540675922039961159501)
                      ·
                        rfl

theorem cell23_8383063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_8383063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383063 prefixEnd_8383063 := by exact prefixLift 8383063
  have htrace : WordTrace (prefixWord ++ tailWord_8383063) baseStart_8383063 baseEnd_8383063 := by
    simpa [prefixWord, tailWord_8383063, baseEnd_8383063] using wordTrace_append hprefix tailTrace_8383063
  have hstable : (prefixWord ++ tailWord_8383063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383063).length < 2 ^ (prefixWord ++ tailWord_8383063).sum := by decide
  have hdescent : baseEnd_8383063 < baseStart_8383063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383076 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_8383076 : Nat := 118140960795 + 8383076 * 2 ^ 59
def prefixEnd_8383076 : Nat := 4983230072969 + 3 ^ 40 * 8383076 * 2
def baseEnd_8383076 : Nat := 4304547351170548410296941

theorem tailTrace_8383076 : CollatzResearch.WordTrace tailWord_8383076 prefixEnd_8383076 4304547351170548410296941 := by
  unfold tailWord_8383076
  simp only [CollatzResearch.WordTrace]
  refine ⟨152877950288777421120612541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203837267051703228160816721 152877950288777421120612541)
  ·
    refine ⟨57329231358291532920229703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152877950288777421120612541 57329231358291532920229703)
    ·
      refine ⟨85993847037437299380344555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57329231358291532920229703 85993847037437299380344555)
      ·
        refine ⟨128990770556155949070516833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85993847037437299380344555 128990770556155949070516833)
        ·
          refine ⟨96743077917116961802887625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128990770556155949070516833 96743077917116961802887625)
          ·
            refine ⟨72557308437837721352165719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96743077917116961802887625 72557308437837721352165719)
            ·
              refine ⟨108835962656756582028248579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72557308437837721352165719 108835962656756582028248579)
              ·
                refine ⟨163253943985134873042372869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108835962656756582028248579 163253943985134873042372869)
                ·
                  refine ⟨30610114497212788695444913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163253943985134873042372869 30610114497212788695444913)
                  ·
                    refine ⟨22957585872909591521583685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30610114497212788695444913 22957585872909591521583685)
                    ·
                      refine ⟨4304547351170548410296941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22957585872909591521583685 4304547351170548410296941)
                      ·
                        rfl

theorem cell23_8383076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_8383076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383076 prefixEnd_8383076 := by exact prefixLift 8383076
  have htrace : WordTrace (prefixWord ++ tailWord_8383076) baseStart_8383076 baseEnd_8383076 := by
    simpa [prefixWord, tailWord_8383076, baseEnd_8383076] using wordTrace_append hprefix tailTrace_8383076
  have hstable : (prefixWord ++ tailWord_8383076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383076).length < 2 ^ (prefixWord ++ tailWord_8383076).sum := by decide
  have hdescent : baseEnd_8383076 < baseStart_8383076 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383137 : List Nat := [1, 2, 3, 3, 3, 1, 3, 2, 5]
def baseStart_8383137 : Nat := 118140960795 + 8383137 * 2 ^ 59
def prefixEnd_8383137 : Nat := 4983230072969 + 3 ^ 40 * 8383137 * 2
def baseEnd_8383137 : Nat := 478286519276719185737129

theorem tailTrace_8383137 : CollatzResearch.WordTrace tailWord_8383137 prefixEnd_8383137 478286519276719185737129 := by
  unfold tailWord_8383137
  simp only [CollatzResearch.WordTrace]
  refine ⟨305758125430333849659195665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203838750286889233106130443 305758125430333849659195665)
  ·
    refine ⟨229318594072750387244396749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305758125430333849659195665 229318594072750387244396749)
    ·
      refine ⟨85994472777281395216648781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229318594072750387244396749 85994472777281395216648781)
      ·
        refine ⟨32247927291480523206243293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85994472777281395216648781 32247927291480523206243293)
        ·
          refine ⟨12092972734305196202341235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32247927291480523206243293 12092972734305196202341235)
          ·
            refine ⟨18139459101457794303511853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092972734305196202341235 18139459101457794303511853)
            ·
              refine ⟨6802297163046672863816945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18139459101457794303511853 6802297163046672863816945)
              ·
                refine ⟨5101722872285004647862709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6802297163046672863816945 5101722872285004647862709)
                ·
                  refine ⟨478286519276719185737129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5101722872285004647862709 478286519276719185737129)
                  ·
                    rfl

theorem cell23_8383137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 2, 5].length) (baseStart_8383137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383137 prefixEnd_8383137 := by exact prefixLift 8383137
  have htrace : WordTrace (prefixWord ++ tailWord_8383137) baseStart_8383137 baseEnd_8383137 := by
    simpa [prefixWord, tailWord_8383137, baseEnd_8383137] using wordTrace_append hprefix tailTrace_8383137
  have hstable : (prefixWord ++ tailWord_8383137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383137).length < 2 ^ (prefixWord ++ tailWord_8383137).sum := by decide
  have hdescent : baseEnd_8383137 < baseStart_8383137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383193 : List Nat := [1, 2, 1, 2, 3, 2, 4, 2, 6]
def baseStart_8383193 : Nat := 118140960795 + 8383193 * 2 ^ 59
def prefixEnd_8383193 : Nat := 4983230072969 + 3 ^ 40 * 8383193 * 2
def baseEnd_8383193 : Nat := 478289714267458272503767

theorem tailTrace_8383193 : CollatzResearch.WordTrace tailWord_8383193 prefixEnd_8383193 478289714267458272503767 := by
  unfold tailWord_8383193
  simp only [CollatzResearch.WordTrace]
  refine ⟨305760167918130971223234233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203840111945420647482156155 305760167918130971223234233)
  ·
    refine ⟨229320125938598228417425675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305760167918130971223234233 229320125938598228417425675)
    ·
      refine ⟨343980188907897342626138513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229320125938598228417425675 343980188907897342626138513)
      ·
        refine ⟨257985141680923006969603885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343980188907897342626138513 257985141680923006969603885)
        ·
          refine ⟨96744428130346127613601457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257985141680923006969603885 96744428130346127613601457)
          ·
            refine ⟨72558321097759595710201093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96744428130346127613601457 72558321097759595710201093)
            ·
              refine ⟨13604685205829924195662705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72558321097759595710201093 13604685205829924195662705)
              ·
                refine ⟨10203513904372443146747029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13604685205829924195662705 10203513904372443146747029)
                ·
                  refine ⟨478289714267458272503767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10203513904372443146747029 478289714267458272503767)
                  ·
                    rfl

theorem cell23_8383193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_8383193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383193 prefixEnd_8383193 := by exact prefixLift 8383193
  have htrace : WordTrace (prefixWord ++ tailWord_8383193) baseStart_8383193 baseEnd_8383193 := by
    simpa [prefixWord, tailWord_8383193, baseEnd_8383193] using wordTrace_append hprefix tailTrace_8383193
  have hstable : (prefixWord ++ tailWord_8383193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383193).length < 2 ^ (prefixWord ++ tailWord_8383193).sum := by decide
  have hdescent : baseEnd_8383193 < baseStart_8383193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383216 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_8383216 : Nat := 118140960795 + 8383216 * 2 ^ 59
def prefixEnd_8383216 : Nat := 4983230072969 + 3 ^ 40 * 8383216 * 2
def baseEnd_8383216 : Nat := 4304619238462177862546297

theorem tailTrace_8383216 : CollatzResearch.WordTrace tailWord_8383216 prefixEnd_8383216 4304619238462177862546297 := by
  unfold tailWord_8383216
  simp only [CollatzResearch.WordTrace]
  refine ⟨152880503398523823075660751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203840671198031764100881001 152880503398523823075660751)
  ·
    refine ⟨229320755097785734613491127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152880503398523823075660751 229320755097785734613491127)
    ·
      refine ⟨343981132646678601920236691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229320755097785734613491127 343981132646678601920236691)
      ·
        refine ⟨515971698970017902880355037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343981132646678601920236691 515971698970017902880355037)
        ·
          refine ⟨193489387113756713580133139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515971698970017902880355037 193489387113756713580133139)
          ·
            refine ⟨290234080670635070370199709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193489387113756713580133139 290234080670635070370199709)
            ·
              refine ⟨108837780251488151388824891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290234080670635070370199709 108837780251488151388824891)
              ·
                refine ⟨163256670377232227083237337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108837780251488151388824891 163256670377232227083237337)
                ·
                  refine ⟨122442502782924170312428003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163256670377232227083237337 122442502782924170312428003)
                  ·
                    refine ⟨183663754174386255468642005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122442502782924170312428003 183663754174386255468642005)
                    ·
                      refine ⟨4304619238462177862546297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183663754174386255468642005 4304619238462177862546297)
                      ·
                        rfl

theorem cell23_8383216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_8383216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383216 prefixEnd_8383216 := by exact prefixLift 8383216
  have htrace : WordTrace (prefixWord ++ tailWord_8383216) baseStart_8383216 baseEnd_8383216 := by
    simpa [prefixWord, tailWord_8383216, baseEnd_8383216] using wordTrace_append hprefix tailTrace_8383216
  have hstable : (prefixWord ++ tailWord_8383216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383216).length < 2 ^ (prefixWord ++ tailWord_8383216).sum := by decide
  have hdescent : baseEnd_8383216 < baseStart_8383216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383221 : List Nat := [1, 3, 6, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8383221 : Nat := 118140960795 + 8383221 * 2 ^ 59
def prefixEnd_8383221 : Nat := 4983230072969 + 3 ^ 40 * 8383221 * 2
def baseEnd_8383221 : Nat := 4304621805865450342983775

theorem tailTrace_8383221 : CollatzResearch.WordTrace tailWord_8383221 prefixEnd_8383221 4304621805865450342983775 := by
  unfold tailWord_8383221
  simp only [CollatzResearch.WordTrace]
  refine ⟨305761189162029532005253517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203840792774686354670169011 305761189162029532005253517)
  ·
    refine ⟨114660445935761074501970069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305761189162029532005253517 114660445935761074501970069)
    ·
      refine ⟨5374708403238800367279847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 114660445935761074501970069 5374708403238800367279847)
      ·
        refine ⟨8062062604858200550919771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374708403238800367279847 8062062604858200550919771)
        ·
          refine ⟨12093093907287300826379657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062062604858200550919771 12093093907287300826379657)
          ·
            refine ⟨9069820430465475619784743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12093093907287300826379657 9069820430465475619784743)
            ·
              refine ⟨13604730645698213429677115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069820430465475619784743 13604730645698213429677115)
              ·
                refine ⟨20407095968547320144515673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13604730645698213429677115 20407095968547320144515673)
                ·
                  refine ⟨15305321976410490108386755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20407095968547320144515673 15305321976410490108386755)
                  ·
                    refine ⟨22957982964615735162580133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15305321976410490108386755 22957982964615735162580133)
                    ·
                      refine ⟨4304621805865450342983775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22957982964615735162580133 4304621805865450342983775)
                      ·
                        rfl

theorem cell23_8383221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8383221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383221 prefixEnd_8383221 := by exact prefixLift 8383221
  have htrace : WordTrace (prefixWord ++ tailWord_8383221) baseStart_8383221 baseEnd_8383221 := by
    simpa [prefixWord, tailWord_8383221, baseEnd_8383221] using wordTrace_append hprefix tailTrace_8383221
  have hstable : (prefixWord ++ tailWord_8383221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383221).length < 2 ^ (prefixWord ++ tailWord_8383221).sum := by decide
  have hdescent : baseEnd_8383221 < baseStart_8383221 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383223 : List Nat := [1, 1, 3, 1, 1, 1, 3, 6, 1, 5]
def baseStart_8383223 : Nat := 118140960795 + 8383223 * 2 ^ 59
def prefixEnd_8383223 : Nat := 4983230072969 + 3 ^ 40 * 8383223 * 2
def baseEnd_8383223 : Nat := 1434874277608919778386255

theorem tailTrace_8383223 : CollatzResearch.WordTrace tailWord_8383223 prefixEnd_8383223 1434874277608919778386255 := by
  unfold tailWord_8383223
  simp only [CollatzResearch.WordTrace]
  refine ⟨305761262108022286346826323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203840841405348190897884215 305761262108022286346826323)
  ·
    refine ⟨458641893162033429520239485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305761262108022286346826323 458641893162033429520239485)
    ·
      refine ⟨171990709935762536070089807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458641893162033429520239485 171990709935762536070089807)
      ·
        refine ⟨257986064903643804105134711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171990709935762536070089807 257986064903643804105134711)
        ·
          refine ⟨386979097355465706157702067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257986064903643804105134711 386979097355465706157702067)
          ·
            refine ⟨580468646033198559236553101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386979097355465706157702067 580468646033198559236553101)
            ·
              refine ⟨217675742262449459713707413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580468646033198559236553101 217675742262449459713707413)
              ·
                refine ⟨10203550418552318424080035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217675742262449459713707413 10203550418552318424080035)
                ·
                  refine ⟨15305325627828477636120053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203550418552318424080035 15305325627828477636120053)
                  ·
                    refine ⟨1434874277608919778386255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15305325627828477636120053 1434874277608919778386255)
                    ·
                      rfl

theorem cell23_8383223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 5].length) (baseStart_8383223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383223 prefixEnd_8383223 := by exact prefixLift 8383223
  have htrace : WordTrace (prefixWord ++ tailWord_8383223) baseStart_8383223 baseEnd_8383223 := by
    simpa [prefixWord, tailWord_8383223, baseEnd_8383223] using wordTrace_append hprefix tailTrace_8383223
  have hstable : (prefixWord ++ tailWord_8383223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383223).length < 2 ^ (prefixWord ++ tailWord_8383223).sum := by decide
  have hdescent : baseEnd_8383223 < baseStart_8383223 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383240 : List Nat := [2, 1, 3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_8383240 : Nat := 118140960795 + 8383240 * 2 ^ 59
def prefixEnd_8383240 : Nat := 4983230072969 + 3 ^ 40 * 8383240 * 2
def baseEnd_8383240 : Nat := 1434877187332628589548729

theorem tailTrace_8383240 : CollatzResearch.WordTrace tailWord_8383240 prefixEnd_8383240 1434877187332628589548729 := by
  unfold tailWord_8383240
  simp only [CollatzResearch.WordTrace]
  refine ⟨152880941074480349125097587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203841254765973798833463449 152880941074480349125097587)
  ·
    refine ⟨229321411611720523687646381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152880941074480349125097587 229321411611720523687646381)
    ·
      refine ⟨85995529354395196382867393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229321411611720523687646381 85995529354395196382867393)
      ·
        refine ⟨64496647015796397287150545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85995529354395196382867393 64496647015796397287150545)
        ·
          refine ⟨48372485261847297965362909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64496647015796397287150545 48372485261847297965362909)
          ·
            refine ⟨18139681973192736737011091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48372485261847297965362909 18139681973192736737011091)
            ·
              refine ⟨27209522959789105105516637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18139681973192736737011091 27209522959789105105516637)
              ·
                refine ⟨10203571109920914414568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27209522959789105105516637 10203571109920914414568739)
                ·
                  refine ⟨15305356664881371621853109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203571109920914414568739 15305356664881371621853109)
                  ·
                    refine ⟨1434877187332628589548729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15305356664881371621853109 1434877187332628589548729)
                    ·
                      rfl

theorem cell23_8383240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_8383240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383240 prefixEnd_8383240 := by exact prefixLift 8383240
  have htrace : WordTrace (prefixWord ++ tailWord_8383240) baseStart_8383240 baseEnd_8383240 := by
    simpa [prefixWord, tailWord_8383240, baseEnd_8383240] using wordTrace_append hprefix tailTrace_8383240
  have hstable : (prefixWord ++ tailWord_8383240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383240).length < 2 ^ (prefixWord ++ tailWord_8383240).sum := by decide
  have hdescent : baseEnd_8383240 < baseStart_8383240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383263 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5]
def baseStart_8383263 : Nat := 118140960795 + 8383263 * 2 ^ 59
def prefixEnd_8383263 : Nat := 4983230072969 + 3 ^ 40 * 8383263 * 2
def baseEnd_8383263 : Nat := 4304643372052939178658581

theorem tailTrace_8383263 : CollatzResearch.WordTrace tailWord_8383263 prefixEnd_8383263 4304643372052939178658581 := by
  unfold tailWord_8383263
  simp only [CollatzResearch.WordTrace]
  refine ⟨305762721027877373178282443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203841814018584915452188295 305762721027877373178282443)
  ·
    refine ⟨458644081541816059767423665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305762721027877373178282443 458644081541816059767423665)
    ·
      refine ⟨343983061156362044825567749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458644081541816059767423665 343983061156362044825567749)
      ·
        refine ⟨64496823966817883404793953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343983061156362044825567749 64496823966817883404793953)
        ·
          refine ⟨48372617975113412553595465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64496823966817883404793953 48372617975113412553595465)
          ·
            refine ⟨36279463481335059415196599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48372617975113412553595465 36279463481335059415196599)
            ·
              refine ⟨54419195222002589122794899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36279463481335059415196599 54419195222002589122794899)
              ·
                refine ⟨81628792833003883684192349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54419195222002589122794899 81628792833003883684192349)
                ·
                  refine ⟨30610797312376456381572131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81628792833003883684192349 30610797312376456381572131)
                  ·
                    refine ⟨45916195968564684572358197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30610797312376456381572131 45916195968564684572358197)
                    ·
                      refine ⟨4304643372052939178658581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45916195968564684572358197 4304643372052939178658581)
                      ·
                        rfl

theorem cell23_8383263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_8383263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383263 prefixEnd_8383263 := by exact prefixLift 8383263
  have htrace : WordTrace (prefixWord ++ tailWord_8383263) baseStart_8383263 baseEnd_8383263 := by
    simpa [prefixWord, tailWord_8383263, baseEnd_8383263] using wordTrace_append hprefix tailTrace_8383263
  have hstable : (prefixWord ++ tailWord_8383263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383263).length < 2 ^ (prefixWord ++ tailWord_8383263).sum := by decide
  have hdescent : baseEnd_8383263 < baseStart_8383263 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383274 : List Nat := [3, 1, 4, 3, 1, 1, 2, 2, 1, 5]
def baseStart_8383274 : Nat := 118140960795 + 8383274 * 2 ^ 59
def prefixEnd_8383274 : Nat := 4983230072969 + 3 ^ 40 * 8383274 * 2
def baseEnd_8383274 : Nat := 1434883006780046211873677

theorem tailTrace_8383274 : CollatzResearch.WordTrace tailWord_8383274 prefixEnd_8383274 1434883006780046211873677 := by
  unfold tailWord_8383274
  simp only [CollatzResearch.WordTrace]
  refine ⟨76440780557709380514233219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203842081487225014704621917 76440780557709380514233219)
  ·
    refine ⟨114661170836564070771349829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76440780557709380514233219 114661170836564070771349829)
    ·
      refine ⟨21498969531855763269628093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114661170836564070771349829 21498969531855763269628093)
      ·
        refine ⟨8062113574445911226110535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21498969531855763269628093 8062113574445911226110535)
        ·
          refine ⟨12093170361668866839165803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062113574445911226110535 12093170361668866839165803)
          ·
            refine ⟨18139755542503300258748705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12093170361668866839165803 18139755542503300258748705)
            ·
              refine ⟨13604816656877475194061529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18139755542503300258748705 13604816656877475194061529)
              ·
                refine ⟨10203612492658106395546147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13604816656877475194061529 10203612492658106395546147)
                ·
                  refine ⟨15305418738987159593319221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203612492658106395546147 15305418738987159593319221)
                  ·
                    refine ⟨1434883006780046211873677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15305418738987159593319221 1434883006780046211873677)
                    ·
                      rfl

theorem cell23_8383274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_8383274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383274 prefixEnd_8383274 := by exact prefixLift 8383274
  have htrace : WordTrace (prefixWord ++ tailWord_8383274) baseStart_8383274 baseEnd_8383274 := by
    simpa [prefixWord, tailWord_8383274, baseEnd_8383274] using wordTrace_append hprefix tailTrace_8383274
  have hstable : (prefixWord ++ tailWord_8383274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383274).length < 2 ^ (prefixWord ++ tailWord_8383274).sum := by decide
  have hdescent : baseEnd_8383274 < baseStart_8383274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383283 : List Nat := [1, 1, 1, 2, 6, 2, 1, 9]
def baseStart_8383283 : Nat := 118140960795 + 8383283 * 2 ^ 59
def prefixEnd_8383283 : Nat := 4983230072969 + 3 ^ 40 * 8383283 * 2
def baseEnd_8383283 : Nat := 159431616358001077792907

theorem tailTrace_8383283 : CollatzResearch.WordTrace tailWord_8383283 prefixEnd_8383283 159431616358001077792907 := by
  unfold tailWord_8383283
  simp only [CollatzResearch.WordTrace]
  refine ⟨305763450487804916594010503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203842300325203277729340335 305763450487804916594010503)
  ·
    refine ⟨458645175731707374891015755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305763450487804916594010503 458645175731707374891015755)
    ·
      refine ⟨687967763597561062336523633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458645175731707374891015755 687967763597561062336523633)
      ·
        refine ⟨515975822698170796752392725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687967763597561062336523633 515975822698170796752392725)
        ·
          refine ⟨24186366688976756097768409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 515975822698170796752392725 24186366688976756097768409)
          ·
            refine ⟨18139775016732567073326307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24186366688976756097768409 18139775016732567073326307)
            ·
              refine ⟨27209662525098850609989461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18139775016732567073326307 27209662525098850609989461)
              ·
                refine ⟨159431616358001077792907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27209662525098850609989461 159431616358001077792907)
                ·
                  rfl

theorem cell23_8383283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 9].length) (baseStart_8383283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383283 prefixEnd_8383283 := by exact prefixLift 8383283
  have htrace : WordTrace (prefixWord ++ tailWord_8383283) baseStart_8383283 baseEnd_8383283 := by
    simpa [prefixWord, tailWord_8383283, baseEnd_8383283] using wordTrace_append hprefix tailTrace_8383283
  have hstable : (prefixWord ++ tailWord_8383283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383283).length < 2 ^ (prefixWord ++ tailWord_8383283).sum := by decide
  have hdescent : baseEnd_8383283 < baseStart_8383283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383327 : List Nat := [1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 3]
def baseStart_8383327 : Nat := 118140960795 + 8383327 * 2 ^ 59
def prefixEnd_8383327 : Nat := 4983230072969 + 3 ^ 40 * 8383327 * 2
def baseEnd_8383327 : Nat := 4304676234814826928258287

theorem tailTrace_8383327 : CollatzResearch.WordTrace tailWord_8383327 prefixEnd_8383327 4304676234814826928258287 := by
  unfold tailWord_8383327
  simp only [CollatzResearch.WordTrace]
  refine ⟨305765055299645512108612235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203843370199763674739074823 305765055299645512108612235)
  ·
    refine ⟨458647582949468268162918353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305765055299645512108612235 458647582949468268162918353)
    ·
      refine ⟨343985687212101201122188765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458647582949468268162918353 343985687212101201122188765)
      ·
        refine ⟨128994632704537950420820787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343985687212101201122188765 128994632704537950420820787)
        ·
          refine ⟨193491949056806925631231181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128994632704537950420820787 193491949056806925631231181)
          ·
            refine ⟨72559480896302597111711693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193491949056806925631231181 72559480896302597111711693)
            ·
              refine ⟨27209805336113473916891885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72559480896302597111711693 27209805336113473916891885)
              ·
                refine ⟨10203677001042552718834457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27209805336113473916891885 10203677001042552718834457)
                ·
                  refine ⟨7652757750781914539125843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10203677001042552718834457 7652757750781914539125843)
                  ·
                    refine ⟨11479136626172871808688765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652757750781914539125843 11479136626172871808688765)
                    ·
                      refine ⟨4304676234814826928258287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11479136626172871808688765 4304676234814826928258287)
                      ·
                        rfl

theorem cell23_8383327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_8383327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383327 prefixEnd_8383327 := by exact prefixLift 8383327
  have htrace : WordTrace (prefixWord ++ tailWord_8383327) baseStart_8383327 baseEnd_8383327 := by
    simpa [prefixWord, tailWord_8383327, baseEnd_8383327] using wordTrace_append hprefix tailTrace_8383327
  have hstable : (prefixWord ++ tailWord_8383327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383327).length < 2 ^ (prefixWord ++ tailWord_8383327).sum := by decide
  have hdescent : baseEnd_8383327 < baseStart_8383327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383403 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 1, 7]
def baseStart_8383403 : Nat := 118140960795 + 8383403 * 2 ^ 59
def prefixEnd_8383403 : Nat := 4983230072969 + 3 ^ 40 * 8383403 * 2
def baseEnd_8383403 : Nat := 1434905086448189543635979

theorem tailTrace_8383403 : CollatzResearch.WordTrace tailWord_8383403 prefixEnd_8383403 1434905086448189543635979 := by
  unfold tailWord_8383403
  simp only [CollatzResearch.WordTrace]
  refine ⟨305767827247370177088378863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203845218164913451392252575 305767827247370177088378863)
  ·
    refine ⟨458651740871055265632568295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305767827247370177088378863 458651740871055265632568295)
    ·
      refine ⟨687977611306582898448852443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458651740871055265632568295 687977611306582898448852443)
      ·
        refine ⟨1031966416959874347673278665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687977611306582898448852443 1031966416959874347673278665)
        ·
          refine ⟨773974812719905760754958999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031966416959874347673278665 773974812719905760754958999)
          ·
            refine ⟨1160962219079858641132438499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773974812719905760754958999 1160962219079858641132438499)
            ·
              refine ⟨1741443328619787961698657749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1160962219079858641132438499 1741443328619787961698657749)
              ·
                refine ⟨40815078014526280352312291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1741443328619787961698657749 40815078014526280352312291)
                ·
                  refine ⟨61222617021789420528468437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40815078014526280352312291 61222617021789420528468437)
                  ·
                    refine ⟨1434905086448189543635979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61222617021789420528468437 1434905086448189543635979)
                    ·
                      rfl

theorem cell23_8383403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 7].length) (baseStart_8383403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383403 prefixEnd_8383403 := by exact prefixLift 8383403
  have htrace : WordTrace (prefixWord ++ tailWord_8383403) baseStart_8383403 baseEnd_8383403 := by
    simpa [prefixWord, tailWord_8383403, baseEnd_8383403] using wordTrace_append hprefix tailTrace_8383403
  have hstable : (prefixWord ++ tailWord_8383403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383403).length < 2 ^ (prefixWord ++ tailWord_8383403).sum := by decide
  have hdescent : baseEnd_8383403 < baseStart_8383403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383405 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_8383405 : Nat := 118140960795 + 8383405 * 2 ^ 59
def prefixEnd_8383405 : Nat := 4983230072969 + 3 ^ 40 * 8383405 * 2
def baseEnd_8383405 : Nat := 4304716286305877623082929

theorem tailTrace_8383405 : CollatzResearch.WordTrace tailWord_8383405 prefixEnd_8383405 4304716286305877623082929 := by
  unfold tailWord_8383405
  simp only [CollatzResearch.WordTrace]
  refine ⟨305767900193362931429951669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203845266795575287619967779 305767900193362931429951669)
  ·
    refine ⟨28665740643127774821557969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305767900193362931429951669 28665740643127774821557969)
    ·
      refine ⟨21499305482345831116168477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28665740643127774821557969 21499305482345831116168477)
      ·
        refine ⟨8062239555879686668563179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21499305482345831116168477 8062239555879686668563179)
        ·
          refine ⟨12093359333819530002844769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062239555879686668563179 12093359333819530002844769)
          ·
            refine ⟨9070019500364647502133577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12093359333819530002844769 9070019500364647502133577)
            ·
              refine ⟨6802514625273485626600183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070019500364647502133577 6802514625273485626600183)
              ·
                refine ⟨10203771937910228439900275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802514625273485626600183 10203771937910228439900275)
                ·
                  refine ⟨15305657906865342659850413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203771937910228439900275 15305657906865342659850413)
                  ·
                    refine ⟨5739621715074503497443905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15305657906865342659850413 5739621715074503497443905)
                    ·
                      refine ⟨4304716286305877623082929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739621715074503497443905 4304716286305877623082929)
                      ·
                        rfl

theorem cell23_8383405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_8383405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383405 prefixEnd_8383405 := by exact prefixLift 8383405
  have htrace : WordTrace (prefixWord ++ tailWord_8383405) baseStart_8383405 baseEnd_8383405 := by
    simpa [prefixWord, tailWord_8383405, baseEnd_8383405] using wordTrace_append hprefix tailTrace_8383405
  have hstable : (prefixWord ++ tailWord_8383405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383405).length < 2 ^ (prefixWord ++ tailWord_8383405).sum := by decide
  have hdescent : baseEnd_8383405 < baseStart_8383405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383433 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_8383433 : Nat := 118140960795 + 8383433 * 2 ^ 59
def prefixEnd_8383433 : Nat := 4983230072969 + 3 ^ 40 * 8383433 * 2
def baseEnd_8383433 : Nat := 1434910221254734504510933

theorem tailTrace_8383433 : CollatzResearch.WordTrace tailWord_8383433 prefixEnd_8383433 1434910221254734504510933 := by
  unfold tailWord_8383433
  simp only [CollatzResearch.WordTrace]
  refine ⟨305768921437261492211970953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203845947624840994807980635 305768921437261492211970953)
  ·
    refine ⟨229326691077946119158978215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305768921437261492211970953 229326691077946119158978215)
    ·
      refine ⟨343990036616919178738467323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229326691077946119158978215 343990036616919178738467323)
      ·
        refine ⟨515985054925378768107700985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343990036616919178738467323 515985054925378768107700985)
        ·
          refine ⟨386988791194034076080775739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515985054925378768107700985 386988791194034076080775739)
          ·
            refine ⟨580483186791051114121163609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386988791194034076080775739 580483186791051114121163609)
            ·
              refine ⟨435362390093288335590872707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580483186791051114121163609 435362390093288335590872707)
              ·
                refine ⟨653043585139932503386309061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435362390093288335590872707 653043585139932503386309061)
                ·
                  refine ⟨122445672213737344384932949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653043585139932503386309061 122445672213737344384932949)
                  ·
                    refine ⟨1434910221254734504510933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122445672213737344384932949 1434910221254734504510933)
                    ·
                      rfl

theorem cell23_8383433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_8383433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383433 prefixEnd_8383433 := by exact prefixLift 8383433
  have htrace : WordTrace (prefixWord ++ tailWord_8383433) baseStart_8383433 baseEnd_8383433 := by
    simpa [prefixWord, tailWord_8383433, baseEnd_8383433] using wordTrace_append hprefix tailTrace_8383433
  have hstable : (prefixWord ++ tailWord_8383433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383433).length < 2 ^ (prefixWord ++ tailWord_8383433).sum := by decide
  have hdescent : baseEnd_8383433 < baseStart_8383433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383480 : List Nat := [2, 1, 2, 1, 1, 3, 1, 6, 6]
def baseStart_8383480 : Nat := 118140960795 + 8383480 * 2 ^ 59
def prefixEnd_8383480 : Nat := 4983230072969 + 3 ^ 40 * 8383480 * 2
def baseEnd_8383480 : Nat := 478306088594996092182787

theorem tailTrace_8383480 : CollatzResearch.WordTrace tailWord_8383480 prefixEnd_8383480 478306088594996092182787 := by
  unfold tailWord_8383480
  simp only [CollatzResearch.WordTrace]
  refine ⟨152885317834045609619465947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203847090445394146159287929 152885317834045609619465947)
  ·
    refine ⟨229327976751068414429198921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152885317834045609619465947 229327976751068414429198921)
    ·
      refine ⟨171995982563301310821899191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229327976751068414429198921 171995982563301310821899191)
      ·
        refine ⟨257993973844951966232848787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171995982563301310821899191 257993973844951966232848787)
        ·
          refine ⟨386990960767427949349273181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257993973844951966232848787 386990960767427949349273181)
          ·
            refine ⟨145121610287785481005977443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 386990960767427949349273181 145121610287785481005977443)
            ·
              refine ⟨217682415431678221508966165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145121610287785481005977443 217682415431678221508966165)
              ·
                refine ⟨10203863223359916633232789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 217682415431678221508966165 10203863223359916633232789)
                ·
                  refine ⟨478306088594996092182787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10203863223359916633232789 478306088594996092182787)
                  ·
                    rfl

theorem cell23_8383480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_8383480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383480 prefixEnd_8383480 := by exact prefixLift 8383480
  have htrace : WordTrace (prefixWord ++ tailWord_8383480) baseStart_8383480 baseEnd_8383480 := by
    simpa [prefixWord, tailWord_8383480, baseEnd_8383480] using wordTrace_append hprefix tailTrace_8383480
  have hstable : (prefixWord ++ tailWord_8383480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383480).length < 2 ^ (prefixWord ++ tailWord_8383480).sum := by decide
  have hdescent : baseEnd_8383480 < baseStart_8383480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383484 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 3, 4]
def baseStart_8383484 : Nat := 118140960795 + 8383484 * 2 ^ 59
def prefixEnd_8383484 : Nat := 4983230072969 + 3 ^ 40 * 8383484 * 2
def baseEnd_8383484 : Nat := 1434918950425860937998355

theorem tailTrace_8383484 : CollatzResearch.WordTrace tailWord_8383484 prefixEnd_8383484 1434918950425860937998355 := by
  unfold tailWord_8383484
  simp only [CollatzResearch.WordTrace]
  refine ⟨152885390780038363961038753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203847187706717818614718337 152885390780038363961038753)
  ·
    refine ⟨114664043085028772970779065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152885390780038363961038753 114664043085028772970779065)
    ·
      refine ⟨85998032313771579728084299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114664043085028772970779065 85998032313771579728084299)
      ·
        refine ⟨128997048470657369592126449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85998032313771579728084299 128997048470657369592126449)
        ·
          refine ⟨96747786352993027194094837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128997048470657369592126449 96747786352993027194094837)
          ·
            refine ⟨9070104970593096299446391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96747786352993027194094837 9070104970593096299446391)
            ·
              refine ⟨13605157455889644449169587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9070104970593096299446391 13605157455889644449169587)
              ·
                refine ⟨20407736183834466673754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13605157455889644449169587 20407736183834466673754381)
                ·
                  refine ⟨7652901068937925002657893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20407736183834466673754381 7652901068937925002657893)
                  ·
                    refine ⟨1434918950425860937998355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7652901068937925002657893 1434918950425860937998355)
                    ·
                      rfl

theorem cell23_8383484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_8383484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383484 prefixEnd_8383484 := by exact prefixLift 8383484
  have htrace : WordTrace (prefixWord ++ tailWord_8383484) baseStart_8383484 baseEnd_8383484 := by
    simpa [prefixWord, tailWord_8383484, baseEnd_8383484] using wordTrace_append hprefix tailTrace_8383484
  have hstable : (prefixWord ++ tailWord_8383484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383484).length < 2 ^ (prefixWord ++ tailWord_8383484).sum := by decide
  have hdescent : baseEnd_8383484 < baseStart_8383484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383507 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 3]
def baseStart_8383507 : Nat := 118140960795 + 8383507 * 2 ^ 59
def prefixEnd_8383507 : Nat := 4983230072969 + 3 ^ 40 * 8383507 * 2
def baseEnd_8383507 : Nat := 4304768661332636224007459

theorem tailTrace_8383507 : CollatzResearch.WordTrace tailWord_8383507 prefixEnd_8383507 4304768661332636224007459 := by
  unfold tailWord_8383507
  simp only [CollatzResearch.WordTrace]
  refine ⟨305771620438993402850164775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203847746959328935233443183 305771620438993402850164775)
  ·
    refine ⟨458657430658490104275247163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305771620438993402850164775 458657430658490104275247163)
    ·
      refine ⟨687986145987735156412870745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458657430658490104275247163 687986145987735156412870745)
      ·
        refine ⟨515989609490801367309653059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687986145987735156412870745 515989609490801367309653059)
        ·
          refine ⟨773984414236202050964479589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515989609490801367309653059 773984414236202050964479589)
          ·
            refine ⟨145122077669287884555839923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 773984414236202050964479589 145122077669287884555839923)
            ·
              refine ⟨217683116503931826833759885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145122077669287884555839923 217683116503931826833759885)
              ·
                refine ⟨81631168688974435062659957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217683116503931826833759885 81631168688974435062659957)
                ·
                  refine ⟨7652922064591353287124371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81631168688974435062659957 7652922064591353287124371)
                  ·
                    refine ⟨11479383096887029930686557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652922064591353287124371 11479383096887029930686557)
                    ·
                      refine ⟨4304768661332636224007459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11479383096887029930686557 4304768661332636224007459)
                      ·
                        rfl

theorem cell23_8383507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_8383507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383507 prefixEnd_8383507 := by exact prefixLift 8383507
  have htrace : WordTrace (prefixWord ++ tailWord_8383507) baseStart_8383507 baseEnd_8383507 := by
    simpa [prefixWord, tailWord_8383507, baseEnd_8383507] using wordTrace_append hprefix tailTrace_8383507
  have hstable : (prefixWord ++ tailWord_8383507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383507).length < 2 ^ (prefixWord ++ tailWord_8383507).sum := by decide
  have hdescent : baseEnd_8383507 < baseStart_8383507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383558 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_8383558 : Nat := 118140960795 + 8383558 * 2 ^ 59
def prefixEnd_8383558 : Nat := 4983230072969 + 3 ^ 40 * 8383558 * 2
def baseEnd_8383558 : Nat := 4304794848846015524469725

theorem tailTrace_8383558 : CollatzResearch.WordTrace tailWord_8383558 prefixEnd_8383558 4304794848846015524469725 := by
  unfold tailWord_8383558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555421267556519955008479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203848987041205759040180885 9555421267556519955008479)
  ·
    refine ⟨14333131901334779932512719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9555421267556519955008479 14333131901334779932512719)
    ·
      refine ⟨21499697852002169898769079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333131901334779932512719 21499697852002169898769079)
      ·
        refine ⟨32249546778003254848153619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21499697852002169898769079 32249546778003254848153619)
        ·
          refine ⟨48374320167004882272230429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32249546778003254848153619 48374320167004882272230429)
          ·
            refine ⟨18140370062626830852086411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48374320167004882272230429 18140370062626830852086411)
            ·
              refine ⟨27210555093940246278129617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18140370062626830852086411 27210555093940246278129617)
              ·
                refine ⟨20407916320455184708597213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27210555093940246278129617 20407916320455184708597213)
                ·
                  refine ⟨7652968620170694265723955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20407916320455184708597213 7652968620170694265723955)
                  ·
                    refine ⟨11479452930256041398585933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652968620170694265723955 11479452930256041398585933)
                    ·
                      refine ⟨4304794848846015524469725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11479452930256041398585933 4304794848846015524469725)
                      ·
                        rfl

theorem cell23_8383558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_8383558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383558 prefixEnd_8383558 := by exact prefixLift 8383558
  have htrace : WordTrace (prefixWord ++ tailWord_8383558) baseStart_8383558 baseEnd_8383558 := by
    simpa [prefixWord, tailWord_8383558, baseEnd_8383558] using wordTrace_append hprefix tailTrace_8383558
  have hstable : (prefixWord ++ tailWord_8383558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383558).length < 2 ^ (prefixWord ++ tailWord_8383558).sum := by decide
  have hdescent : baseEnd_8383558 < baseStart_8383558 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383584 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_8383584 : Nat := 118140960795 + 8383584 * 2 ^ 59
def prefixEnd_8383584 : Nat := 4983230072969 + 3 ^ 40 * 8383584 * 2
def baseEnd_8383584 : Nat := 4304808199343032422744605

theorem tailTrace_8383584 : CollatzResearch.WordTrace tailWord_8383584 prefixEnd_8383584 4304808199343032422744605 := by
  unfold tailWord_8383584
  simp only [CollatzResearch.WordTrace]
  refine ⟨152887214429857222500358903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203849619239809630000478537 152887214429857222500358903)
  ·
    refine ⟨229330821644785833750538355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152887214429857222500358903 229330821644785833750538355)
    ·
      refine ⟨343996232467178750625807533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229330821644785833750538355 343996232467178750625807533)
      ·
        refine ⟨128998587175192031484677825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343996232467178750625807533 128998587175192031484677825)
        ·
          refine ⟨96748940381394023613508369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 128998587175192031484677825 96748940381394023613508369)
          ·
            refine ⟨72561705286045517710131277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96748940381394023613508369 72561705286045517710131277)
            ·
              refine ⟨27210639482267069141299229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72561705286045517710131277 27210639482267069141299229)
              ·
                refine ⟨10203989805850150927987211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27210639482267069141299229 10203989805850150927987211)
                ·
                  refine ⟨15305984708775226391980817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203989805850150927987211 15305984708775226391980817)
                  ·
                    refine ⟨11479488531581419793985613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15305984708775226391980817 11479488531581419793985613)
                    ·
                      refine ⟨4304808199343032422744605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11479488531581419793985613 4304808199343032422744605)
                      ·
                        rfl

theorem cell23_8383584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_8383584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383584 prefixEnd_8383584 := by exact prefixLift 8383584
  have htrace : WordTrace (prefixWord ++ tailWord_8383584) baseStart_8383584 baseEnd_8383584 := by
    simpa [prefixWord, tailWord_8383584, baseEnd_8383584] using wordTrace_append hprefix tailTrace_8383584
  have hstable : (prefixWord ++ tailWord_8383584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383584).length < 2 ^ (prefixWord ++ tailWord_8383584).sum := by decide
  have hdescent : baseEnd_8383584 < baseStart_8383584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383591 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 2, 4]
def baseStart_8383591 : Nat := 118140960795 + 8383591 * 2 ^ 59
def prefixEnd_8383591 : Nat := 4983230072969 + 3 ^ 40 * 8383591 * 2
def baseEnd_8383591 : Nat := 1434937264569204631785691

theorem tailTrace_8383591 : CollatzResearch.WordTrace tailWord_8383591 prefixEnd_8383591 1434937264569204631785691 := by
  unfold tailWord_8383591
  simp only [CollatzResearch.WordTrace]
  refine ⟨305774684170689085196222627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203849789447126056797481751 305774684170689085196222627)
  ·
    refine ⟨458662026256033627794333941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305774684170689085196222627 458662026256033627794333941)
    ·
      refine ⟨42999564961503152605718807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458662026256033627794333941 42999564961503152605718807)
      ·
        refine ⟨64499347442254728908578211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42999564961503152605718807 64499347442254728908578211)
        ·
          refine ⟨96749021163382093362867317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64499347442254728908578211 96749021163382093362867317)
          ·
            refine ⟨9070220734067071252768811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96749021163382093362867317 9070220734067071252768811)
            ·
              refine ⟨13605331101100606879153217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9070220734067071252768811 13605331101100606879153217)
              ·
                refine ⟨10203998325825455159364913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13605331101100606879153217 10203998325825455159364913)
                ·
                  refine ⟨7652998744369091369523685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10203998325825455159364913 7652998744369091369523685)
                  ·
                    refine ⟨1434937264569204631785691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7652998744369091369523685 1434937264569204631785691)
                    ·
                      rfl

theorem cell23_8383591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_8383591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383591 prefixEnd_8383591 := by exact prefixLift 8383591
  have htrace : WordTrace (prefixWord ++ tailWord_8383591) baseStart_8383591 baseEnd_8383591 := by
    simpa [prefixWord, tailWord_8383591, baseEnd_8383591] using wordTrace_append hprefix tailTrace_8383591
  have hstable : (prefixWord ++ tailWord_8383591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383591).length < 2 ^ (prefixWord ++ tailWord_8383591).sum := by decide
  have hdescent : baseEnd_8383591 < baseStart_8383591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383598 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_8383598 : Nat := 118140960795 + 8383598 * 2 ^ 59
def prefixEnd_8383598 : Nat := 4983230072969 + 3 ^ 40 * 8383598 * 2
def baseEnd_8383598 : Nat := 4304815388072195367969541

theorem tailTrace_8383598 : CollatzResearch.WordTrace tailWord_8383598 prefixEnd_8383598 4304815388072195367969541 := by
  unfold tailWord_8383598
  simp only [CollatzResearch.WordTrace]
  refine ⟨38221867435207965673965931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203849959654442483594484965 38221867435207965673965931)
  ·
    refine ⟨57332801152811948510948897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38221867435207965673965931 57332801152811948510948897)
    ·
      refine ⟨42999600864608961383211673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57332801152811948510948897 42999600864608961383211673)
      ·
        refine ⟨32249700648456721037408755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42999600864608961383211673 32249700648456721037408755)
        ·
          refine ⟨48374550972685081556113133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32249700648456721037408755 48374550972685081556113133)
          ·
            refine ⟨18140456614756905583542425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48374550972685081556113133 18140456614756905583542425)
            ·
              refine ⟨13605342461067679187656819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18140456614756905583542425 13605342461067679187656819)
              ·
                refine ⟨20408013691601518781485229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13605342461067679187656819 20408013691601518781485229)
                ·
                  refine ⟨7653005134350569543056961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20408013691601518781485229 7653005134350569543056961)
                  ·
                    refine ⟨5739753850762927157292721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653005134350569543056961 5739753850762927157292721)
                    ·
                      refine ⟨4304815388072195367969541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739753850762927157292721 4304815388072195367969541)
                      ·
                        rfl

theorem cell23_8383598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_8383598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383598 prefixEnd_8383598 := by exact prefixLift 8383598
  have htrace : WordTrace (prefixWord ++ tailWord_8383598) baseStart_8383598 baseEnd_8383598 := by
    simpa [prefixWord, tailWord_8383598, baseEnd_8383598] using wordTrace_append hprefix tailTrace_8383598
  have hstable : (prefixWord ++ tailWord_8383598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383598).length < 2 ^ (prefixWord ++ tailWord_8383598).sum := by decide
  have hdescent : baseEnd_8383598 < baseStart_8383598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383621 : List Nat := [1, 3, 1, 1, 7, 1, 2, 7]
def baseStart_8383621 : Nat := 118140960795 + 8383621 * 2 ^ 59
def prefixEnd_8383621 : Nat := 4983230072969 + 3 ^ 40 * 8383621 * 2
def baseEnd_8383621 : Nat := 159438044375083288073405

theorem tailTrace_8383621 : CollatzResearch.WordTrace tailWord_8383621 prefixEnd_8383621 159438044375083288073405 := by
  unfold tailWord_8383621
  simp only [CollatzResearch.WordTrace]
  refine ⟨305775778360580400319814717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203850518907053600213209811 305775778360580400319814717)
  ·
    refine ⟨114665916885217650119930519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305775778360580400319814717 114665916885217650119930519)
    ·
      refine ⟨171998875327826475179895779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114665916885217650119930519 171998875327826475179895779)
      ·
        refine ⟨257998312991739712769843669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171998875327826475179895779 257998312991739712769843669)
        ·
          refine ⟨6046835460743899518043211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 257998312991739712769843669 6046835460743899518043211)
          ·
            refine ⟨9070253191115849277064817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046835460743899518043211 9070253191115849277064817)
            ·
              refine ⟨6802689893336886957798613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070253191115849277064817 6802689893336886957798613)
              ·
                refine ⟨159438044375083288073405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6802689893336886957798613 159438044375083288073405)
                ·
                  rfl

theorem cell23_8383621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 7].length) (baseStart_8383621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383621 prefixEnd_8383621 := by exact prefixLift 8383621
  have htrace : WordTrace (prefixWord ++ tailWord_8383621) baseStart_8383621 baseEnd_8383621 := by
    simpa [prefixWord, tailWord_8383621, baseEnd_8383621] using wordTrace_append hprefix tailTrace_8383621
  have hstable : (prefixWord ++ tailWord_8383621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383621).length < 2 ^ (prefixWord ++ tailWord_8383621).sum := by decide
  have hdescent : baseEnd_8383621 < baseStart_8383621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383665 : List Nat := [1, 2, 2, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_8383665 : Nat := 118140960795 + 8383665 * 2 ^ 59
def prefixEnd_8383665 : Nat := 4983230072969 + 3 ^ 40 * 8383665 * 2
def baseEnd_8383665 : Nat := 4304849791276046605831733

theorem tailTrace_8383665 : CollatzResearch.WordTrace tailWord_8383665 prefixEnd_8383665 4304849791276046605831733 := by
  unfold tailWord_8383665
  simp only [CollatzResearch.WordTrace]
  refine ⟨305777383172420995834416449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203851588781613997222944299 305777383172420995834416449)
  ·
    refine ⟨229333037379315746875812337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305777383172420995834416449 229333037379315746875812337)
    ·
      refine ⟨171999778034486810156859253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229333037379315746875812337 171999778034486810156859253)
      ·
        refine ⟨16124979190733138452205555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 171999778034486810156859253 16124979190733138452205555)
        ·
          refine ⟨24187468786099707678308333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124979190733138452205555 24187468786099707678308333)
          ·
            refine ⟨9070300794787390379365625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24187468786099707678308333 9070300794787390379365625)
            ·
              refine ⟨6802725596090542784524219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070300794787390379365625 6802725596090542784524219)
              ·
                refine ⟨10204088394135814176786329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802725596090542784524219 10204088394135814176786329)
                ·
                  refine ⟨7653066295601860632589747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10204088394135814176786329 7653066295601860632589747)
                  ·
                    refine ⟨11479599443402790948884621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7653066295601860632589747 11479599443402790948884621)
                    ·
                      refine ⟨4304849791276046605831733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11479599443402790948884621 4304849791276046605831733)
                      ·
                        rfl

theorem cell23_8383665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_8383665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383665 prefixEnd_8383665 := by exact prefixLift 8383665
  have htrace : WordTrace (prefixWord ++ tailWord_8383665) baseStart_8383665 baseEnd_8383665 := by
    simpa [prefixWord, tailWord_8383665, baseEnd_8383665] using wordTrace_append hprefix tailTrace_8383665
  have hstable : (prefixWord ++ tailWord_8383665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383665).length < 2 ^ (prefixWord ++ tailWord_8383665).sum := by decide
  have hdescent : baseEnd_8383665 < baseStart_8383665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383667 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4]
def baseStart_8383667 : Nat := 118140960795 + 8383667 * 2 ^ 59
def prefixEnd_8383667 : Nat := 4983230072969 + 3 ^ 40 * 8383667 * 2
def baseEnd_8383667 : Nat := 4304850818237355598006723

theorem tailTrace_8383667 : CollatzResearch.WordTrace tailWord_8383667 prefixEnd_8383667 4304850818237355598006723 := by
  unfold tailWord_8383667
  simp only [CollatzResearch.WordTrace]
  refine ⟨305777456118413750175989255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203851637412275833450659503 305777456118413750175989255)
  ·
    refine ⟨458666184177620625263983883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305777456118413750175989255 458666184177620625263983883)
    ·
      refine ⟨687999276266430937895975825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458666184177620625263983883 687999276266430937895975825)
      ·
        refine ⟨515999457199823203421981869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687999276266430937895975825 515999457199823203421981869)
        ·
          refine ⟨193499796449933701283243201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515999457199823203421981869 193499796449933701283243201)
          ·
            refine ⟨145124847337450275962432401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193499796449933701283243201 145124847337450275962432401)
            ·
              refine ⟨108843635503087706971824301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145124847337450275962432401 108843635503087706971824301)
              ·
                refine ⟨40816363313657890114434113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108843635503087706971824301 40816363313657890114434113)
                ·
                  refine ⟨30612272485243417585825585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40816363313657890114434113 30612272485243417585825585)
                  ·
                    refine ⟨22959204363932563189369189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30612272485243417585825585 22959204363932563189369189)
                    ·
                      refine ⟨4304850818237355598006723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22959204363932563189369189 4304850818237355598006723)
                      ·
                        rfl

theorem cell23_8383667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_8383667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383667 prefixEnd_8383667 := by exact prefixLift 8383667
  have htrace : WordTrace (prefixWord ++ tailWord_8383667) baseStart_8383667 baseEnd_8383667 := by
    simpa [prefixWord, tailWord_8383667, baseEnd_8383667] using wordTrace_append hprefix tailTrace_8383667
  have hstable : (prefixWord ++ tailWord_8383667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383667).length < 2 ^ (prefixWord ++ tailWord_8383667).sum := by decide
  have hdescent : baseEnd_8383667 < baseStart_8383667 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383677 : List Nat := [1, 4, 1, 2, 1, 1, 2, 4, 7]
def baseStart_8383677 : Nat := 118140960795 + 8383677 * 2 ^ 59
def prefixEnd_8383677 : Nat := 4983230072969 + 3 ^ 40 * 8383677 * 2
def baseEnd_8383677 : Nat := 478317328115988950986853

theorem tailTrace_8383677 : CollatzResearch.WordTrace tailWord_8383677 prefixEnd_8383677 478317328115988950986853 := by
  unfold tailWord_8383677
  simp only [CollatzResearch.WordTrace]
  refine ⟨305777820848377521883853285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203851880565585014589235523 305777820848377521883853285)
  ·
    refine ⟨57333341409070785353222491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305777820848377521883853285 57333341409070785353222491)
    ·
      refine ⟨86000012113606178029833737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57333341409070785353222491 86000012113606178029833737)
      ·
        refine ⟨64500009085204633522375303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86000012113606178029833737 64500009085204633522375303)
        ·
          refine ⟨96750013627806950283562955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64500009085204633522375303 96750013627806950283562955)
          ·
            refine ⟨145125020441710425425344433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96750013627806950283562955 145125020441710425425344433)
            ·
              refine ⟨108843765331282819069008325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145125020441710425425344433 108843765331282819069008325)
              ·
                refine ⟨20408205999615528575439061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108843765331282819069008325 20408205999615528575439061)
                ·
                  refine ⟨478317328115988950986853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20408205999615528575439061 478317328115988950986853)
                  ·
                    rfl

theorem cell23_8383677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_8383677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383677 prefixEnd_8383677 := by exact prefixLift 8383677
  have htrace : WordTrace (prefixWord ++ tailWord_8383677) baseStart_8383677 baseEnd_8383677 := by
    simpa [prefixWord, tailWord_8383677, baseEnd_8383677] using wordTrace_append hprefix tailTrace_8383677
  have hstable : (prefixWord ++ tailWord_8383677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383677).length < 2 ^ (prefixWord ++ tailWord_8383677).sum := by decide
  have hdescent : baseEnd_8383677 < baseStart_8383677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383711 : List Nat := [1, 1, 2, 3, 2, 1, 6, 2, 5]
def baseStart_8383711 : Nat := 118140960795 + 8383711 * 2 ^ 59
def prefixEnd_8383711 : Nat := 4983230072969 + 3 ^ 40 * 8383711 * 2
def baseEnd_8383711 : Nat := 478319267931794825095169

theorem tailTrace_8383711 : CollatzResearch.WordTrace tailWord_8383711 prefixEnd_8383711 478319267931794825095169 := by
  unfold tailWord_8383711
  simp only [CollatzResearch.WordTrace]
  refine ⟨305779060930254345690590987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203852707286836230460393991 305779060930254345690590987)
  ·
    refine ⟨458668591395381518535886481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305779060930254345690590987 458668591395381518535886481)
    ·
      refine ⟨344001443546536138901914861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458668591395381518535886481 344001443546536138901914861)
      ·
        refine ⟨129000541329951052088218073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344001443546536138901914861 129000541329951052088218073)
        ·
          refine ⟨96750405997463289066163555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129000541329951052088218073 96750405997463289066163555)
          ·
            refine ⟨145125608996194933599245333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96750405997463289066163555 145125608996194933599245333)
            ·
              refine ⟨6802762921696637512464625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145125608996194933599245333 6802762921696637512464625)
              ·
                refine ⟨5102072191272478134348469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6802762921696637512464625 5102072191272478134348469)
                ·
                  refine ⟨478319267931794825095169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5102072191272478134348469 478319267931794825095169)
                  ·
                    rfl

theorem cell23_8383711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 2, 5].length) (baseStart_8383711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383711 prefixEnd_8383711 := by exact prefixLift 8383711
  have htrace : WordTrace (prefixWord ++ tailWord_8383711) baseStart_8383711 baseEnd_8383711 := by
    simpa [prefixWord, tailWord_8383711, baseEnd_8383711] using wordTrace_append hprefix tailTrace_8383711
  have hstable : (prefixWord ++ tailWord_8383711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383711).length < 2 ^ (prefixWord ++ tailWord_8383711).sum := by decide
  have hdescent : baseEnd_8383711 < baseStart_8383711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383744 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2]
def baseStart_8383744 : Nat := 118140960795 + 8383744 * 2 ^ 59
def prefixEnd_8383744 : Nat := 4983230072969 + 3 ^ 40 * 8383744 * 2
def baseEnd_8383744 : Nat := 4304890356247751796743869

theorem tailTrace_8383744 : CollatzResearch.WordTrace tailWord_8383744 prefixEnd_8383744 4304890356247751796743869 := by
  unfold tailWord_8383744
  simp only [CollatzResearch.WordTrace]
  refine ⟨152890132269567396163271143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203853509692756528217694857 152890132269567396163271143)
  ·
    refine ⟨229335198404351094244906715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152890132269567396163271143 229335198404351094244906715)
    ·
      refine ⟨344002797606526641367360073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229335198404351094244906715 344002797606526641367360073)
      ·
        refine ⟨258002098204894981025520055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344002797606526641367360073 258002098204894981025520055)
        ·
          refine ⟨387003147307342471538280083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258002098204894981025520055 387003147307342471538280083)
          ·
            refine ⟨580504720961013707307420125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387003147307342471538280083 580504720961013707307420125)
            ·
              refine ⟨217689270360380140240282547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580504720961013707307420125 217689270360380140240282547)
              ·
                refine ⟨326533905540570210360423821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217689270360380140240282547 326533905540570210360423821)
                ·
                  refine ⟨122450214577713828885158933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 326533905540570210360423821 122450214577713828885158933)
                  ·
                    refine ⟨5739853808330335728991825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122450214577713828885158933 5739853808330335728991825)
                    ·
                      refine ⟨4304890356247751796743869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739853808330335728991825 4304890356247751796743869)
                      ·
                        rfl

theorem cell23_8383744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_8383744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383744 prefixEnd_8383744 := by exact prefixLift 8383744
  have htrace : WordTrace (prefixWord ++ tailWord_8383744) baseStart_8383744 baseEnd_8383744 := by
    simpa [prefixWord, tailWord_8383744, baseEnd_8383744] using wordTrace_append hprefix tailTrace_8383744
  have hstable : (prefixWord ++ tailWord_8383744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383744).length < 2 ^ (prefixWord ++ tailWord_8383744).sum := by decide
  have hdescent : baseEnd_8383744 < baseStart_8383744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383754 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 7, 4]
def baseStart_8383754 : Nat := 118140960795 + 8383754 * 2 ^ 59
def prefixEnd_8383754 : Nat := 4983230072969 + 3 ^ 40 * 8383754 * 2
def baseEnd_8383754 : Nat := 1434965163684765585872941

theorem tailTrace_8383754 : CollatzResearch.WordTrace tailWord_8383754 prefixEnd_8383754 1434965163684765585872941 := by
  unfold tailWord_8383754
  simp only [CollatzResearch.WordTrace]
  refine ⟨76445157317274641008601579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203853752846065709356270877 76445157317274641008601579)
  ·
    refine ⟨114667735975911961512902369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76445157317274641008601579 114667735975911961512902369)
    ·
      refine ⟨86000801981933971134676777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114667735975911961512902369 86000801981933971134676777)
      ·
        refine ⟨64500601486450478351007583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86000801981933971134676777 64500601486450478351007583)
        ·
          refine ⟨96750902229675717526511375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64500601486450478351007583 96750902229675717526511375)
          ·
            refine ⟨145126353344513576289767063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96750902229675717526511375 145126353344513576289767063)
            ·
              refine ⟨217689530016770364434650595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145126353344513576289767063 217689530016770364434650595)
              ·
                refine ⟨326534295025155546651975893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217689530016770364434650595 326534295025155546651975893)
                ·
                  refine ⟨7653147539652083124655685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 326534295025155546651975893 7653147539652083124655685)
                  ·
                    refine ⟨1434965163684765585872941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653147539652083124655685 1434965163684765585872941)
                    ·
                      rfl

theorem cell23_8383754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_8383754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383754 prefixEnd_8383754 := by exact prefixLift 8383754
  have htrace : WordTrace (prefixWord ++ tailWord_8383754) baseStart_8383754 baseEnd_8383754 := by
    simpa [prefixWord, tailWord_8383754, baseEnd_8383754] using wordTrace_append hprefix tailTrace_8383754
  have hstable : (prefixWord ++ tailWord_8383754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383754).length < 2 ^ (prefixWord ++ tailWord_8383754).sum := by decide
  have hdescent : baseEnd_8383754 < baseStart_8383754 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383868 : List Nat := [2, 2, 2, 1, 1, 1, 7, 1, 1, 1, 4]
def baseStart_8383868 : Nat := 118140960795 + 8383868 * 2 ^ 59
def prefixEnd_8383868 : Nat := 4983230072969 + 3 ^ 40 * 8383868 * 2
def baseEnd_8383868 : Nat := 4304954027848909311593299

theorem tailTrace_8383868 : CollatzResearch.WordTrace tailWord_8383868 prefixEnd_8383868 4304954027848909311593299 := by
  unfold tailWord_8383868
  simp only [CollatzResearch.WordTrace]
  refine ⟨152892393595342780752028129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203856524793790374336037505 152892393595342780752028129)
  ·
    refine ⟨114669295196507085564021097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152892393595342780752028129 114669295196507085564021097)
    ·
      refine ⟨86001971397380314173015823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114669295196507085564021097 86001971397380314173015823)
      ·
        refine ⟨129002957096070471259523735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86001971397380314173015823 129002957096070471259523735)
        ·
          refine ⟨193504435644105706889285603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129002957096070471259523735 193504435644105706889285603)
          ·
            refine ⟨290256653466158560333928405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193504435644105706889285603 290256653466158560333928405)
            ·
              refine ⟨6802890315613091257826447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 290256653466158560333928405 6802890315613091257826447)
              ·
                refine ⟨10204335473419636886739671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802890315613091257826447 10204335473419636886739671)
                ·
                  refine ⟨15306503210129455330109507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10204335473419636886739671 15306503210129455330109507)
                  ·
                    refine ⟨22959754815194182995164261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15306503210129455330109507 22959754815194182995164261)
                    ·
                      refine ⟨4304954027848909311593299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22959754815194182995164261 4304954027848909311593299)
                      ·
                        rfl

theorem cell23_8383868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 1, 1, 4].length) (baseStart_8383868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383868 prefixEnd_8383868 := by exact prefixLift 8383868
  have htrace : WordTrace (prefixWord ++ tailWord_8383868) baseStart_8383868 baseEnd_8383868 := by
    simpa [prefixWord, tailWord_8383868, baseEnd_8383868] using wordTrace_append hprefix tailTrace_8383868
  have hstable : (prefixWord ++ tailWord_8383868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383868).length < 2 ^ (prefixWord ++ tailWord_8383868).sum := by decide
  have hdescent : baseEnd_8383868 < baseStart_8383868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383904 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_8383904 : Nat := 118140960795 + 8383904 * 2 ^ 59
def prefixEnd_8383904 : Nat := 4983230072969 + 3 ^ 40 * 8383904 * 2
def baseEnd_8383904 : Nat := 1434990837717490390247711

theorem tailTrace_8383904 : CollatzResearch.WordTrace tailWord_8383904 prefixEnd_8383904 1434990837717490390247711 := by
  unfold tailWord_8383904
  simp only [CollatzResearch.WordTrace]
  refine ⟨152893050109277569826183383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203857400145703426434911177 152893050109277569826183383)
  ·
    refine ⟨229339575163916354739275075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152893050109277569826183383 229339575163916354739275075)
    ·
      refine ⟨344009362745874532108912613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229339575163916354739275075 344009362745874532108912613)
      ·
        refine ⟨64501755514851474770421115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 344009362745874532108912613 64501755514851474770421115)
        ·
          refine ⟨96752633272277212155631673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64501755514851474770421115 96752633272277212155631673)
          ·
            refine ⟨72564474954207909116723755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96752633272277212155631673 72564474954207909116723755)
            ·
              refine ⟨108846712431311863675085633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72564474954207909116723755 108846712431311863675085633)
              ·
                refine ⟨81635034323483897756314225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108846712431311863675085633 81635034323483897756314225)
                ·
                  refine ⟨61226275742612923317235669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81635034323483897756314225 61226275742612923317235669)
                  ·
                    refine ⟨1434990837717490390247711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61226275742612923317235669 1434990837717490390247711)
                    ·
                      rfl

theorem cell23_8383904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_8383904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383904 prefixEnd_8383904 := by exact prefixLift 8383904
  have htrace : WordTrace (prefixWord ++ tailWord_8383904) baseStart_8383904 baseEnd_8383904 := by
    simpa [prefixWord, tailWord_8383904, baseEnd_8383904] using wordTrace_append hprefix tailTrace_8383904
  have hstable : (prefixWord ++ tailWord_8383904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383904).length < 2 ^ (prefixWord ++ tailWord_8383904).sum := by decide
  have hdescent : baseEnd_8383904 < baseStart_8383904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383941 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_8383941 : Nat := 118140960795 + 8383941 * 2 ^ 59
def prefixEnd_8383941 : Nat := 4983230072969 + 3 ^ 40 * 8383941 * 2
def baseEnd_8383941 : Nat := 4304991511936687525980463

theorem tailTrace_8383941 : CollatzResearch.WordTrace tailWord_8383941 prefixEnd_8383941 4304991511936687525980463 := by
  unfold tailWord_8383941
  simp only [CollatzResearch.WordTrace]
  refine ⟨305787449719421094971463677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203858299812947396647642451 305787449719421094971463677)
  ·
    refine ⟨114670293644782910614298879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305787449719421094971463677 114670293644782910614298879)
    ·
      refine ⟨172005440467174365921448319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114670293644782910614298879 172005440467174365921448319)
      ·
        refine ⟨258008160700761548882172479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172005440467174365921448319 258008160700761548882172479)
        ·
          refine ⟨387012241051142323323258719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258008160700761548882172479 387012241051142323323258719)
          ·
            refine ⟨580518361576713484984888079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387012241051142323323258719 580518361576713484984888079)
            ·
              refine ⟨870777542365070227477332119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580518361576713484984888079 870777542365070227477332119)
              ·
                refine ⟨1306166313547605341215998179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870777542365070227477332119 1306166313547605341215998179)
                ·
                  refine ⟨1959249470321408011823997269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1306166313547605341215998179 1959249470321408011823997269)
                  ·
                    refine ⟨5739988682582250034640617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1959249470321408011823997269 5739988682582250034640617)
                    ·
                      refine ⟨4304991511936687525980463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5739988682582250034640617 4304991511936687525980463)
                      ·
                        rfl

theorem cell23_8383941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_8383941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383941 prefixEnd_8383941 := by exact prefixLift 8383941
  have htrace : WordTrace (prefixWord ++ tailWord_8383941) baseStart_8383941 baseEnd_8383941 := by
    simpa [prefixWord, tailWord_8383941, baseEnd_8383941] using wordTrace_append hprefix tailTrace_8383941
  have hstable : (prefixWord ++ tailWord_8383941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383941).length < 2 ^ (prefixWord ++ tailWord_8383941).sum := by decide
  have hdescent : baseEnd_8383941 < baseStart_8383941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383975 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_8383975 : Nat := 118140960795 + 8383975 * 2 ^ 59
def prefixEnd_8383975 : Nat := 4983230072969 + 3 ^ 40 * 8383975 * 2
def baseEnd_8383975 : Nat := 4305008970278940392955307

theorem tailTrace_8383975 : CollatzResearch.WordTrace tailWord_8383975 prefixEnd_8383975 4305008970278940392955307 := by
  unfold tailWord_8383975
  simp only [CollatzResearch.WordTrace]
  refine ⟨305788689801297918778201379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203859126534198612518800919 305788689801297918778201379)
  ·
    refine ⟨458683034701946878167302069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305788689801297918778201379 458683034701946878167302069)
    ·
      refine ⟨43001534503307519828184569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 458683034701946878167302069 43001534503307519828184569)
      ·
        refine ⟨32251150877480639871138427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43001534503307519828184569 32251150877480639871138427)
        ·
          refine ⟨48376726316220959806707641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251150877480639871138427 48376726316220959806707641)
          ·
            refine ⟨36282544737165719855030731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48376726316220959806707641 36282544737165719855030731)
            ·
              refine ⟨54423817105748579782546097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36282544737165719855030731 54423817105748579782546097)
              ·
                refine ⟨40817862829311434836909573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54423817105748579782546097 40817862829311434836909573)
                ·
                  refine ⟨7653349280495894031920545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40817862829311434836909573 7653349280495894031920545)
                  ·
                    refine ⟨5740011960371920523940409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653349280495894031920545 5740011960371920523940409)
                    ·
                      refine ⟨4305008970278940392955307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740011960371920523940409 4305008970278940392955307)
                      ·
                        rfl

theorem cell23_8383975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_8383975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383975 prefixEnd_8383975 := by exact prefixLift 8383975
  have htrace : WordTrace (prefixWord ++ tailWord_8383975) baseStart_8383975 baseEnd_8383975 := by
    simpa [prefixWord, tailWord_8383975, baseEnd_8383975] using wordTrace_append hprefix tailTrace_8383975
  have hstable : (prefixWord ++ tailWord_8383975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383975).length < 2 ^ (prefixWord ++ tailWord_8383975).sum := by decide
  have hdescent : baseEnd_8383975 < baseStart_8383975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383978 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_8383978 : Nat := 118140960795 + 8383978 * 2 ^ 59
def prefixEnd_8383978 : Nat := 4983230072969 + 3 ^ 40 * 8383978 * 2
def baseEnd_8383978 : Nat := 4305010510720903881217793

theorem tailTrace_8383978 : CollatzResearch.WordTrace tailWord_8383978 prefixEnd_8383978 4305010510720903881217793 := by
  unfold tailWord_8383978
  simp only [CollatzResearch.WordTrace]
  refine ⟨76447199805071762572640147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203859199480191366860373725 76447199805071762572640147)
  ·
    refine ⟨114670799707607643858960221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76447199805071762572640147 114670799707607643858960221)
    ·
      refine ⟨43001549890352866447110083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114670799707607643858960221 43001549890352866447110083)
      ·
        refine ⟨64502324835529299670665125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43001549890352866447110083 64502324835529299670665125)
        ·
          refine ⟨12094185906661743688249711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64502324835529299670665125 12094185906661743688249711)
          ·
            refine ⟨18141278859992615532374567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094185906661743688249711 18141278859992615532374567)
            ·
              refine ⟨27211918289988923298561851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141278859992615532374567 27211918289988923298561851)
              ·
                refine ⟨40817877434983384947842777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27211918289988923298561851 40817877434983384947842777)
                ·
                  refine ⟨30613408076237538710882083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40817877434983384947842777 30613408076237538710882083)
                  ·
                    refine ⟨45920112114356308066323125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30613408076237538710882083 45920112114356308066323125)
                    ·
                      refine ⟨4305010510720903881217793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45920112114356308066323125 4305010510720903881217793)
                      ·
                        rfl

theorem cell23_8383978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_8383978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383978 prefixEnd_8383978 := by exact prefixLift 8383978
  have htrace : WordTrace (prefixWord ++ tailWord_8383978) baseStart_8383978 baseEnd_8383978 := by
    simpa [prefixWord, tailWord_8383978, baseEnd_8383978] using wordTrace_append hprefix tailTrace_8383978
  have hstable : (prefixWord ++ tailWord_8383978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383978).length < 2 ^ (prefixWord ++ tailWord_8383978).sum := by decide
  have hdescent : baseEnd_8383978 < baseStart_8383978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8383991 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3]
def baseStart_8383991 : Nat := 118140960795 + 8383991 * 2 ^ 59
def prefixEnd_8383991 : Nat := 4983230072969 + 3 ^ 40 * 8383991 * 2
def baseEnd_8383991 : Nat := 4305017185969412330355233

theorem tailTrace_8383991 : CollatzResearch.WordTrace tailWord_8383991 prefixEnd_8383991 4305017185969412330355233 := by
  unfold tailWord_8383991
  simp only [CollatzResearch.WordTrace]
  refine ⟨305789273369239953510783827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203859515579493302340522551 305789273369239953510783827)
  ·
    refine ⟨458683910053859930266175741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305789273369239953510783827 458683910053859930266175741)
    ·
      refine ⟨172006466270197473849815903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458683910053859930266175741 172006466270197473849815903)
      ·
        refine ⟨258009699405296210774723855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172006466270197473849815903 258009699405296210774723855)
        ·
          refine ⟨387014549107944316162085783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258009699405296210774723855 387014549107944316162085783)
          ·
            refine ⟨580521823661916474243128675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387014549107944316162085783 580521823661916474243128675)
            ·
              refine ⟨870782735492874711364693013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580521823661916474243128675 870782735492874711364693013)
              ·
                refine ⟨40817940726228502095219985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 870782735492874711364693013 40817940726228502095219985)
                ·
                  refine ⟨30613455544671376571414989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40817940726228502095219985 30613455544671376571414989)
                  ·
                    refine ⟨11480045829251766214280621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30613455544671376571414989 11480045829251766214280621)
                    ·
                      refine ⟨4305017185969412330355233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11480045829251766214280621 4305017185969412330355233)
                      ·
                        rfl

theorem cell23_8383991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_8383991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8383991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8383991 prefixEnd_8383991 := by exact prefixLift 8383991
  have htrace : WordTrace (prefixWord ++ tailWord_8383991) baseStart_8383991 baseEnd_8383991 := by
    simpa [prefixWord, tailWord_8383991, baseEnd_8383991] using wordTrace_append hprefix tailTrace_8383991
  have hstable : (prefixWord ++ tailWord_8383991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8383991).length < 2 ^ (prefixWord ++ tailWord_8383991).sum := by decide
  have hdescent : baseEnd_8383991 < baseStart_8383991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8383991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384013 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_8384013 : Nat := 118140960795 + 8384013 * 2 ^ 59
def prefixEnd_8384013 : Nat := 4983230072969 + 3 ^ 40 * 8384013 * 2
def baseEnd_8384013 : Nat := 4305028482543811244280133

theorem tailTrace_8384013 : CollatzResearch.WordTrace tailWord_8384013 prefixEnd_8384013 4305028482543811244280133 := by
  unfold tailWord_8384013
  simp only [CollatzResearch.WordTrace]
  refine ⟨305790075775160251268084693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203860050516773500845389795 305790075775160251268084693)
  ·
    refine ⟨7166954900980318389095735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 305790075775160251268084693 7166954900980318389095735)
    ·
      refine ⟨10750432351470477583643603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7166954900980318389095735 10750432351470477583643603)
      ·
        refine ⟨16125648527205716375465405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10750432351470477583643603 16125648527205716375465405)
        ·
          refine ⟨6047118197702143640799527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16125648527205716375465405 6047118197702143640799527)
          ·
            refine ⟨9070677296553215461199291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047118197702143640799527 9070677296553215461199291)
            ·
              refine ⟨13606015944829823191798937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9070677296553215461199291 13606015944829823191798937)
              ·
                refine ⟨10204511958622367393849203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13606015944829823191798937 10204511958622367393849203)
                ·
                  refine ⟨15306767937933551090773805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10204511958622367393849203 15306767937933551090773805)
                  ·
                    refine ⟨5740037976725081659040177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15306767937933551090773805 5740037976725081659040177)
                    ·
                      refine ⟨4305028482543811244280133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740037976725081659040177 4305028482543811244280133)
                      ·
                        rfl

theorem cell23_8384013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_8384013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384013 prefixEnd_8384013 := by exact prefixLift 8384013
  have htrace : WordTrace (prefixWord ++ tailWord_8384013) baseStart_8384013 baseEnd_8384013 := by
    simpa [prefixWord, tailWord_8384013, baseEnd_8384013] using wordTrace_append hprefix tailTrace_8384013
  have hstable : (prefixWord ++ tailWord_8384013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384013).length < 2 ^ (prefixWord ++ tailWord_8384013).sum := by decide
  have hdescent : baseEnd_8384013 < baseStart_8384013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384028 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_8384028 : Nat := 118140960795 + 8384028 * 2 ^ 59
def prefixEnd_8384028 : Nat := 4983230072969 + 3 ^ 40 * 8384028 * 2
def baseEnd_8384028 : Nat := 1435012061584542895197521

theorem tailTrace_8384028 : CollatzResearch.WordTrace tailWord_8384028 prefixEnd_8384028 1435012061584542895197521 := by
  unfold tailWord_8384028
  simp only [CollatzResearch.WordTrace]
  refine ⟨152895311435052954414940369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203860415246737272553253825 152895311435052954414940369)
  ·
    refine ⟨114671483576289715811205277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152895311435052954414940369 114671483576289715811205277)
    ·
      refine ⟨43001806341108643429201979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114671483576289715811205277 43001806341108643429201979)
      ·
        refine ⟨64502709511662965143802969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43001806341108643429201979 64502709511662965143802969)
        ·
          refine ⟨48377032133747223857852227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64502709511662965143802969 48377032133747223857852227)
          ·
            refine ⟨72565548200620835786778341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48377032133747223857852227 72565548200620835786778341)
            ·
              refine ⟨13606040287616406710020939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72565548200620835786778341 13606040287616406710020939)
              ·
                refine ⟨20409060431424610065031409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13606040287616406710020939 20409060431424610065031409)
                ·
                  refine ⟨15306795323568457548773557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20409060431424610065031409 15306795323568457548773557)
                  ·
                    refine ⟨1435012061584542895197521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15306795323568457548773557 1435012061584542895197521)
                    ·
                      rfl

theorem cell23_8384028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_8384028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384028 prefixEnd_8384028 := by exact prefixLift 8384028
  have htrace : WordTrace (prefixWord ++ tailWord_8384028) baseStart_8384028 baseEnd_8384028 := by
    simpa [prefixWord, tailWord_8384028, baseEnd_8384028] using wordTrace_append hprefix tailTrace_8384028
  have hstable : (prefixWord ++ tailWord_8384028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384028).length < 2 ^ (prefixWord ++ tailWord_8384028).sum := by decide
  have hdescent : baseEnd_8384028 < baseStart_8384028 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384031 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4]
def baseStart_8384031 : Nat := 118140960795 + 8384031 * 2 ^ 59
def prefixEnd_8384031 : Nat := 4983230072969 + 3 ^ 40 * 8384031 * 2
def baseEnd_8384031 : Nat := 4305037725195592173855049

theorem tailTrace_8384031 : CollatzResearch.WordTrace tailWord_8384031 prefixEnd_8384031 4305037725195592173855049 := by
  unfold tailWord_8384031
  simp only [CollatzResearch.WordTrace]
  refine ⟨305790732289095040342239947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203860488192730026894826631 305790732289095040342239947)
  ·
    refine ⟨458686098433642560513359921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305790732289095040342239947 458686098433642560513359921)
    ·
      refine ⟨344014573825231920385019941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458686098433642560513359921 344014573825231920385019941)
      ·
        refine ⟨64502732592230985072191239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 344014573825231920385019941 64502732592230985072191239)
        ·
          refine ⟨96754098888346477608286859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64502732592230985072191239 96754098888346477608286859)
          ·
            refine ⟨145131148332519716412430289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96754098888346477608286859 145131148332519716412430289)
            ·
              refine ⟨108848361249389787309322717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145131148332519716412430289 108848361249389787309322717)
              ·
                refine ⟨40818135468521170240996019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108848361249389787309322717 40818135468521170240996019)
                ·
                  refine ⟨61227203202781755361494029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40818135468521170240996019 61227203202781755361494029)
                  ·
                    refine ⟨22960201201043158260560261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61227203202781755361494029 22960201201043158260560261)
                    ·
                      refine ⟨4305037725195592173855049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22960201201043158260560261 4305037725195592173855049)
                      ·
                        rfl

theorem cell23_8384031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_8384031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384031 prefixEnd_8384031 := by exact prefixLift 8384031
  have htrace : WordTrace (prefixWord ++ tailWord_8384031) baseStart_8384031 baseEnd_8384031 := by
    simpa [prefixWord, tailWord_8384031, baseEnd_8384031] using wordTrace_append hprefix tailTrace_8384031
  have hstable : (prefixWord ++ tailWord_8384031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384031).length < 2 ^ (prefixWord ++ tailWord_8384031).sum := by decide
  have hdescent : baseEnd_8384031 < baseStart_8384031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384048 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2]
def baseStart_8384048 : Nat := 118140960795 + 8384048 * 2 ^ 59
def prefixEnd_8384048 : Nat := 4983230072969 + 3 ^ 40 * 8384048 * 2
def baseEnd_8384048 : Nat := 4305046454366718607342471

theorem tailTrace_8384048 : CollatzResearch.WordTrace tailWord_8384048 prefixEnd_8384048 4305046454366718607342471 := by
  unfold tailWord_8384048
  simp only [CollatzResearch.WordTrace]
  refine ⟨152895676165016726122804399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203860901553355634830405865 152895676165016726122804399)
  ·
    refine ⟨229343514247525089184206599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152895676165016726122804399 229343514247525089184206599)
    ·
      refine ⟨344015271371287633776309899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229343514247525089184206599 344015271371287633776309899)
      ·
        refine ⟨516022907056931450664464849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344015271371287633776309899 516022907056931450664464849)
        ·
          refine ⟨387017180292698587998348637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516022907056931450664464849 387017180292698587998348637)
          ·
            refine ⟨145131442609761970499380739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387017180292698587998348637 145131442609761970499380739)
            ·
              refine ⟨217697163914642955749071109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145131442609761970499380739 217697163914642955749071109)
              ·
                refine ⟨40818218233995554202950833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217697163914642955749071109 40818218233995554202950833)
                ·
                  refine ⟨30613663675496665652213125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40818218233995554202950833 30613663675496665652213125)
                  ·
                    refine ⟨5740061939155624809789961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30613663675496665652213125 5740061939155624809789961)
                    ·
                      refine ⟨4305046454366718607342471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740061939155624809789961 4305046454366718607342471)
                      ·
                        rfl

theorem cell23_8384048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2].length) (baseStart_8384048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384048 prefixEnd_8384048 := by exact prefixLift 8384048
  have htrace : WordTrace (prefixWord ++ tailWord_8384048) baseStart_8384048 baseEnd_8384048 := by
    simpa [prefixWord, tailWord_8384048, baseEnd_8384048] using wordTrace_append hprefix tailTrace_8384048
  have hstable : (prefixWord ++ tailWord_8384048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384048).length < 2 ^ (prefixWord ++ tailWord_8384048).sum := by decide
  have hdescent : baseEnd_8384048 < baseStart_8384048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384058 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_8384058 : Nat := 118140960795 + 8384058 * 2 ^ 59
def prefixEnd_8384058 : Nat := 4983230072969 + 3 ^ 40 * 8384058 * 2
def baseEnd_8384058 : Nat := 1435017196391087856072475

theorem tailTrace_8384058 : CollatzResearch.WordTrace tailWord_8384058 prefixEnd_8384058 1435017196391087856072475 := by
  unfold tailWord_8384058
  simp only [CollatzResearch.WordTrace]
  refine ⟨76447929264999305988368207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203861144706664815968981885 76447929264999305988368207)
  ·
    refine ⟨114671893897498958982552311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76447929264999305988368207 114671893897498958982552311)
    ·
      refine ⟨172007840846248438473828467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114671893897498958982552311 172007840846248438473828467)
      ·
        refine ⟨258011761269372657710742701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172007840846248438473828467 258011761269372657710742701)
        ·
          refine ⟨96754410476014746641528513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258011761269372657710742701 96754410476014746641528513)
          ·
            refine ⟨72565807857011059981146385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96754410476014746641528513 72565807857011059981146385)
            ·
              refine ⟨54424355892758294985859789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72565807857011059981146385 54424355892758294985859789)
              ·
                refine ⟨20409133459784360619697421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54424355892758294985859789 20409133459784360619697421)
                ·
                  refine ⟨7653425047419135232386533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20409133459784360619697421 7653425047419135232386533)
                  ·
                    refine ⟨1435017196391087856072475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653425047419135232386533 1435017196391087856072475)
                    ·
                      rfl

theorem cell23_8384058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_8384058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384058 prefixEnd_8384058 := by exact prefixLift 8384058
  have htrace : WordTrace (prefixWord ++ tailWord_8384058) baseStart_8384058 baseEnd_8384058 := by
    simpa [prefixWord, tailWord_8384058, baseEnd_8384058] using wordTrace_append hprefix tailTrace_8384058
  have hstable : (prefixWord ++ tailWord_8384058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384058).length < 2 ^ (prefixWord ++ tailWord_8384058).sum := by decide
  have hdescent : baseEnd_8384058 < baseStart_8384058 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384065 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_8384065 : Nat := 118140960795 + 8384065 * 2 ^ 59
def prefixEnd_8384065 : Nat := 4983230072969 + 3 ^ 40 * 8384065 * 2
def baseEnd_8384065 : Nat := 4305055183537845040829893

theorem tailTrace_8384065 : CollatzResearch.WordTrace tailWord_8384065 prefixEnd_8384065 4305055183537845040829893 := by
  unfold tailWord_8384065
  simp only [CollatzResearch.WordTrace]
  refine ⟨305791972370971864148977649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203861314913981242765985099 305791972370971864148977649)
  ·
    refine ⟨229343979278228898111733237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305791972370971864148977649 229343979278228898111733237)
    ·
      refine ⟨21500998057333959197974991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229343979278228898111733237 21500998057333959197974991)
      ·
        refine ⟨32251497086000938796962487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500998057333959197974991 32251497086000938796962487)
        ·
          refine ⟨48377245629001408195443731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251497086000938796962487 48377245629001408195443731)
          ·
            refine ⟨72565868443502112293165597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48377245629001408195443731 72565868443502112293165597)
            ·
              refine ⟨27212200666313292109937099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72565868443502112293165597 27212200666313292109937099)
              ·
                refine ⟨40818300999469938164905649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27212200666313292109937099 40818300999469938164905649)
                ·
                  refine ⟨30613725749602453623679237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40818300999469938164905649 30613725749602453623679237)
                  ·
                    refine ⟨5740073578050460054439857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30613725749602453623679237 5740073578050460054439857)
                    ·
                      refine ⟨4305055183537845040829893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740073578050460054439857 4305055183537845040829893)
                      ·
                        rfl

theorem cell23_8384065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_8384065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384065 prefixEnd_8384065 := by exact prefixLift 8384065
  have htrace : WordTrace (prefixWord ++ tailWord_8384065) baseStart_8384065 baseEnd_8384065 := by
    simpa [prefixWord, tailWord_8384065, baseEnd_8384065] using wordTrace_append hprefix tailTrace_8384065
  have hstable : (prefixWord ++ tailWord_8384065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384065).length < 2 ^ (prefixWord ++ tailWord_8384065).sum := by decide
  have hdescent : baseEnd_8384065 < baseStart_8384065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384092 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 1, 4]
def baseStart_8384092 : Nat := 118140960795 + 8384092 * 2 ^ 59
def prefixEnd_8384092 : Nat := 4983230072969 + 3 ^ 40 * 8384092 * 2
def baseEnd_8384092 : Nat := 1435023015838505478397423

theorem tailTrace_8384092 : CollatzResearch.WordTrace tailWord_8384092 prefixEnd_8384092 1435023015838505478397423 := by
  unfold tailWord_8384092
  simp only [CollatzResearch.WordTrace]
  refine ⟨152896478570937023880105265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203861971427916031840140353 152896478570937023880105265)
  ·
    refine ⟨114672358928202767910078949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152896478570937023880105265 114672358928202767910078949)
    ·
      refine ⟨21501067299038018983139803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114672358928202767910078949 21501067299038018983139803)
      ·
        refine ⟨32251600948557028474709705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21501067299038018983139803 32251600948557028474709705)
        ·
          refine ⟨24188700711417771356032279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32251600948557028474709705 24188700711417771356032279)
          ·
            refine ⟨36283051067126657034048419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188700711417771356032279 36283051067126657034048419)
            ·
              refine ⟨54424576600689985551072629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36283051067126657034048419 54424576600689985551072629)
              ·
                refine ⟨5102304056314686145413059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54424576600689985551072629 5102304056314686145413059)
                ·
                  refine ⟨7653456084472029218119589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102304056314686145413059 7653456084472029218119589)
                  ·
                    refine ⟨1435023015838505478397423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653456084472029218119589 1435023015838505478397423)
                    ·
                      rfl

theorem cell23_8384092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_8384092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384092 prefixEnd_8384092 := by exact prefixLift 8384092
  have htrace : WordTrace (prefixWord ++ tailWord_8384092) baseStart_8384092 baseEnd_8384092 := by
    simpa [prefixWord, tailWord_8384092, baseEnd_8384092] using wordTrace_append hprefix tailTrace_8384092
  have hstable : (prefixWord ++ tailWord_8384092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384092).length < 2 ^ (prefixWord ++ tailWord_8384092).sum := by decide
  have hdescent : baseEnd_8384092 < baseStart_8384092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384125 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 5, 2]
def baseStart_8384125 : Nat := 118140960795 + 8384125 * 2 ^ 59
def prefixEnd_8384125 : Nat := 4983230072969 + 3 ^ 40 * 8384125 * 2
def baseEnd_8384125 : Nat := 4305085992377114806079617

theorem tailTrace_8384125 : CollatzResearch.WordTrace tailWord_8384125 prefixEnd_8384125 4305085992377114806079617 := by
  unfold tailWord_8384125
  simp only [CollatzResearch.WordTrace]
  refine ⟨305794160750754494396161829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203862773833836329597441219 305794160750754494396161829)
  ·
    refine ⟨57336405140766467699280343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305794160750754494396161829 57336405140766467699280343)
    ·
      refine ⟨86004607711149701548920515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57336405140766467699280343 86004607711149701548920515)
      ·
        refine ⟨129006911566724552323380773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86004607711149701548920515 129006911566724552323380773)
        ·
          refine ⟨24188795918760853560633895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129006911566724552323380773 24188795918760853560633895)
          ·
            refine ⟨36283193878141280340950843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188795918760853560633895 36283193878141280340950843)
            ·
              refine ⟨54424790817211920511426265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36283193878141280340950843 54424790817211920511426265)
              ·
                refine ⟨40818593112908940383569699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54424790817211920511426265 40818593112908940383569699)
                ·
                  refine ⟨61227889669363410575354549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40818593112908940383569699 61227889669363410575354549)
                  ·
                    refine ⟨5740114656502819741439489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61227889669363410575354549 5740114656502819741439489)
                    ·
                      refine ⟨4305085992377114806079617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740114656502819741439489 4305085992377114806079617)
                      ·
                        rfl

theorem cell23_8384125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_8384125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384125 prefixEnd_8384125 := by exact prefixLift 8384125
  have htrace : WordTrace (prefixWord ++ tailWord_8384125) baseStart_8384125 baseEnd_8384125 := by
    simpa [prefixWord, tailWord_8384125, baseEnd_8384125] using wordTrace_append hprefix tailTrace_8384125
  have hstable : (prefixWord ++ tailWord_8384125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384125).length < 2 ^ (prefixWord ++ tailWord_8384125).sum := by decide
  have hdescent : baseEnd_8384125 < baseStart_8384125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384135 : List Nat := [1, 1, 4, 2, 1, 4, 2, 2, 1, 5]
def baseStart_8384135 : Nat := 118140960795 + 8384135 * 2 ^ 59
def prefixEnd_8384135 : Nat := 4983230072969 + 3 ^ 40 * 8384135 * 2
def baseEnd_8384135 : Nat := 1435030375727886588984857

theorem tailTrace_8384135 : CollatzResearch.WordTrace tailWord_8384135 prefixEnd_8384135 1435030375727886588984857 := by
  unfold tailWord_8384135
  simp only [CollatzResearch.WordTrace]
  refine ⟨305794525480718266104025859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203863016987145510736017239 305794525480718266104025859)
  ·
    refine ⟨458691788221077399156038789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305794525480718266104025859 458691788221077399156038789)
    ·
      refine ⟨86004710291452012341757273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458691788221077399156038789 86004710291452012341757273)
      ·
        refine ⟨64503532718589009256317955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86004710291452012341757273 64503532718589009256317955)
        ·
          refine ⟨96755299077883513884476933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64503532718589009256317955 96755299077883513884476933)
          ·
            refine ⟨18141618577103158853339425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 96755299077883513884476933 18141618577103158853339425)
            ·
              refine ⟨13606213932827369140004569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18141618577103158853339425 13606213932827369140004569)
              ·
                refine ⟨10204660449620526855003427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13606213932827369140004569 10204660449620526855003427)
                ·
                  refine ⟨15306990674430790282505141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10204660449620526855003427 15306990674430790282505141)
                  ·
                    refine ⟨1435030375727886588984857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15306990674430790282505141 1435030375727886588984857)
                    ·
                      rfl

theorem cell23_8384135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_8384135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384135 prefixEnd_8384135 := by exact prefixLift 8384135
  have htrace : WordTrace (prefixWord ++ tailWord_8384135) baseStart_8384135 baseEnd_8384135 := by
    simpa [prefixWord, tailWord_8384135, baseEnd_8384135] using wordTrace_append hprefix tailTrace_8384135
  have hstable : (prefixWord ++ tailWord_8384135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384135).length < 2 ^ (prefixWord ++ tailWord_8384135).sum := by decide
  have hdescent : baseEnd_8384135 < baseStart_8384135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384159 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 2, 3, 2]
def baseStart_8384159 : Nat := 118140960795 + 8384159 * 2 ^ 59
def prefixEnd_8384159 : Nat := 4983230072969 + 3 ^ 40 * 8384159 * 2
def baseEnd_8384159 : Nat := 4305103450719367673054461

theorem tailTrace_8384159 : CollatzResearch.WordTrace tailWord_8384159 prefixEnd_8384159 4305103450719367673054461 := by
  unfold tailWord_8384159
  simp only [CollatzResearch.WordTrace]
  refine ⟨305795400832631318202899531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203863600555087545468599687 305795400832631318202899531)
  ·
    refine ⟨458693101248946977304349297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305795400832631318202899531 458693101248946977304349297)
    ·
      refine ⟨344019825936710232978261973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458693101248946977304349297 344019825936710232978261973)
      ·
        refine ⟨8062964670391646085428015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 344019825936710232978261973 8062964670391646085428015)
        ·
          refine ⟨12094447005587469128142023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062964670391646085428015 12094447005587469128142023)
          ·
            refine ⟨18141670508381203692213035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094447005587469128142023 18141670508381203692213035)
            ·
              refine ⟨27212505762571805538319553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141670508381203692213035 27212505762571805538319553)
              ·
                refine ⟨20409379321928854153739665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27212505762571805538319553 20409379321928854153739665)
                ·
                  refine ⟨15307034491446640615304749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20409379321928854153739665 15307034491446640615304749)
                  ·
                    refine ⟨5740137934292490230739281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15307034491446640615304749 5740137934292490230739281)
                    ·
                      refine ⟨4305103450719367673054461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740137934292490230739281 4305103450719367673054461)
                      ·
                        rfl

theorem cell23_8384159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_8384159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384159 prefixEnd_8384159 := by exact prefixLift 8384159
  have htrace : WordTrace (prefixWord ++ tailWord_8384159) baseStart_8384159 baseEnd_8384159 := by
    simpa [prefixWord, tailWord_8384159, baseEnd_8384159] using wordTrace_append hprefix tailTrace_8384159
  have hstable : (prefixWord ++ tailWord_8384159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384159).length < 2 ^ (prefixWord ++ tailWord_8384159).sum := by decide
  have hdescent : baseEnd_8384159 < baseStart_8384159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384228 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_8384228 : Nat := 118140960795 + 8384228 * 2 ^ 59
def prefixEnd_8384228 : Nat := 4983230072969 + 3 ^ 40 * 8384228 * 2
def baseEnd_8384228 : Nat := 4305138880884527903091643

theorem tailTrace_8384228 : CollatzResearch.WordTrace tailWord_8384228 prefixEnd_8384228 4305138880884527903091643 := by
  unfold tailWord_8384228
  simp only [CollatzResearch.WordTrace]
  refine ⟨152898958734690671493580669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203865278312920895324774225 152898958734690671493580669)
  ·
    refine ⟨57337109525509001810092751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152898958734690671493580669 57337109525509001810092751)
    ·
      refine ⟨86005664288263502715139127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57337109525509001810092751 86005664288263502715139127)
      ·
        refine ⟨129008496432395254072708691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86005664288263502715139127 129008496432395254072708691)
        ·
          refine ⟨193512744648592881109063037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129008496432395254072708691 193512744648592881109063037)
          ·
            refine ⟨72567279243222330415898639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193512744648592881109063037 72567279243222330415898639)
            ·
              refine ⟨108850918864833495623847959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72567279243222330415898639 108850918864833495623847959)
              ·
                refine ⟨163276378297250243435771939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108850918864833495623847959 163276378297250243435771939)
                ·
                  refine ⟨244914567445875365153657909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163276378297250243435771939 244914567445875365153657909)
                  ·
                    refine ⟨22960740698050815483155429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 244914567445875365153657909 22960740698050815483155429)
                    ·
                      refine ⟨4305138880884527903091643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22960740698050815483155429 4305138880884527903091643)
                      ·
                        rfl

theorem cell23_8384228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_8384228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384228 prefixEnd_8384228 := by exact prefixLift 8384228
  have htrace : WordTrace (prefixWord ++ tailWord_8384228) baseStart_8384228 baseEnd_8384228 := by
    simpa [prefixWord, tailWord_8384228, baseEnd_8384228] using wordTrace_append hprefix tailTrace_8384228
  have hstable : (prefixWord ++ tailWord_8384228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384228).length < 2 ^ (prefixWord ++ tailWord_8384228).sum := by decide
  have hdescent : baseEnd_8384228 < baseStart_8384228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384232 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_8384232 : Nat := 118140960795 + 8384232 * 2 ^ 59
def prefixEnd_8384232 : Nat := 4983230072969 + 3 ^ 40 * 8384232 * 2
def baseEnd_8384232 : Nat := 4305140934807145887441625

theorem tailTrace_8384232 : CollatzResearch.WordTrace tailWord_8384232 prefixEnd_8384232 4305140934807145887441625 := by
  unfold tailWord_8384232
  simp only [CollatzResearch.WordTrace]
  refine ⟨152899031680683425835153475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203865375574244567780204633 152899031680683425835153475)
  ·
    refine ⟨229348547521025138752730213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152899031680683425835153475 229348547521025138752730213)
    ·
      refine ⟨43002852660192213516136915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229348547521025138752730213 43002852660192213516136915)
      ·
        refine ⟨64504278990288320274205373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43002852660192213516136915 64504278990288320274205373)
        ·
          refine ⟨24189104621358120102827015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64504278990288320274205373 24189104621358120102827015)
          ·
            refine ⟨36283656932037180154240523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24189104621358120102827015 36283656932037180154240523)
            ·
              refine ⟨54425485398055770231360785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36283656932037180154240523 54425485398055770231360785)
              ·
                refine ⟨40819114048541827673520589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54425485398055770231360785 40819114048541827673520589)
                ·
                  refine ⟨15307167768203185377570221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40819114048541827673520589 15307167768203185377570221)
                  ·
                    refine ⟨5740187913076194516588833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15307167768203185377570221 5740187913076194516588833)
                    ·
                      refine ⟨4305140934807145887441625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740187913076194516588833 4305140934807145887441625)
                      ·
                        rfl

theorem cell23_8384232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_8384232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384232 prefixEnd_8384232 := by exact prefixLift 8384232
  have htrace : WordTrace (prefixWord ++ tailWord_8384232) baseStart_8384232 baseEnd_8384232 := by
    simpa [prefixWord, tailWord_8384232, baseEnd_8384232] using wordTrace_append hprefix tailTrace_8384232
  have hstable : (prefixWord ++ tailWord_8384232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384232).length < 2 ^ (prefixWord ++ tailWord_8384232).sum := by decide
  have hdescent : baseEnd_8384232 < baseStart_8384232 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384248 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_8384248 : Nat := 118140960795 + 8384248 * 2 ^ 59
def prefixEnd_8384248 : Nat := 4983230072969 + 3 ^ 40 * 8384248 * 2
def baseEnd_8384248 : Nat := 4305149150497617824841551

theorem tailTrace_8384248 : CollatzResearch.WordTrace tailWord_8384248 prefixEnd_8384248 4305149150497617824841551 := by
  unfold tailWord_8384248
  simp only [CollatzResearch.WordTrace]
  refine ⟨152899323464654443201444699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203865764619539257601926265 152899323464654443201444699)
  ·
    refine ⟨229348985196981664802167049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152899323464654443201444699 229348985196981664802167049)
    ·
      refine ⟨172011738897736248601625287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229348985196981664802167049 172011738897736248601625287)
      ·
        refine ⟨258017608346604372902437931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172011738897736248601625287 258017608346604372902437931)
        ·
          refine ⟨387026412519906559353656897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258017608346604372902437931 387026412519906559353656897)
          ·
            refine ⟨290269809389929919515242673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387026412519906559353656897 290269809389929919515242673)
            ·
              refine ⟨217702357042447439636432005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290269809389929919515242673 217702357042447439636432005)
              ·
                refine ⟨40819191945458894931831001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217702357042447439636432005 40819191945458894931831001)
                ·
                  refine ⟨30614393959094171198873251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40819191945458894931831001 30614393959094171198873251)
                  ·
                    refine ⟨45921590938641256798309877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30614393959094171198873251 45921590938641256798309877)
                    ·
                      refine ⟨4305149150497617824841551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45921590938641256798309877 4305149150497617824841551)
                      ·
                        rfl

theorem cell23_8384248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_8384248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384248 prefixEnd_8384248 := by exact prefixLift 8384248
  have htrace : WordTrace (prefixWord ++ tailWord_8384248) baseStart_8384248 baseEnd_8384248 := by
    simpa [prefixWord, tailWord_8384248, baseEnd_8384248] using wordTrace_append hprefix tailTrace_8384248
  have hstable : (prefixWord ++ tailWord_8384248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384248).length < 2 ^ (prefixWord ++ tailWord_8384248).sum := by decide
  have hdescent : baseEnd_8384248 < baseStart_8384248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384266 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_8384266 : Nat := 118140960795 + 8384266 * 2 ^ 59
def prefixEnd_8384266 : Nat := 4983230072969 + 3 ^ 40 * 8384266 * 2
def baseEnd_8384266 : Nat := 4305158393149398754416469

theorem tailTrace_8384266 : CollatzResearch.WordTrace tailWord_8384266 prefixEnd_8384266 4305158393149398754416469 := by
  unfold tailWord_8384266
  simp only [CollatzResearch.WordTrace]
  refine ⟨76449825860810918869261163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203866202295495783651363101 76449825860810918869261163)
  ·
    refine ⟨114674738791216378303891745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76449825860810918869261163 114674738791216378303891745)
    ·
      refine ⟨86006054093412283727918809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114674738791216378303891745 86006054093412283727918809)
      ·
        refine ⟨64504540570059212795939107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86006054093412283727918809 64504540570059212795939107)
        ·
          refine ⟨96756810855088819193908661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64504540570059212795939107 96756810855088819193908661)
          ·
            refine ⟨9070951017664576799428937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96756810855088819193908661 9070951017664576799428937)
            ·
              refine ⟨6803213263248432599571703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070951017664576799428937 6803213263248432599571703)
              ·
                refine ⟨10204819894872648899357555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803213263248432599571703 10204819894872648899357555)
                ·
                  refine ⟨15307229842308973349036333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10204819894872648899357555 15307229842308973349036333)
                  ·
                    refine ⟨5740211190865865005888625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15307229842308973349036333 5740211190865865005888625)
                    ·
                      refine ⟨4305158393149398754416469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740211190865865005888625 4305158393149398754416469)
                      ·
                        rfl

theorem cell23_8384266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_8384266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384266 prefixEnd_8384266 := by exact prefixLift 8384266
  have htrace : WordTrace (prefixWord ++ tailWord_8384266) baseStart_8384266 baseEnd_8384266 := by
    simpa [prefixWord, tailWord_8384266, baseEnd_8384266] using wordTrace_append hprefix tailTrace_8384266
  have hstable : (prefixWord ++ tailWord_8384266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384266).length < 2 ^ (prefixWord ++ tailWord_8384266).sum := by decide
  have hdescent : baseEnd_8384266 < baseStart_8384266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384279 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 4, 2, 2]
def baseStart_8384279 : Nat := 118140960795 + 8384279 * 2 ^ 59
def prefixEnd_8384279 : Nat := 4983230072969 + 3 ^ 40 * 8384279 * 2
def baseEnd_8384279 : Nat := 4305165068397907203553909

theorem tailTrace_8384279 : CollatzResearch.WordTrace tailWord_8384279 prefixEnd_8384279 4305165068397907203553909 := by
  unfold tailWord_8384279
  simp only [CollatzResearch.WordTrace]
  refine ⟨305799777592196578697267891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203866518394797719131511927 305799777592196578697267891)
  ·
    refine ⟨458699666388294868045901837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305799777592196578697267891 458699666388294868045901837)
    ·
      refine ⟨172012374895610575517213189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458699666388294868045901837 172012374895610575517213189)
      ·
        refine ⟨32252320292926982909477473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172012374895610575517213189 32252320292926982909477473)
        ·
          refine ⟨24189240219695237182108105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32252320292926982909477473 24189240219695237182108105)
          ·
            refine ⟨18141930164771427886581079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24189240219695237182108105 18141930164771427886581079)
            ·
              refine ⟨27212895247157141829871619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141930164771427886581079 27212895247157141829871619)
              ·
                refine ⟨40819342870735712744807429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27212895247157141829871619 40819342870735712744807429)
                ·
                  refine ⟨7653626788262946139651393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40819342870735712744807429 7653626788262946139651393)
                  ·
                    refine ⟨5740220091197209604738545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653626788262946139651393 5740220091197209604738545)
                    ·
                      refine ⟨4305165068397907203553909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740220091197209604738545 4305165068397907203553909)
                      ·
                        rfl

theorem cell23_8384279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_8384279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384279 prefixEnd_8384279 := by exact prefixLift 8384279
  have htrace : WordTrace (prefixWord ++ tailWord_8384279) baseStart_8384279 baseEnd_8384279 := by
    simpa [prefixWord, tailWord_8384279, baseEnd_8384279] using wordTrace_append hprefix tailTrace_8384279
  have hstable : (prefixWord ++ tailWord_8384279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384279).length < 2 ^ (prefixWord ++ tailWord_8384279).sum := by decide
  have hdescent : baseEnd_8384279 < baseStart_8384279 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384319 : List Nat := [1, 1, 2, 2, 6, 2, 1, 3, 5]
def baseStart_8384319 : Nat := 118140960795 + 8384319 * 2 ^ 59
def prefixEnd_8384319 : Nat := 4983230072969 + 3 ^ 40 * 8384319 * 2
def baseEnd_8384319 : Nat := 478353956402676338561525

theorem tailTrace_8384319 : CollatzResearch.WordTrace tailWord_8384319 prefixEnd_8384319 478353956402676338561525 := by
  unfold tailWord_8384319
  simp only [CollatzResearch.WordTrace]
  refine ⟨305801236512051665528724011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203867491008034443685816007 305801236512051665528724011)
  ·
    refine ⟨458701854768077498293086017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305801236512051665528724011 458701854768077498293086017)
    ·
      refine ⟨344026391076058123719814513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458701854768077498293086017 344026391076058123719814513)
      ·
        refine ⟨258019793307043592789860885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344026391076058123719814513 258019793307043592789860885)
        ·
          refine ⟨12094677811267668412024729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 258019793307043592789860885 12094677811267668412024729)
          ·
            refine ⟨9071008358450751309018547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12094677811267668412024729 9071008358450751309018547)
            ·
              refine ⟨13606512537676126963527821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071008358450751309018547 13606512537676126963527821)
              ·
                refine ⟨5102442201628547611322933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13606512537676126963527821 5102442201628547611322933)
                ·
                  refine ⟨478353956402676338561525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5102442201628547611322933 478353956402676338561525)
                  ·
                    rfl

theorem cell23_8384319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 3, 5].length) (baseStart_8384319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384319 prefixEnd_8384319 := by exact prefixLift 8384319
  have htrace : WordTrace (prefixWord ++ tailWord_8384319) baseStart_8384319 baseEnd_8384319 := by
    simpa [prefixWord, tailWord_8384319, baseEnd_8384319] using wordTrace_append hprefix tailTrace_8384319
  have hstable : (prefixWord ++ tailWord_8384319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384319).length < 2 ^ (prefixWord ++ tailWord_8384319).sum := by decide
  have hdescent : baseEnd_8384319 < baseStart_8384319 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384332 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 2, 5]
def baseStart_8384332 : Nat := 118140960795 + 8384332 * 2 ^ 59
def prefixEnd_8384332 : Nat := 4983230072969 + 3 ^ 40 * 8384332 * 2
def baseEnd_8384332 : Nat := 1435064094290865165397055

theorem tailTrace_8384332 : CollatzResearch.WordTrace tailWord_8384332 prefixEnd_8384332 1435064094290865165397055 := by
  unfold tailWord_8384332
  simp only [CollatzResearch.WordTrace]
  refine ⟨152900855330502284374473625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203867807107336379165964833 152900855330502284374473625)
  ·
    refine ⟨114675641497876713280855219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152900855330502284374473625 114675641497876713280855219)
    ·
      refine ⟨172013462246815069921282829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114675641497876713280855219 172013462246815069921282829)
      ·
        refine ⟨64505048342555651220481061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172013462246815069921282829 64505048342555651220481061)
        ·
          refine ⟨12094696564229184603840199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64505048342555651220481061 12094696564229184603840199)
          ·
            refine ⟨18142044846343776905760299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094696564229184603840199 18142044846343776905760299)
            ·
              refine ⟨27213067269515665358640449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18142044846343776905760299 27213067269515665358640449)
              ·
                refine ⟨20409800452136749018980337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27213067269515665358640449 20409800452136749018980337)
                ·
                  refine ⟨15307350339102561764235253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20409800452136749018980337 15307350339102561764235253)
                  ·
                    refine ⟨1435064094290865165397055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15307350339102561764235253 1435064094290865165397055)
                    ·
                      rfl

theorem cell23_8384332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 2, 5].length) (baseStart_8384332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384332 prefixEnd_8384332 := by exact prefixLift 8384332
  have htrace : WordTrace (prefixWord ++ tailWord_8384332) baseStart_8384332 baseEnd_8384332 := by
    simpa [prefixWord, tailWord_8384332, baseEnd_8384332] using wordTrace_append hprefix tailTrace_8384332
  have hstable : (prefixWord ++ tailWord_8384332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384332).length < 2 ^ (prefixWord ++ tailWord_8384332).sum := by decide
  have hdescent : baseEnd_8384332 < baseStart_8384332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384365 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_8384365 : Nat := 118140960795 + 8384365 * 2 ^ 59
def prefixEnd_8384365 : Nat := 4983230072969 + 3 ^ 40 * 8384365 * 2
def baseEnd_8384365 : Nat := 4305209227734193867078513

theorem tailTrace_8384365 : CollatzResearch.WordTrace tailWord_8384365 prefixEnd_8384365 4305209227734193867078513 := by
  unfold tailWord_8384365
  simp only [CollatzResearch.WordTrace]
  refine ⟨305802914269885015384898549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203868609513256676923265699 305802914269885015384898549)
  ·
    refine ⟨28669023212801720192334239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305802914269885015384898549 28669023212801720192334239)
    ·
      refine ⟨43003534819202580288501359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28669023212801720192334239 43003534819202580288501359)
      ·
        refine ⟨64505302228803870432752039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43003534819202580288501359 64505302228803870432752039)
        ·
          refine ⟨96757953343205805649128059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64505302228803870432752039 96757953343205805649128059)
          ·
            refine ⟨145136930014808708473692089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96757953343205805649128059 145136930014808708473692089)
            ·
              refine ⟨108852697511106531355269067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145136930014808708473692089 108852697511106531355269067)
              ·
                refine ⟨163279046266659797032903601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108852697511106531355269067 163279046266659797032903601)
                ·
                  refine ⟨122459284699994847774677701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163279046266659797032903601 122459284699994847774677701)
                  ·
                    refine ⟨22961115881249033957752069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122459284699994847774677701 22961115881249033957752069)
                    ·
                      refine ⟨4305209227734193867078513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22961115881249033957752069 4305209227734193867078513)
                      ·
                        rfl

theorem cell23_8384365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_8384365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384365 prefixEnd_8384365 := by exact prefixLift 8384365
  have htrace : WordTrace (prefixWord ++ tailWord_8384365) baseStart_8384365 baseEnd_8384365 := by
    simpa [prefixWord, tailWord_8384365, baseEnd_8384365] using wordTrace_append hprefix tailTrace_8384365
  have hstable : (prefixWord ++ tailWord_8384365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384365).length < 2 ^ (prefixWord ++ tailWord_8384365).sum := by decide
  have hdescent : baseEnd_8384365 < baseStart_8384365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384405 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_8384405 : Nat := 118140960795 + 8384405 * 2 ^ 59
def prefixEnd_8384405 : Nat := 4983230072969 + 3 ^ 40 * 8384405 * 2
def baseEnd_8384405 : Nat := 1435076588986791236859443

theorem tailTrace_8384405 : CollatzResearch.WordTrace tailWord_8384405 prefixEnd_8384405 1435076588986791236859443 := by
  unfold tailWord_8384405
  simp only [CollatzResearch.WordTrace]
  refine ⟨305804373189740102216354669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203869582126493401477569779 305804373189740102216354669)
  ·
    refine ⟨114676639946152538331133001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305804373189740102216354669 114676639946152538331133001)
    ·
      refine ⟨86007479959614403748349751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114676639946152538331133001 86007479959614403748349751)
      ·
        refine ⟨129011219939421605622524627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86007479959614403748349751 129011219939421605622524627)
        ·
          refine ⟨193516829909132408433786941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129011219939421605622524627 193516829909132408433786941)
          ·
            refine ⟨72568811215924653162670103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193516829909132408433786941 72568811215924653162670103)
            ·
              refine ⟨108853216823886979744005155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72568811215924653162670103 108853216823886979744005155)
              ·
                refine ⟨163279825235830469616007733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108853216823886979744005155 163279825235830469616007733)
                ·
                  refine ⟨15307483615859106526500725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163279825235830469616007733 15307483615859106526500725)
                  ·
                    refine ⟨1435076588986791236859443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15307483615859106526500725 1435076588986791236859443)
                    ·
                      rfl

theorem cell23_8384405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_8384405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384405 prefixEnd_8384405 := by exact prefixLift 8384405
  have htrace : WordTrace (prefixWord ++ tailWord_8384405) baseStart_8384405 baseEnd_8384405 := by
    simpa [prefixWord, tailWord_8384405, baseEnd_8384405] using wordTrace_append hprefix tailTrace_8384405
  have hstable : (prefixWord ++ tailWord_8384405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384405).length < 2 ^ (prefixWord ++ tailWord_8384405).sum := by decide
  have hdescent : baseEnd_8384405 < baseStart_8384405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384435 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 1, 6]
def baseStart_8384435 : Nat := 118140960795 + 8384435 * 2 ^ 59
def prefixEnd_8384435 : Nat := 4983230072969 + 3 ^ 40 * 8384435 * 2
def baseEnd_8384435 : Nat := 1435081723793336197734397

theorem tailTrace_8384435 : CollatzResearch.WordTrace tailWord_8384435 prefixEnd_8384435 1435081723793336197734397 := by
  unfold tailWord_8384435
  simp only [CollatzResearch.WordTrace]
  refine ⟨305805467379631417339946759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203870311586420944893297839 305805467379631417339946759)
  ·
    refine ⟨458708201069447126009920139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305805467379631417339946759 458708201069447126009920139)
    ·
      refine ⟨688062301604170689014880209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458708201069447126009920139 688062301604170689014880209)
      ·
        refine ⟨516046726203128016761160157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688062301604170689014880209 516046726203128016761160157)
        ·
          refine ⟨193517522326173006285435059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516046726203128016761160157 193517522326173006285435059)
          ·
            refine ⟨290276283489259509428152589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193517522326173006285435059 290276283489259509428152589)
            ·
              refine ⟨108853606308472316035557221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290276283489259509428152589 108853606308472316035557221)
              ·
                refine ⟨20410051182838559256666979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108853606308472316035557221 20410051182838559256666979)
                ·
                  refine ⟨30615076774257838885000469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410051182838559256666979 30615076774257838885000469)
                  ·
                    refine ⟨1435081723793336197734397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30615076774257838885000469 1435081723793336197734397)
                    ·
                      rfl

theorem cell23_8384435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 6].length) (baseStart_8384435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384435 prefixEnd_8384435 := by exact prefixLift 8384435
  have htrace : WordTrace (prefixWord ++ tailWord_8384435) baseStart_8384435 baseEnd_8384435 := by
    simpa [prefixWord, tailWord_8384435, baseEnd_8384435] using wordTrace_append hprefix tailTrace_8384435
  have hstable : (prefixWord ++ tailWord_8384435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384435).length < 2 ^ (prefixWord ++ tailWord_8384435).sum := by decide
  have hdescent : baseEnd_8384435 < baseStart_8384435 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384455 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6]
def baseStart_8384455 : Nat := 118140960795 + 8384455 * 2 ^ 59
def prefixEnd_8384455 : Nat := 4983230072969 + 3 ^ 40 * 8384455 * 2
def baseEnd_8384455 : Nat := 4305255440993098514953099

theorem tailTrace_8384455 : CollatzResearch.WordTrace tailWord_8384455 prefixEnd_8384455 4305255440993098514953099 := by
  unfold tailWord_8384455
  simp only [CollatzResearch.WordTrace]
  refine ⟨305806196839558960755674819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203870797893039307170449879 305806196839558960755674819)
  ·
    refine ⟨458709295259338441133512229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305806196839558960755674819 458709295259338441133512229)
    ·
      refine ⟨86007992861125957712533543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458709295259338441133512229 86007992861125957712533543)
      ·
        refine ⟨129011989291688936568800315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86007992861125957712533543 129011989291688936568800315)
        ·
          refine ⟨193517983937533404853200473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129011989291688936568800315 193517983937533404853200473)
          ·
            refine ⟨145138487953150053639900355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193517983937533404853200473 145138487953150053639900355)
            ·
              refine ⟨217707731929725080459850533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145138487953150053639900355 217707731929725080459850533)
              ·
                refine ⟨40820199736823452586221975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217707731929725080459850533 40820199736823452586221975)
                ·
                  refine ⟨61230299605235178879332963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40820199736823452586221975 61230299605235178879332963)
                  ·
                    refine ⟨91845449407852768318999445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61230299605235178879332963 91845449407852768318999445)
                    ·
                      refine ⟨4305255440993098514953099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91845449407852768318999445 4305255440993098514953099)
                      ·
                        rfl

theorem cell23_8384455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_8384455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384455 prefixEnd_8384455 := by exact prefixLift 8384455
  have htrace : WordTrace (prefixWord ++ tailWord_8384455) baseStart_8384455 baseEnd_8384455 := by
    simpa [prefixWord, tailWord_8384455, baseEnd_8384455] using wordTrace_append hprefix tailTrace_8384455
  have hstable : (prefixWord ++ tailWord_8384455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384455).length < 2 ^ (prefixWord ++ tailWord_8384455).sum := by decide
  have hdescent : baseEnd_8384455 < baseStart_8384455 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384462 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_8384462 : Nat := 118140960795 + 8384462 * 2 ^ 59
def prefixEnd_8384462 : Nat := 4983230072969 + 3 ^ 40 * 8384462 * 2
def baseEnd_8384462 : Nat := 4305259035357679987565567

theorem tailTrace_8384462 : CollatzResearch.WordTrace tailWord_8384462 prefixEnd_8384462 4305259035357679987565567 := by
  unfold tailWord_8384462
  simp only [CollatzResearch.WordTrace]
  refine ⟨38225806518816700118897455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203870968100355733967453093 38225806518816700118897455)
  ·
    refine ⟨57338709778225050178346183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38225806518816700118897455 57338709778225050178346183)
    ·
      refine ⟨86008064667337575267519275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57338709778225050178346183 86008064667337575267519275)
      ·
        refine ⟨129012097001006362901278913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86008064667337575267519275 129012097001006362901278913)
        ·
          refine ⟨96759072750754772175959185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129012097001006362901278913 96759072750754772175959185)
          ·
            refine ⟨72569304563066079131969389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96759072750754772175959185 72569304563066079131969389)
            ·
              refine ⟨27213489211149779674488521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72569304563066079131969389 27213489211149779674488521)
              ·
                refine ⟨20410116908362334755866391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27213489211149779674488521 20410116908362334755866391)
                ·
                  refine ⟨30615175362543502133799587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410116908362334755866391 30615175362543502133799587)
                  ·
                    refine ⟨45922763043815253200699381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30615175362543502133799587 45922763043815253200699381)
                    ·
                      refine ⟨4305259035357679987565567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45922763043815253200699381 4305259035357679987565567)
                      ·
                        rfl

theorem cell23_8384462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_8384462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384462 prefixEnd_8384462 := by exact prefixLift 8384462
  have htrace : WordTrace (prefixWord ++ tailWord_8384462) baseStart_8384462 baseEnd_8384462 := by
    simpa [prefixWord, tailWord_8384462, baseEnd_8384462] using wordTrace_append hprefix tailTrace_8384462
  have hstable : (prefixWord ++ tailWord_8384462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384462).length < 2 ^ (prefixWord ++ tailWord_8384462).sum := by decide
  have hdescent : baseEnd_8384462 < baseStart_8384462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384469 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_8384469 : Nat := 118140960795 + 8384469 * 2 ^ 59
def prefixEnd_8384469 : Nat := 4983230072969 + 3 ^ 40 * 8384469 * 2
def baseEnd_8384469 : Nat := 1435087543240753820059345

theorem tailTrace_8384469 : CollatzResearch.WordTrace tailWord_8384469 prefixEnd_8384469 1435087543240753820059345 := by
  unfold tailWord_8384469
  simp only [CollatzResearch.WordTrace]
  refine ⟨305806707461508241146684461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203871138307672160764456307 305806707461508241146684461)
  ·
    refine ⟨114677515298065590430006673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305806707461508241146684461 114677515298065590430006673)
    ·
      refine ⟨86008136473549192822505005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114677515298065590430006673 86008136473549192822505005)
      ·
        refine ⟨32253051177580947308439377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86008136473549192822505005 32253051177580947308439377)
        ·
          refine ⟨24189788383185710481329533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32253051177580947308439377 24189788383185710481329533)
          ·
            refine ⟨9071170643694641430498575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189788383185710481329533 9071170643694641430498575)
            ·
              refine ⟨13606755965541962145747863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071170643694641430498575 13606755965541962145747863)
              ·
                refine ⟨20410133948312943218621795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13606755965541962145747863 20410133948312943218621795)
                ·
                  refine ⟨30615200922469414827932693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410133948312943218621795 30615200922469414827932693)
                  ·
                    refine ⟨1435087543240753820059345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30615200922469414827932693 1435087543240753820059345)
                    ·
                      rfl

theorem cell23_8384469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_8384469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384469 prefixEnd_8384469 := by exact prefixLift 8384469
  have htrace : WordTrace (prefixWord ++ tailWord_8384469) baseStart_8384469 baseEnd_8384469 := by
    simpa [prefixWord, tailWord_8384469, baseEnd_8384469] using wordTrace_append hprefix tailTrace_8384469
  have hstable : (prefixWord ++ tailWord_8384469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384469).length < 2 ^ (prefixWord ++ tailWord_8384469).sum := by decide
  have hdescent : baseEnd_8384469 < baseStart_8384469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384479 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 3]
def baseStart_8384479 : Nat := 118140960795 + 8384479 * 2 ^ 59
def prefixEnd_8384479 : Nat := 4983230072969 + 3 ^ 40 * 8384479 * 2
def baseEnd_8384479 : Nat := 4305267764528806421052989

theorem tailTrace_8384479 : CollatzResearch.WordTrace tailWord_8384479 prefixEnd_8384479 4305267764528806421052989 := by
  unfold tailWord_8384479
  simp only [CollatzResearch.WordTrace]
  refine ⟨305807072191472012854548491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203871381460981341903032327 305807072191472012854548491)
  ·
    refine ⟨458710608287208019281822737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305807072191472012854548491 458710608287208019281822737)
    ·
      refine ⟨344032956215406014461367053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458710608287208019281822737 344032956215406014461367053)
      ·
        refine ⟨129012358580777255423012645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344032956215406014461367053 129012358580777255423012645)
        ·
          refine ⟨24189817233895735391814871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129012358580777255423012645 24189817233895735391814871)
          ·
            refine ⟨36284725850843603087722307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24189817233895735391814871 36284725850843603087722307)
            ·
              refine ⟨54427088776265404631583461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36284725850843603087722307 54427088776265404631583461)
              ·
                refine ⟨10205079145549763368421899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54427088776265404631583461 10205079145549763368421899)
                ·
                  refine ⟨15307618718324645052632849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10205079145549763368421899 15307618718324645052632849)
                  ·
                    refine ⟨11480714038743483789474637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15307618718324645052632849 11480714038743483789474637)
                    ·
                      refine ⟨4305267764528806421052989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11480714038743483789474637 4305267764528806421052989)
                      ·
                        rfl

theorem cell23_8384479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_8384479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384479 prefixEnd_8384479 := by exact prefixLift 8384479
  have htrace : WordTrace (prefixWord ++ tailWord_8384479) baseStart_8384479 baseEnd_8384479 := by
    simpa [prefixWord, tailWord_8384479, baseEnd_8384479] using wordTrace_append hprefix tailTrace_8384479
  have hstable : (prefixWord ++ tailWord_8384479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384479).length < 2 ^ (prefixWord ++ tailWord_8384479).sum := by decide
  have hdescent : baseEnd_8384479 < baseStart_8384479 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384492 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 3]
def baseStart_8384492 : Nat := 118140960795 + 8384492 * 2 ^ 59
def prefixEnd_8384492 : Nat := 4983230072969 + 3 ^ 40 * 8384492 * 2
def baseEnd_8384492 : Nat := 4305274439777314870190429

theorem tailTrace_8384492 : CollatzResearch.WordTrace tailWord_8384492 prefixEnd_8384492 4305274439777314870190429 := by
  unfold tailWord_8384492
  simp only [CollatzResearch.WordTrace]
  refine ⟨152903773170212458037385865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203871697560283277383181153 152903773170212458037385865)
  ·
    refine ⟨114677829877659343528039399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152903773170212458037385865 114677829877659343528039399)
    ·
      refine ⟨172016744816489015292059099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114677829877659343528039399 172016744816489015292059099)
      ·
        refine ⟨258025117224733522938088649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172016744816489015292059099 258025117224733522938088649)
        ·
          refine ⟨193518837918550142203566487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258025117224733522938088649 193518837918550142203566487)
          ·
            refine ⟨290278256877825213305349731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193518837918550142203566487 290278256877825213305349731)
            ·
              refine ⟨435417385316737819958024597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290278256877825213305349731 435417385316737819958024597)
              ·
                refine ⟨20410189936722085310532403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 435417385316737819958024597 20410189936722085310532403)
                ·
                  refine ⟨30615284905083127965798605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410189936722085310532403 30615284905083127965798605)
                  ·
                    refine ⟨11480731839406172987174477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30615284905083127965798605 11480731839406172987174477)
                    ·
                      refine ⟨4305274439777314870190429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11480731839406172987174477 4305274439777314870190429)
                      ·
                        rfl

theorem cell23_8384492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_8384492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384492 prefixEnd_8384492 := by exact prefixLift 8384492
  have htrace : WordTrace (prefixWord ++ tailWord_8384492) baseStart_8384492 baseEnd_8384492 := by
    simpa [prefixWord, tailWord_8384492, baseEnd_8384492] using wordTrace_append hprefix tailTrace_8384492
  have hstable : (prefixWord ++ tailWord_8384492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384492).length < 2 ^ (prefixWord ++ tailWord_8384492).sum := by decide
  have hdescent : baseEnd_8384492 < baseStart_8384492 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384509 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_8384509 : Nat := 118140960795 + 8384509 * 2 ^ 59
def prefixEnd_8384509 : Nat := 4983230072969 + 3 ^ 40 * 8384509 * 2
def baseEnd_8384509 : Nat := 4305283168948441303677851

theorem tailTrace_8384509 : CollatzResearch.WordTrace tailWord_8384509 prefixEnd_8384509 4305283168948441303677851 := by
  unfold tailWord_8384509
  simp only [CollatzResearch.WordTrace]
  refine ⟨305808166381363327978140581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203872110920908885318760387 305808166381363327978140581)
  ·
    refine ⟨57339031196505623995901359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305808166381363327978140581 57339031196505623995901359)
    ·
      refine ⟨86008546794758435993852039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57339031196505623995901359 86008546794758435993852039)
      ·
        refine ⟨129012820192137653990778059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86008546794758435993852039 129012820192137653990778059)
        ·
          refine ⟨193519230288206480986167089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129012820192137653990778059 193519230288206480986167089)
          ·
            refine ⟨145139422716154860739625317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193519230288206480986167089 145139422716154860739625317)
            ·
              refine ⟨27213641759279036388679747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145139422716154860739625317 27213641759279036388679747)
              ·
                refine ⟨40820462638918554583019621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27213641759279036388679747 40820462638918554583019621)
                ·
                  refine ⟨7653836744797228984316179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40820462638918554583019621 7653836744797228984316179)
                  ·
                    refine ⟨11480755117195843476474269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7653836744797228984316179 11480755117195843476474269)
                    ·
                      refine ⟨4305283168948441303677851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11480755117195843476474269 4305283168948441303677851)
                      ·
                        rfl

theorem cell23_8384509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_8384509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384509 prefixEnd_8384509 := by exact prefixLift 8384509
  have htrace : WordTrace (prefixWord ++ tailWord_8384509) baseStart_8384509 baseEnd_8384509 := by
    simpa [prefixWord, tailWord_8384509, baseEnd_8384509] using wordTrace_append hprefix tailTrace_8384509
  have hstable : (prefixWord ++ tailWord_8384509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384509).length < 2 ^ (prefixWord ++ tailWord_8384509).sum := by decide
  have hdescent : baseEnd_8384509 < baseStart_8384509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384510 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_8384510 : Nat := 118140960795 + 8384510 * 2 ^ 59
def prefixEnd_8384510 : Nat := 4983230072969 + 3 ^ 40 * 8384510 * 2
def baseEnd_8384510 : Nat := 4305283682429095799765347

theorem tailTrace_8384510 : CollatzResearch.WordTrace tailWord_8384510 prefixEnd_8384510 4305283682429095799765347 := by
  unfold tailWord_8384510
  simp only [CollatzResearch.WordTrace]
  refine ⟨38226025356794963143615873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203872135236239803432617989 38226025356794963143615873)
  ·
    refine ⟨28669519017596222357711905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38226025356794963143615873 28669519017596222357711905)
    ·
      refine ⟨21502139263197166768283929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28669519017596222357711905 21502139263197166768283929)
      ·
        refine ⟨16126604447397875076212947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21502139263197166768283929 16126604447397875076212947)
        ·
          refine ⟨24189906671096812614319421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126604447397875076212947 24189906671096812614319421)
          ·
            refine ⟨9071215001661304730369783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189906671096812614319421 9071215001661304730369783)
            ·
              refine ⟨13606822502491957095554675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071215001661304730369783 13606822502491957095554675)
              ·
                refine ⟨20410233753737935643332013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13606822502491957095554675 20410233753737935643332013)
                ·
                  refine ⟨7653837657651725866249505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20410233753737935643332013 7653837657651725866249505)
                  ·
                    refine ⟨5740378243238794399687129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653837657651725866249505 5740378243238794399687129)
                    ·
                      refine ⟨4305283682429095799765347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740378243238794399687129 4305283682429095799765347)
                      ·
                        rfl

theorem cell23_8384510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_8384510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384510 prefixEnd_8384510 := by exact prefixLift 8384510
  have htrace : WordTrace (prefixWord ++ tailWord_8384510) baseStart_8384510 baseEnd_8384510 := by
    simpa [prefixWord, tailWord_8384510, baseEnd_8384510] using wordTrace_append hprefix tailTrace_8384510
  have hstable : (prefixWord ++ tailWord_8384510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384510).length < 2 ^ (prefixWord ++ tailWord_8384510).sum := by decide
  have hdescent : baseEnd_8384510 < baseStart_8384510 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384526 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_8384526 : Nat := 118140960795 + 8384526 * 2 ^ 59
def prefixEnd_8384526 : Nat := 4983230072969 + 3 ^ 40 * 8384526 * 2
def baseEnd_8384526 : Nat := 4305291898119567737165273

theorem tailTrace_8384526 : CollatzResearch.WordTrace tailWord_8384526 prefixEnd_8384526 4305291898119567737165273 := by
  unfold tailWord_8384526
  simp only [CollatzResearch.WordTrace]
  refine ⟨38226098302787717485188679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203872524281534493254339621 38226098302787717485188679)
  ·
    refine ⟨57339147454181576227783019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38226098302787717485188679 57339147454181576227783019)
    ·
      refine ⟨86008721181272364341674529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57339147454181576227783019 86008721181272364341674529)
      ·
        refine ⟨64506540885954273256255897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86008721181272364341674529 64506540885954273256255897)
        ·
          refine ⟨48379905664465704942191923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64506540885954273256255897 48379905664465704942191923)
          ·
            refine ⟨72569858496698557413287885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48379905664465704942191923 72569858496698557413287885)
            ·
              refine ⟨27213696936261959029982957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72569858496698557413287885 27213696936261959029982957)
              ·
                refine ⟨10205136351098234636243609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27213696936261959029982957 10205136351098234636243609)
                ·
                  refine ⟨7653852263323675977182707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10205136351098234636243609 7653852263323675977182707)
                  ·
                    refine ⟨11480778394985513965774061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7653852263323675977182707 11480778394985513965774061)
                    ·
                      refine ⟨4305291898119567737165273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11480778394985513965774061 4305291898119567737165273)
                      ·
                        rfl

theorem cell23_8384526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_8384526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384526 prefixEnd_8384526 := by exact prefixLift 8384526
  have htrace : WordTrace (prefixWord ++ tailWord_8384526) baseStart_8384526 baseEnd_8384526 := by
    simpa [prefixWord, tailWord_8384526, baseEnd_8384526] using wordTrace_append hprefix tailTrace_8384526
  have hstable : (prefixWord ++ tailWord_8384526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384526).length < 2 ^ (prefixWord ++ tailWord_8384526).sum := by decide
  have hdescent : baseEnd_8384526 < baseStart_8384526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384549 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_8384549 : Nat := 118140960795 + 8384549 * 2 ^ 59
def prefixEnd_8384549 : Nat := 4983230072969 + 3 ^ 40 * 8384549 * 2
def baseEnd_8384549 : Nat := 4305303708174621147177667

theorem tailTrace_8384549 : CollatzResearch.WordTrace tailWord_8384549 prefixEnd_8384549 4305303708174621147177667 := by
  unfold tailWord_8384549
  simp only [CollatzResearch.WordTrace]
  refine ⟨305809625301218414809596701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203873083534145609873064467 305809625301218414809596701)
  ·
    refine ⟨114678609487956905553598763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305809625301218414809596701 114678609487956905553598763)
    ·
      refine ⟨172017914231935358330398145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114678609487956905553598763 172017914231935358330398145)
      ·
        refine ⟨129013435673951518747798609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172017914231935358330398145 129013435673951518747798609)
        ·
          refine ⟨96760076755463639060848957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129013435673951518747798609 96760076755463639060848957)
          ·
            refine ⟨36285028783298864647818359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96760076755463639060848957 36285028783298864647818359)
            ·
              refine ⟨54427543174948296971727539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36285028783298864647818359 54427543174948296971727539)
              ·
                refine ⟨81641314762422445457591309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54427543174948296971727539 81641314762422445457591309)
                ·
                  refine ⟨30615493035908417046596741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81641314762422445457591309 30615493035908417046596741)
                  ·
                    refine ⟨5740404944232828196236889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30615493035908417046596741 5740404944232828196236889)
                    ·
                      refine ⟨4305303708174621147177667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740404944232828196236889 4305303708174621147177667)
                      ·
                        rfl

theorem cell23_8384549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_8384549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384549 prefixEnd_8384549 := by exact prefixLift 8384549
  have htrace : WordTrace (prefixWord ++ tailWord_8384549) baseStart_8384549 baseEnd_8384549 := by
    simpa [prefixWord, tailWord_8384549, baseEnd_8384549] using wordTrace_append hprefix tailTrace_8384549
  have hstable : (prefixWord ++ tailWord_8384549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384549).length < 2 ^ (prefixWord ++ tailWord_8384549).sum := by decide
  have hdescent : baseEnd_8384549 < baseStart_8384549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384555 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 11]
def baseStart_8384555 : Nat := 118140960795 + 8384555 * 2 ^ 59
def prefixEnd_8384555 : Nat := 4983230072969 + 3 ^ 40 * 8384555 * 2
def baseEnd_8384555 : Nat := 478367421006505347078071

theorem tailTrace_8384555 : CollatzResearch.WordTrace tailWord_8384555 prefixEnd_8384555 478367421006505347078071 := by
  unfold tailWord_8384555
  simp only [CollatzResearch.WordTrace]
  refine ⟨305809844139196677834315119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203873229426131118556210079 305809844139196677834315119)
  ·
    refine ⟨458714766208795016751472679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305809844139196677834315119 458714766208795016751472679)
    ·
      refine ⟨688072149313192525127209019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458714766208795016751472679 688072149313192525127209019)
      ·
        refine ⟨1032108223969788787690813529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688072149313192525127209019 1032108223969788787690813529)
        ·
          refine ⟨774081167977341590768110147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032108223969788787690813529 774081167977341590768110147)
          ·
            refine ⟨1161121751966012386152165221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774081167977341590768110147 1161121751966012386152165221)
            ·
              refine ⟨217710328493627322403530979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1161121751966012386152165221 217710328493627322403530979)
              ·
                refine ⟨326565492740440983605296469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217710328493627322403530979 326565492740440983605296469)
                ·
                  refine ⟨478367421006505347078071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 326565492740440983605296469 478367421006505347078071)
                  ·
                    rfl

theorem cell23_8384555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 11].length) (baseStart_8384555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384555 prefixEnd_8384555 := by exact prefixLift 8384555
  have htrace : WordTrace (prefixWord ++ tailWord_8384555) baseStart_8384555 baseEnd_8384555 := by
    simpa [prefixWord, tailWord_8384555, baseEnd_8384555] using wordTrace_append hprefix tailTrace_8384555
  have hstable : (prefixWord ++ tailWord_8384555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384555).length < 2 ^ (prefixWord ++ tailWord_8384555).sum := by decide
  have hdescent : baseEnd_8384555 < baseStart_8384555 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384566 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_8384566 : Nat := 118140960795 + 8384566 * 2 ^ 59
def prefixEnd_8384566 : Nat := 4983230072969 + 3 ^ 40 * 8384566 * 2
def baseEnd_8384566 : Nat := 4305312437345747580665089

theorem tailTrace_8384566 : CollatzResearch.WordTrace tailWord_8384566 prefixEnd_8384566 4305312437345747580665089 := by
  unfold tailWord_8384566
  simp only [CollatzResearch.WordTrace]
  refine ⟨19113140333884801669560347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203873496894771217808643701 19113140333884801669560347)
  ·
    refine ⟨28669710500827202504340521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19113140333884801669560347 28669710500827202504340521)
    ·
      refine ⟨21502282875620401878255391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28669710500827202504340521 21502282875620401878255391)
      ·
        refine ⟨32253424313430602817383087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21502282875620401878255391 32253424313430602817383087)
        ·
          refine ⟨48380136470145904226074631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32253424313430602817383087 48380136470145904226074631)
          ·
            refine ⟨72570204705218856339111947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48380136470145904226074631 72570204705218856339111947)
            ·
              refine ⟨108855307057828284508667921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72570204705218856339111947 108855307057828284508667921)
              ·
                refine ⟨81641480293371213381500941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108855307057828284508667921 81641480293371213381500941)
                ·
                  refine ⟨30615555110014205018062853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81641480293371213381500941 30615555110014205018062853)
                  ·
                    refine ⟨5740416583127663440886785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30615555110014205018062853 5740416583127663440886785)
                    ·
                      refine ⟨4305312437345747580665089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740416583127663440886785 4305312437345747580665089)
                      ·
                        rfl

theorem cell23_8384566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_8384566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384566 prefixEnd_8384566 := by exact prefixLift 8384566
  have htrace : WordTrace (prefixWord ++ tailWord_8384566) baseStart_8384566 baseEnd_8384566 := by
    simpa [prefixWord, tailWord_8384566, baseEnd_8384566] using wordTrace_append hprefix tailTrace_8384566
  have hstable : (prefixWord ++ tailWord_8384566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384566).length < 2 ^ (prefixWord ++ tailWord_8384566).sum := by decide
  have hdescent : baseEnd_8384566 < baseStart_8384566 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384572 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 7]
def baseStart_8384572 : Nat := 118140960795 + 8384572 * 2 ^ 59
def prefixEnd_8384572 : Nat := 4983230072969 + 3 ^ 40 * 8384572 * 2
def baseEnd_8384572 : Nat := 478368390914408284132229

theorem tailTrace_8384572 : CollatzResearch.WordTrace tailWord_8384572 prefixEnd_8384572 478368390914408284132229 := by
  unfold tailWord_8384572
  simp only [CollatzResearch.WordTrace]
  refine ⟨152905232090067544868841985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203873642786756726491789313 152905232090067544868841985)
  ·
    refine ⟨114678924067550658651631489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152905232090067544868841985 114678924067550658651631489)
    ·
      refine ⟨86009193050662993988723617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114678924067550658651631489 86009193050662993988723617)
      ·
        refine ⟨64506894787997245491542713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86009193050662993988723617 64506894787997245491542713)
        ·
          refine ⟨48380171090997934118657035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64506894787997245491542713 48380171090997934118657035)
          ·
            refine ⟨72570256636496901177985553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48380171090997934118657035 72570256636496901177985553)
            ·
              refine ⟨54427692477372675883489165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72570256636496901177985553 54427692477372675883489165)
              ·
                refine ⟨20410384679014753456308437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54427692477372675883489165 20410384679014753456308437)
                ·
                  refine ⟨478368390914408284132229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20410384679014753456308437 478368390914408284132229)
                  ·
                    rfl

theorem cell23_8384572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_8384572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384572 prefixEnd_8384572 := by exact prefixLift 8384572
  have htrace : WordTrace (prefixWord ++ tailWord_8384572) baseStart_8384572 baseEnd_8384572 := by
    simpa [prefixWord, tailWord_8384572, baseEnd_8384572] using wordTrace_append hprefix tailTrace_8384572
  have hstable : (prefixWord ++ tailWord_8384572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384572).length < 2 ^ (prefixWord ++ tailWord_8384572).sum := by decide
  have hdescent : baseEnd_8384572 < baseStart_8384572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384589 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 7]
def baseStart_8384589 : Nat := 118140960795 + 8384589 * 2 ^ 59
def prefixEnd_8384589 : Nat := 4983230072969 + 3 ^ 40 * 8384589 * 2
def baseEnd_8384589 : Nat := 478369360822311221186387

theorem tailTrace_8384589 : CollatzResearch.WordTrace tailWord_8384589 prefixEnd_8384589 478369360822311221186387 := by
  unfold tailWord_8384589
  simp only [CollatzResearch.WordTrace]
  refine ⟨305811084221073501641052821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203874056147382334427368547 305811084221073501641052821)
  ·
    refine ⟨14334894572862820389424351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305811084221073501641052821 14334894572862820389424351)
    ·
      refine ⟨21502341859294230584136527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14334894572862820389424351 21502341859294230584136527)
      ·
        refine ⟨32253512788941345876204791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21502341859294230584136527 32253512788941345876204791)
        ·
          refine ⟨48380269183412018814307187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32253512788941345876204791 48380269183412018814307187)
          ·
            refine ⟨72570403775118028221460781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48380269183412018814307187 72570403775118028221460781)
            ·
              refine ⟨27213901415669260583047793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72570403775118028221460781 27213901415669260583047793)
              ·
                refine ⟨20410426061751945437285845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27213901415669260583047793 20410426061751945437285845)
                ·
                  refine ⟨478369360822311221186387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20410426061751945437285845 478369360822311221186387)
                  ·
                    rfl

theorem cell23_8384589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_8384589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384589 prefixEnd_8384589 := by exact prefixLift 8384589
  have htrace : WordTrace (prefixWord ++ tailWord_8384589) baseStart_8384589 baseEnd_8384589 := by
    simpa [prefixWord, tailWord_8384589, baseEnd_8384589] using wordTrace_append hprefix tailTrace_8384589
  have hstable : (prefixWord ++ tailWord_8384589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384589).length < 2 ^ (prefixWord ++ tailWord_8384589).sum := by decide
  have hdescent : baseEnd_8384589 < baseStart_8384589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384602 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_8384602 : Nat := 118140960795 + 8384602 * 2 ^ 59
def prefixEnd_8384602 : Nat := 4983230072969 + 3 ^ 40 * 8384602 * 2
def baseEnd_8384602 : Nat := 1435110307549769813271641

theorem tailTrace_8384602 : CollatzResearch.WordTrace tailWord_8384602 prefixEnd_8384602 1435110307549769813271641 := by
  unfold tailWord_8384602
  simp only [CollatzResearch.WordTrace]
  refine ⟨76452889592506601215319015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203874372246684269907517373 76452889592506601215319015)
  ·
    refine ⟨114679334388759901822978523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76452889592506601215319015 114679334388759901822978523)
    ·
      refine ⟨172019001583139852734467785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114679334388759901822978523 172019001583139852734467785)
      ·
        refine ⟨129014251187354889550850839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172019001583139852734467785 129014251187354889550850839)
        ·
          refine ⟨193521376781032334326276259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129014251187354889550850839 193521376781032334326276259)
          ·
            refine ⟨290282065171548501489414389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193521376781032334326276259 290282065171548501489414389)
            ·
              refine ⟨27213943609832672014632599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290282065171548501489414389 27213943609832672014632599)
              ·
                refine ⟨40820915414749008021948899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27213943609832672014632599 40820915414749008021948899)
                ·
                  refine ⟨61231373122123512032923349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40820915414749008021948899 61231373122123512032923349)
                  ·
                    refine ⟨1435110307549769813271641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61231373122123512032923349 1435110307549769813271641)
                    ·
                      rfl

theorem cell23_8384602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_8384602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384602 prefixEnd_8384602 := by exact prefixLift 8384602
  have htrace : WordTrace (prefixWord ++ tailWord_8384602) baseStart_8384602 baseEnd_8384602 := by
    simpa [prefixWord, tailWord_8384602, baseEnd_8384602] using wordTrace_append hprefix tailTrace_8384602
  have hstable : (prefixWord ++ tailWord_8384602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384602).length < 2 ^ (prefixWord ++ tailWord_8384602).sum := by decide
  have hdescent : baseEnd_8384602 < baseStart_8384602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384612 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_8384612 : Nat := 118140960795 + 8384612 * 2 ^ 59
def prefixEnd_8384612 : Nat := 4983230072969 + 3 ^ 40 * 8384612 * 2
def baseEnd_8384612 : Nat := 4305336057455854400689877

theorem tailTrace_8384612 : CollatzResearch.WordTrace tailWord_8384612 prefixEnd_8384612 4305336057455854400689877 := by
  unfold tailWord_8384612
  simp only [CollatzResearch.WordTrace]
  refine ⟨152905961549995088284570045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203874615399993451046093393 152905961549995088284570045)
  ·
    refine ⟨57339735581248158106713767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152905961549995088284570045 57339735581248158106713767)
    ·
      refine ⟨86009603371872237160070651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57339735581248158106713767 86009603371872237160070651)
      ·
        refine ⟨129014405057808355740105977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86009603371872237160070651 129014405057808355740105977)
        ·
          refine ⟨96760803793356266805079483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129014405057808355740105977 96760803793356266805079483)
          ·
            refine ⟨145141205690034400207619225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96760803793356266805079483 145141205690034400207619225)
            ·
              refine ⟨108855904267525800155714419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145141205690034400207619225 108855904267525800155714419)
              ·
                refine ⟨163283856401288700233571629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108855904267525800155714419 163283856401288700233571629)
                ·
                  refine ⟨61231446150483262587589361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163283856401288700233571629 61231446150483262587589361)
                  ·
                    refine ⟨45923584612862446940692021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61231446150483262587589361 45923584612862446940692021)
                    ·
                      refine ⟨4305336057455854400689877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45923584612862446940692021 4305336057455854400689877)
                      ·
                        rfl

theorem cell23_8384612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_8384612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384612 prefixEnd_8384612 := by exact prefixLift 8384612
  have htrace : WordTrace (prefixWord ++ tailWord_8384612) baseStart_8384612 baseEnd_8384612 := by
    simpa [prefixWord, tailWord_8384612, baseEnd_8384612] using wordTrace_append hprefix tailTrace_8384612
  have hstable : (prefixWord ++ tailWord_8384612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384612).length < 2 ^ (prefixWord ++ tailWord_8384612).sum := by decide
  have hdescent : baseEnd_8384612 < baseStart_8384612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384649 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_8384649 : Nat := 118140960795 + 8384649 * 2 ^ 59
def prefixEnd_8384649 : Nat := 4983230072969 + 3 ^ 40 * 8384649 * 2
def baseEnd_8384649 : Nat := 1435118352080023585309069

theorem tailTrace_8384649 : CollatzResearch.WordTrace tailWord_8384649 prefixEnd_8384649 1435118352080023585309069 := by
  unfold tailWord_8384649
  simp only [CollatzResearch.WordTrace]
  refine ⟨305813272600856131888237001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203875515067237421258824667 305813272600856131888237001)
  ·
    refine ⟨229359954450642098916177751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305813272600856131888237001 229359954450642098916177751)
    ·
      refine ⟨344039931675963148374266627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229359954450642098916177751 344039931675963148374266627)
      ·
        refine ⟨516059897513944722561399941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344039931675963148374266627 516059897513944722561399941)
        ·
          refine ⟨96761230783864635480262489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 516059897513944722561399941 96761230783864635480262489)
          ·
            refine ⟨72570923087898476610196867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96761230783864635480262489 72570923087898476610196867)
            ·
              refine ⟨108856384631847714915295301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72570923087898476610196867 108856384631847714915295301)
              ·
                refine ⟨20410572118471446546617869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108856384631847714915295301 20410572118471446546617869)
                ·
                  refine ⟨7653964544426792454981701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20410572118471446546617869 7653964544426792454981701)
                  ·
                    refine ⟨1435118352080023585309069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7653964544426792454981701 1435118352080023585309069)
                    ·
                      rfl

theorem cell23_8384649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_8384649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384649 prefixEnd_8384649 := by exact prefixLift 8384649
  have htrace : WordTrace (prefixWord ++ tailWord_8384649) baseStart_8384649 baseEnd_8384649 := by
    simpa [prefixWord, tailWord_8384649, baseEnd_8384649] using wordTrace_append hprefix tailTrace_8384649
  have hstable : (prefixWord ++ tailWord_8384649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384649).length < 2 ^ (prefixWord ++ tailWord_8384649).sum := by decide
  have hdescent : baseEnd_8384649 < baseStart_8384649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384659 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3]
def baseStart_8384659 : Nat := 118140960795 + 8384659 * 2 ^ 59
def prefixEnd_8384659 : Nat := 4983230072969 + 3 ^ 40 * 8384659 * 2
def baseEnd_8384659 : Nat := 4305360191046615716802161

theorem tailTrace_8384659 : CollatzResearch.WordTrace tailWord_8384659 prefixEnd_8384659 4305360191046615716802161 := by
  unfold tailWord_8384659
  simp only [CollatzResearch.WordTrace]
  refine ⟨305813637330819903596101031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203875758220546602397400687 305813637330819903596101031)
  ·
    refine ⟨458720455996229855394151547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305813637330819903596101031 458720455996229855394151547)
    ·
      refine ⟨688080683994344783091227321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458720455996229855394151547 688080683994344783091227321)
      ·
        refine ⟨516060512995758587318420491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688080683994344783091227321 516060512995758587318420491)
        ·
          refine ⟨774090769493637880977630737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516060512995758587318420491 774090769493637880977630737)
          ·
            refine ⟨580568077120228410733223053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774090769493637880977630737 580568077120228410733223053)
            ·
              refine ⟨217713028920085654024958645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580568077120228410733223053 217713028920085654024958645)
              ·
                refine ⟨20410596461258030064839873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217713028920085654024958645 20410596461258030064839873)
                ·
                  refine ⟨15307947345943522548629905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20410596461258030064839873 15307947345943522548629905)
                  ·
                    refine ⟨11480960509457641911472429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15307947345943522548629905 11480960509457641911472429)
                    ·
                      refine ⟨4305360191046615716802161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11480960509457641911472429 4305360191046615716802161)
                      ·
                        rfl

theorem cell23_8384659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_8384659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384659 prefixEnd_8384659 := by exact prefixLift 8384659
  have htrace : WordTrace (prefixWord ++ tailWord_8384659) baseStart_8384659 baseEnd_8384659 := by
    simpa [prefixWord, tailWord_8384659, baseEnd_8384659] using wordTrace_append hprefix tailTrace_8384659
  have hstable : (prefixWord ++ tailWord_8384659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384659).length < 2 ^ (prefixWord ++ tailWord_8384659).sum := by decide
  have hdescent : baseEnd_8384659 < baseStart_8384659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384776 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_8384776 : Nat := 118140960795 + 8384776 * 2 ^ 59
def prefixEnd_8384776 : Nat := 4983230072969 + 3 ^ 40 * 8384776 * 2
def baseEnd_8384776 : Nat := 4305420268283191759039123

theorem tailTrace_8384776 : CollatzResearch.WordTrace tailWord_8384776 prefixEnd_8384776 4305420268283191759039123 := by
  unfold tailWord_8384776
  simp only [CollatzResearch.WordTrace]
  refine ⟨152908952335698016289055091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203878603114264021718740121 152908952335698016289055091)
  ·
    refine ⟨229363428503547024433582637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152908952335698016289055091 229363428503547024433582637)
    ·
      refine ⟨86011285688830134162593489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229363428503547024433582637 86011285688830134162593489)
      ·
        refine ⟨64508464266622600621945117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86011285688830134162593489 64508464266622600621945117)
        ·
          refine ⟨24190674099983475233229419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64508464266622600621945117 24190674099983475233229419)
          ·
            refine ⟨36286011149975212849844129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24190674099983475233229419 36286011149975212849844129)
            ·
              refine ⟨27214508362481409637383097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36286011149975212849844129 27214508362481409637383097)
              ·
                refine ⟨20410881271861057228037323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27214508362481409637383097 20410881271861057228037323)
                ·
                  refine ⟨30616321907791585842055985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410881271861057228037323 30616321907791585842055985)
                  ·
                    refine ⟨22962241430843689381541989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30616321907791585842055985 22962241430843689381541989)
                    ·
                      refine ⟨4305420268283191759039123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22962241430843689381541989 4305420268283191759039123)
                      ·
                        rfl

theorem cell23_8384776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_8384776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384776 prefixEnd_8384776 := by exact prefixLift 8384776
  have htrace : WordTrace (prefixWord ++ tailWord_8384776) baseStart_8384776 baseEnd_8384776 := by
    simpa [prefixWord, tailWord_8384776, baseEnd_8384776] using wordTrace_append hprefix tailTrace_8384776
  have hstable : (prefixWord ++ tailWord_8384776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384776).length < 2 ^ (prefixWord ++ tailWord_8384776).sum := by decide
  have hdescent : baseEnd_8384776 < baseStart_8384776 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384797 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 3, 2, 2]
def baseStart_8384797 : Nat := 118140960795 + 8384797 * 2 ^ 59
def prefixEnd_8384797 : Nat := 4983230072969 + 3 ^ 40 * 8384797 * 2
def baseEnd_8384797 : Nat := 4305431051376936176876527

theorem tailTrace_8384797 : CollatzResearch.WordTrace tailWord_8384797 prefixEnd_8384797 4305431051376936176876527 := by
  unfold tailWord_8384797
  simp only [CollatzResearch.WordTrace]
  refine ⟨305818670604319953164624645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203879113736213302109749763 305818670604319953164624645)
  ·
    refine ⟨57341000738309991218367121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305818670604319953164624645 57341000738309991218367121)
    ·
      refine ⟨43005750553732493413775341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57341000738309991218367121 43005750553732493413775341)
      ·
        refine ⟨16127156457649685030165753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43005750553732493413775341 16127156457649685030165753)
        ·
          refine ⟨12095367343237263772624315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16127156457649685030165753 12095367343237263772624315)
          ·
            refine ⟨18143051014855895658936473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095367343237263772624315 18143051014855895658936473)
            ·
              refine ⟨13607288261141921744202355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18143051014855895658936473 13607288261141921744202355)
              ·
                refine ⟨20410932391712882616303533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607288261141921744202355 20410932391712882616303533)
                ·
                  refine ⟨7654099646892330981113825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20410932391712882616303533 7654099646892330981113825)
                  ·
                    refine ⟨5740574735169248235835369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7654099646892330981113825 5740574735169248235835369)
                    ·
                      refine ⟨4305431051376936176876527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740574735169248235835369 4305431051376936176876527)
                      ·
                        rfl

theorem cell23_8384797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_8384797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384797 prefixEnd_8384797 := by exact prefixLift 8384797
  have htrace : WordTrace (prefixWord ++ tailWord_8384797) baseStart_8384797 baseEnd_8384797 := by
    simpa [prefixWord, tailWord_8384797, baseEnd_8384797] using wordTrace_append hprefix tailTrace_8384797
  have hstable : (prefixWord ++ tailWord_8384797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384797).length < 2 ^ (prefixWord ++ tailWord_8384797).sum := by decide
  have hdescent : baseEnd_8384797 < baseStart_8384797 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384807 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 1, 6]
def baseStart_8384807 : Nat := 118140960795 + 8384807 * 2 ^ 59
def prefixEnd_8384807 : Nat := 4983230072969 + 3 ^ 40 * 8384807 * 2
def baseEnd_8384807 : Nat := 1435145395394493712583827

theorem tailTrace_8384807 : CollatzResearch.WordTrace tailWord_8384807 prefixEnd_8384807 1435145395394493712583827 := by
  unfold tailWord_8384807
  simp only [CollatzResearch.WordTrace]
  refine ⟨305819035334283724872488675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203879356889522483248325783 305819035334283724872488675)
  ·
    refine ⟨458728553001425587308733013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305819035334283724872488675 458728553001425587308733013)
    ·
      refine ⟨5375725230485456101274215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 458728553001425587308733013 5375725230485456101274215)
      ·
        refine ⟨8063587845728184151911323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375725230485456101274215 8063587845728184151911323)
        ·
          refine ⟨12095381768592276227866985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063587845728184151911323 12095381768592276227866985)
          ·
            refine ⟨9071536326444207170900239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095381768592276227866985 9071536326444207170900239)
            ·
              refine ⟨13607304489666310756350359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071536326444207170900239 13607304489666310756350359)
              ·
                refine ⟨20410956734499466134525539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607304489666310756350359 20410956734499466134525539)
                ·
                  refine ⟨30616435101749199201788309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410956734499466134525539 30616435101749199201788309)
                  ·
                    refine ⟨1435145395394493712583827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30616435101749199201788309 1435145395394493712583827)
                    ·
                      rfl

theorem cell23_8384807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_8384807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384807 prefixEnd_8384807 := by exact prefixLift 8384807
  have htrace : WordTrace (prefixWord ++ tailWord_8384807) baseStart_8384807 baseEnd_8384807 := by
    simpa [prefixWord, tailWord_8384807, baseEnd_8384807] using wordTrace_append hprefix tailTrace_8384807
  have hstable : (prefixWord ++ tailWord_8384807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384807).length < 2 ^ (prefixWord ++ tailWord_8384807).sum := by decide
  have hdescent : baseEnd_8384807 < baseStart_8384807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384810 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_8384810 : Nat := 118140960795 + 8384810 * 2 ^ 59
def prefixEnd_8384810 : Nat := 4983230072969 + 3 ^ 40 * 8384810 * 2
def baseEnd_8384810 : Nat := 4305437726625444626013967

theorem tailTrace_8384810 : CollatzResearch.WordTrace tailWord_8384810 prefixEnd_8384810 4305437726625444626013967 := by
  unfold tailWord_8384810
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454786188318214096211971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203879429835515237589898589 76454786188318214096211971)
  ·
    refine ⟨114682179282477321144317957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76454786188318214096211971 114682179282477321144317957)
    ·
      refine ⟨21502908615464497714559617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114682179282477321144317957 21502908615464497714559617)
      ·
        refine ⟨16127181461598373285919713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21502908615464497714559617 16127181461598373285919713)
        ·
          refine ⟨12095386096198779964439785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16127181461598373285919713 12095386096198779964439785)
          ·
            refine ⟨9071539572149084973329839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095386096198779964439785 9071539572149084973329839)
            ·
              refine ⟨13607309358223627459994759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071539572149084973329839 13607309358223627459994759)
              ·
                refine ⟨20410964037335441189992139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607309358223627459994759 20410964037335441189992139)
                ·
                  refine ⟨30616446056003161784988209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410964037335441189992139 30616446056003161784988209)
                  ·
                    refine ⟨22962334542002371338741157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30616446056003161784988209 22962334542002371338741157)
                    ·
                      refine ⟨4305437726625444626013967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22962334542002371338741157 4305437726625444626013967)
                      ·
                        rfl

theorem cell23_8384810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_8384810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384810 prefixEnd_8384810 := by exact prefixLift 8384810
  have htrace : WordTrace (prefixWord ++ tailWord_8384810) baseStart_8384810 baseEnd_8384810 := by
    simpa [prefixWord, tailWord_8384810, baseEnd_8384810] using wordTrace_append hprefix tailTrace_8384810
  have hstable : (prefixWord ++ tailWord_8384810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384810).length < 2 ^ (prefixWord ++ tailWord_8384810).sum := by decide
  have hdescent : baseEnd_8384810 < baseStart_8384810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384864 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3]
def baseStart_8384864 : Nat := 118140960795 + 8384864 * 2 ^ 59
def prefixEnd_8384864 : Nat := 4983230072969 + 3 ^ 40 * 8384864 * 2
def baseEnd_8384864 : Nat := 4305465454580787414738719

theorem tailTrace_8384864 : CollatzResearch.WordTrace tailWord_8384864 prefixEnd_8384864 4305465454580787414738719 := by
  unfold tailWord_8384864
  simp only [CollatzResearch.WordTrace]
  refine ⟨152910557147538611803656823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203880742863384815738209097 152910557147538611803656823)
  ·
    refine ⟨229365835721307917705485235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152910557147538611803656823 229365835721307917705485235)
    ·
      refine ⟨344048753581961876558227853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229365835721307917705485235 344048753581961876558227853)
      ·
        refine ⟨129018282593235703709335445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344048753581961876558227853 129018282593235703709335445)
        ·
          refine ⟨6047731996557923611375099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129018282593235703709335445 6047731996557923611375099)
          ·
            refine ⟨9071597994836885417062649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047731996557923611375099 9071597994836885417062649)
            ·
              refine ⟨6803698496127664062796987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9071597994836885417062649 6803698496127664062796987)
              ·
                refine ⟨10205547744191496094195481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803698496127664062796987 10205547744191496094195481)
                ·
                  refine ⟨7654160808143622070646611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10205547744191496094195481 7654160808143622070646611)
                  ·
                    refine ⟨11481241212215433105969917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654160808143622070646611 11481241212215433105969917)
                    ·
                      refine ⟨4305465454580787414738719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481241212215433105969917 4305465454580787414738719)
                      ·
                        rfl

theorem cell23_8384864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_8384864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384864 prefixEnd_8384864 := by exact prefixLift 8384864
  have htrace : WordTrace (prefixWord ++ tailWord_8384864) baseStart_8384864 baseEnd_8384864 := by
    simpa [prefixWord, tailWord_8384864, baseEnd_8384864] using wordTrace_append hprefix tailTrace_8384864
  have hstable : (prefixWord ++ tailWord_8384864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384864).length < 2 ^ (prefixWord ++ tailWord_8384864).sum := by decide
  have hdescent : baseEnd_8384864 < baseStart_8384864 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384910 : List Nat := [4, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_8384910 : Nat := 118140960795 + 8384910 * 2 ^ 59
def prefixEnd_8384910 : Nat := 4983230072969 + 3 ^ 40 * 8384910 * 2
def baseEnd_8384910 : Nat := 478387674965654914973723

theorem tailTrace_8384910 : CollatzResearch.WordTrace tailWord_8384910 prefixEnd_8384910 478387674965654914973723 := by
  unfold tailWord_8384910
  simp only [CollatzResearch.WordTrace]
  refine ⟨38227849006613821682936023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203881861368607048975658789 38227849006613821682936023)
  ·
    refine ⟨57341773509920732524404035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38227849006613821682936023 57341773509920732524404035)
    ·
      refine ⟨86012660264881098786606053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57341773509920732524404035 86012660264881098786606053)
      ·
        refine ⟨16127373799665206022488635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86012660264881098786606053 16127373799665206022488635)
        ·
          refine ⟨24191060699497809033732953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16127373799665206022488635 24191060699497809033732953)
          ·
            refine ⟨18143295524623356775299715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24191060699497809033732953 18143295524623356775299715)
            ·
              refine ⟨27214943286935035162949573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18143295524623356775299715 27214943286935035162949573)
              ·
                refine ⟨5102801866300319093053045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27214943286935035162949573 5102801866300319093053045)
                ·
                  refine ⟨478387674965654914973723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5102801866300319093053045 478387674965654914973723)
                  ·
                    rfl

theorem cell23_8384910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_8384910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384910 prefixEnd_8384910 := by exact prefixLift 8384910
  have htrace : WordTrace (prefixWord ++ tailWord_8384910) baseStart_8384910 baseEnd_8384910 := by
    simpa [prefixWord, tailWord_8384910, baseEnd_8384910] using wordTrace_append hprefix tailTrace_8384910
  have hstable : (prefixWord ++ tailWord_8384910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384910).length < 2 ^ (prefixWord ++ tailWord_8384910).sum := by decide
  have hdescent : baseEnd_8384910 < baseStart_8384910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384970 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_8384970 : Nat := 118140960795 + 8384970 * 2 ^ 59
def prefixEnd_8384970 : Nat := 4983230072969 + 3 ^ 40 * 8384970 * 2
def baseEnd_8384970 : Nat := 1435173294510054666671077

theorem tailTrace_8384970 : CollatzResearch.WordTrace tailWord_8384970 prefixEnd_8384970 1435173294510054666671077 := by
  unfold tailWord_8384970
  simp only [CollatzResearch.WordTrace]
  refine ⟨76456245108173300927668091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203883320288462135807114909 76456245108173300927668091)
  ·
    refine ⟨114684367662259951391502137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76456245108173300927668091 114684367662259951391502137)
    ·
      refine ⟨86013275746694963543626603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114684367662259951391502137 86013275746694963543626603)
      ·
        refine ⟨129019913620042445315439905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86013275746694963543626603 129019913620042445315439905)
        ·
          refine ⟨96764935215031833986579929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129019913620042445315439905 96764935215031833986579929)
          ·
            refine ⟨72573701411273875489934947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96764935215031833986579929 72573701411273875489934947)
            ·
              refine ⟨108860552116910813234902421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72573701411273875489934947 108860552116910813234902421)
              ·
                refine ⟨5102838380480194370386051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108860552116910813234902421 5102838380480194370386051)
                ·
                  refine ⟨7654257570720291555579077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102838380480194370386051 7654257570720291555579077)
                  ·
                    refine ⟨1435173294510054666671077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654257570720291555579077 1435173294510054666671077)
                    ·
                      rfl

theorem cell23_8384970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_8384970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384970 prefixEnd_8384970 := by exact prefixLift 8384970
  have htrace : WordTrace (prefixWord ++ tailWord_8384970) baseStart_8384970 baseEnd_8384970 := by
    simpa [prefixWord, tailWord_8384970, baseEnd_8384970] using wordTrace_append hprefix tailTrace_8384970
  have hstable : (prefixWord ++ tailWord_8384970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384970).length < 2 ^ (prefixWord ++ tailWord_8384970).sum := by decide
  have hdescent : baseEnd_8384970 < baseStart_8384970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384976 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_8384976 : Nat := 118140960795 + 8384976 * 2 ^ 59
def prefixEnd_8384976 : Nat := 4983230072969 + 3 ^ 40 * 8384976 * 2
def baseEnd_8384976 : Nat := 4305522964414090976538203

theorem tailTrace_8384976 : CollatzResearch.WordTrace tailWord_8384976 prefixEnd_8384976 4305522964414090976538203 := by
  unfold tailWord_8384976
  simp only [CollatzResearch.WordTrace]
  refine ⟨152912599635335733367695391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203883466180447644490260521 152912599635335733367695391)
  ·
    refine ⟨229368899453003600051543087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152912599635335733367695391 229368899453003600051543087)
    ·
      refine ⟨344053349179505400077314631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229368899453003600051543087 344053349179505400077314631)
      ·
        refine ⟨516080023769258100115971947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344053349179505400077314631 516080023769258100115971947)
        ·
          refine ⟨774120035653887150173957921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516080023769258100115971947 774120035653887150173957921)
          ·
            refine ⟨580590026740415362630468441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774120035653887150173957921 580590026740415362630468441)
            ·
              refine ⟨435442520055311521972851331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580590026740415362630468441 435442520055311521972851331)
              ·
                refine ⟨653163780082967282959276997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435442520055311521972851331 653163780082967282959276997)
                ·
                  refine ⟨122468208765556365554864437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 653163780082967282959276997 122468208765556365554864437)
                  ·
                    refine ⟨11481394571770909270768541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122468208765556365554864437 11481394571770909270768541)
                    ·
                      refine ⟨4305522964414090976538203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481394571770909270768541 4305522964414090976538203)
                      ·
                        rfl

theorem cell23_8384976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_8384976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384976 prefixEnd_8384976 := by exact prefixLift 8384976
  have htrace : WordTrace (prefixWord ++ tailWord_8384976) baseStart_8384976 baseEnd_8384976 := by
    simpa [prefixWord, tailWord_8384976, baseEnd_8384976] using wordTrace_append hprefix tailTrace_8384976
  have hstable : (prefixWord ++ tailWord_8384976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384976).length < 2 ^ (prefixWord ++ tailWord_8384976).sum := by decide
  have hdescent : baseEnd_8384976 < baseStart_8384976 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8384986 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_8384986 : Nat := 118140960795 + 8384986 * 2 ^ 59
def prefixEnd_8384986 : Nat := 4983230072969 + 3 ^ 40 * 8384986 * 2
def baseEnd_8384986 : Nat := 4305528099220635937413157

theorem tailTrace_8384986 : CollatzResearch.WordTrace tailWord_8384986 prefixEnd_8384986 4305528099220635937413157 := by
  unfold tailWord_8384986
  simp only [CollatzResearch.WordTrace]
  refine ⟨76456391000158809610813703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203883709333756825628836541 76456391000158809610813703)
  ·
    refine ⟨114684586500238214416220555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76456391000158809610813703 114684586500238214416220555)
    ·
      refine ⟨172026879750357321624330833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114684586500238214416220555 172026879750357321624330833)
      ·
        refine ⟨129020159812767991218248125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172026879750357321624330833 129020159812767991218248125)
        ·
          refine ⟨48382559929787996706843047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129020159812767991218248125 48382559929787996706843047)
          ·
            refine ⟨72573839894681995060264571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48382559929787996706843047 72573839894681995060264571)
            ·
              refine ⟨108860759842022992590396857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72573839894681995060264571 108860759842022992590396857)
              ·
                refine ⟨81645569881517244442797643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108860759842022992590396857 81645569881517244442797643)
                ·
                  refine ⟨122468354822275866664196465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81645569881517244442797643 122468354822275866664196465)
                  ·
                    refine ⟨91851266116706899998147349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122468354822275866664196465 91851266116706899998147349)
                    ·
                      refine ⟨4305528099220635937413157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91851266116706899998147349 4305528099220635937413157)
                      ·
                        rfl

theorem cell23_8384986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_8384986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8384986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8384986 prefixEnd_8384986 := by exact prefixLift 8384986
  have htrace : WordTrace (prefixWord ++ tailWord_8384986) baseStart_8384986 baseEnd_8384986 := by
    simpa [prefixWord, tailWord_8384986, baseEnd_8384986] using wordTrace_append hprefix tailTrace_8384986
  have hstable : (prefixWord ++ tailWord_8384986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8384986).length < 2 ^ (prefixWord ++ tailWord_8384986).sum := by decide
  have hdescent : baseEnd_8384986 < baseStart_8384986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8384986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385003 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 5, 2]
def baseStart_8385003 : Nat := 118140960795 + 8385003 * 2 ^ 59
def prefixEnd_8385003 : Nat := 4983230072969 + 3 ^ 40 * 8385003 * 2
def baseEnd_8385003 : Nat := 4305536828391762370900579

theorem tailTrace_8385003 : CollatzResearch.WordTrace tailWord_8385003 prefixEnd_8385003 4305536828391762370900579 := by
  unfold tailWord_8385003
  simp only [CollatzResearch.WordTrace]
  refine ⟨305826184041573650346623663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203884122694382433564415775 305826184041573650346623663)
  ·
    refine ⟨458739276062360475519935495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305826184041573650346623663 458739276062360475519935495)
    ·
      refine ⟨688108914093540713279903243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458739276062360475519935495 688108914093540713279903243)
      ·
        refine ⟨1032163371140311069919854865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688108914093540713279903243 1032163371140311069919854865)
        ·
          refine ⟨774122528355233302439891149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032163371140311069919854865 774122528355233302439891149)
          ·
            refine ⟨290295948133212488414959181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774122528355233302439891149 290295948133212488414959181)
            ·
              refine ⟨108860980549954683155609693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290295948133212488414959181 108860980549954683155609693)
              ·
                refine ⟨40822867706233006183353635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108860980549954683155609693 40822867706233006183353635)
                ·
                  refine ⟨61234301559349509275030453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40822867706233006183353635 61234301559349509275030453)
                  ·
                    refine ⟨5740715771189016494534105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61234301559349509275030453 5740715771189016494534105)
                    ·
                      refine ⟨4305536828391762370900579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740715771189016494534105 4305536828391762370900579)
                      ·
                        rfl

theorem cell23_8385003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5, 2].length) (baseStart_8385003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385003 prefixEnd_8385003 := by exact prefixLift 8385003
  have htrace : WordTrace (prefixWord ++ tailWord_8385003) baseStart_8385003 baseEnd_8385003 := by
    simpa [prefixWord, tailWord_8385003, baseEnd_8385003] using wordTrace_append hprefix tailTrace_8385003
  have hstable : (prefixWord ++ tailWord_8385003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385003).length < 2 ^ (prefixWord ++ tailWord_8385003).sum := by decide
  have hdescent : baseEnd_8385003 < baseStart_8385003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385033 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 6, 2]
def baseStart_8385033 : Nat := 118140960795 + 8385033 * 2 ^ 59
def prefixEnd_8385033 : Nat := 4983230072969 + 3 ^ 40 * 8385033 * 2
def baseEnd_8385033 : Nat := 4305552232811397253525441

theorem tailTrace_8385033 : CollatzResearch.WordTrace tailWord_8385033 prefixEnd_8385033 4305552232811397253525441 := by
  unfold tailWord_8385033
  simp only [CollatzResearch.WordTrace]
  refine ⟨305827278231464965470215753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203884852154309976980143835 305827278231464965470215753)
  ·
    refine ⟨229370458673598724102661815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305827278231464965470215753 229370458673598724102661815)
    ·
      refine ⟨344055688010398086153992723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229370458673598724102661815 344055688010398086153992723)
      ·
        refine ⟨516083532015597129230989085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344055688010398086153992723 516083532015597129230989085)
        ·
          refine ⟨193531324505848923461620907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516083532015597129230989085 193531324505848923461620907)
          ·
            refine ⟨290296986758773385192431361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193531324505848923461620907 290296986758773385192431361)
            ·
              refine ⟨217722740069080038894323521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290296986758773385192431361 217722740069080038894323521)
              ·
                refine ⟨163292055051810029170742641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217722740069080038894323521 163292055051810029170742641)
                ·
                  refine ⟨122469041288857521878056981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163292055051810029170742641 122469041288857521878056981)
                  ·
                    refine ⟨5740736310415196338033921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122469041288857521878056981 5740736310415196338033921)
                    ·
                      refine ⟨4305552232811397253525441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740736310415196338033921 4305552232811397253525441)
                      ·
                        rfl

theorem cell23_8385033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6, 2].length) (baseStart_8385033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385033 prefixEnd_8385033 := by exact prefixLift 8385033
  have htrace : WordTrace (prefixWord ++ tailWord_8385033) baseStart_8385033 baseEnd_8385033 := by
    simpa [prefixWord, tailWord_8385033, baseEnd_8385033] using wordTrace_append hprefix tailTrace_8385033
  have hstable : (prefixWord ++ tailWord_8385033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385033).length < 2 ^ (prefixWord ++ tailWord_8385033).sum := by decide
  have hdescent : baseEnd_8385033 < baseStart_8385033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385050 : List Nat := [3, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4]
def baseStart_8385050 : Nat := 118140960795 + 8385050 * 2 ^ 59
def prefixEnd_8385050 : Nat := 4983230072969 + 3 ^ 40 * 8385050 * 2
def baseEnd_8385050 : Nat := 4305560961982523687012863

theorem tailTrace_8385050 : CollatzResearch.WordTrace tailWord_8385050 prefixEnd_8385050 4305560961982523687012863 := by
  unfold tailWord_8385050
  simp only [CollatzResearch.WordTrace]
  refine ⟨76456974568100844343396151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203885265514935584915723069 76456974568100844343396151)
  ·
    refine ⟨114685461852151266515094227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76456974568100844343396151 114685461852151266515094227)
    ·
      refine ⟨172028192778226899772641341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114685461852151266515094227 172028192778226899772641341)
      ·
        refine ⟨64510572291835087414740503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172028192778226899772641341 64510572291835087414740503)
        ·
          refine ⟨96765858437752631122110755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64510572291835087414740503 96765858437752631122110755)
          ·
            refine ⟨145148787656628946683166133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96765858437752631122110755 145148787656628946683166133)
            ·
              refine ⟨13607698842808963751546825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145148787656628946683166133 13607698842808963751546825)
              ·
                refine ⟨10205774132106722813660119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13607698842808963751546825 10205774132106722813660119)
                ·
                  refine ⟨15308661198160084220490179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10205774132106722813660119 15308661198160084220490179)
                  ·
                    refine ⟨22962991797240126330735269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15308661198160084220490179 22962991797240126330735269)
                    ·
                      refine ⟨4305560961982523687012863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22962991797240126330735269 4305560961982523687012863)
                      ·
                        rfl

theorem cell23_8385050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_8385050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385050 prefixEnd_8385050 := by exact prefixLift 8385050
  have htrace : WordTrace (prefixWord ++ tailWord_8385050) baseStart_8385050 baseEnd_8385050 := by
    simpa [prefixWord, tailWord_8385050, baseEnd_8385050] using wordTrace_append hprefix tailTrace_8385050
  have hstable : (prefixWord ++ tailWord_8385050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385050).length < 2 ^ (prefixWord ++ tailWord_8385050).sum := by decide
  have hdescent : baseEnd_8385050 < baseStart_8385050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385078 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_8385078 : Nat := 118140960795 + 8385078 * 2 ^ 59
def prefixEnd_8385078 : Nat := 4983230072969 + 3 ^ 40 * 8385078 * 2
def baseEnd_8385078 : Nat := 4305575339440849577462735

theorem tailTrace_8385078 : CollatzResearch.WordTrace tailWord_8385078 prefixEnd_8385078 4305575339440849577462735 := by
  unfold tailWord_8385078
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114307469768871134725243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203885946344201292103735925 19114307469768871134725243)
  ·
    refine ⟨28671461204653306702087865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19114307469768871134725243 28671461204653306702087865)
    ·
      refine ⟨21503595903489980026565899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28671461204653306702087865 21503595903489980026565899)
      ·
        refine ⟨32255393855234970039848849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21503595903489980026565899 32255393855234970039848849)
        ·
          refine ⟨24191545391426227529886637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32255393855234970039848849 24191545391426227529886637)
          ·
            refine ⟨9071829521784835323707489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24191545391426227529886637 9071829521784835323707489)
            ·
              refine ⟨6803872141338626492780617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9071829521784835323707489 6803872141338626492780617)
              ·
                refine ⟨5102904106003969869585463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803872141338626492780617 5102904106003969869585463)
                ·
                  refine ⟨7654356159005954804378195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102904106003969869585463 7654356159005954804378195)
                  ·
                    refine ⟨11481534238508932206567293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654356159005954804378195 11481534238508932206567293)
                    ·
                      refine ⟨4305575339440849577462735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481534238508932206567293 4305575339440849577462735)
                      ·
                        rfl

theorem cell23_8385078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_8385078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385078 prefixEnd_8385078 := by exact prefixLift 8385078
  have htrace : WordTrace (prefixWord ++ tailWord_8385078) baseStart_8385078 baseEnd_8385078 := by
    simpa [prefixWord, tailWord_8385078, baseEnd_8385078] using wordTrace_append hprefix tailTrace_8385078
  have hstable : (prefixWord ++ tailWord_8385078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385078).length < 2 ^ (prefixWord ++ tailWord_8385078).sum := by decide
  have hdescent : baseEnd_8385078 < baseStart_8385078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385094 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_8385094 : Nat := 118140960795 + 8385094 * 2 ^ 59
def prefixEnd_8385094 : Nat := 4983230072969 + 3 ^ 40 * 8385094 * 2
def baseEnd_8385094 : Nat := 1435194518377107171620887

theorem tailTrace_8385094 : CollatzResearch.WordTrace tailWord_8385094 prefixEnd_8385094 1435194518377107171620887 := by
  unfold tailWord_8385094
  simp only [CollatzResearch.WordTrace]
  refine ⟨9557171971382624152755823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203886335389495981925457557 9557171971382624152755823)
  ·
    refine ⟨14335757957073936229133735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9557171971382624152755823 14335757957073936229133735)
    ·
      refine ⟨21503636935610904343700603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14335757957073936229133735 21503636935610904343700603)
      ·
        refine ⟨32255455403416356515550905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21503636935610904343700603 32255455403416356515550905)
        ·
          refine ⟨24191591552562267386663179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32255455403416356515550905 24191591552562267386663179)
          ·
            refine ⟨36287387328843401079994769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24191591552562267386663179 36287387328843401079994769)
            ·
              refine ⟨27215540496632550809996077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36287387328843401079994769 27215540496632550809996077)
              ·
                refine ⟨10205827686237206553748529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27215540496632550809996077 10205827686237206553748529)
                ·
                  refine ⟨7654370764677904915311397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10205827686237206553748529 7654370764677904915311397)
                  ·
                    refine ⟨1435194518377107171620887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7654370764677904915311397 1435194518377107171620887)
                    ·
                      rfl

theorem cell23_8385094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_8385094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385094 prefixEnd_8385094 := by exact prefixLift 8385094
  have htrace : WordTrace (prefixWord ++ tailWord_8385094) baseStart_8385094 baseEnd_8385094 := by
    simpa [prefixWord, tailWord_8385094, baseEnd_8385094] using wordTrace_append hprefix tailTrace_8385094
  have hstable : (prefixWord ++ tailWord_8385094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385094).length < 2 ^ (prefixWord ++ tailWord_8385094).sum := by decide
  have hdescent : baseEnd_8385094 < baseStart_8385094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385100 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 1, 3, 3]
def baseStart_8385100 : Nat := 118140960795 + 8385100 * 2 ^ 59
def prefixEnd_8385100 : Nat := 4983230072969 + 3 ^ 40 * 8385100 * 2
def baseEnd_8385100 : Nat := 4305586636015248491387633

theorem tailTrace_8385100 : CollatzResearch.WordTrace tailWord_8385100 prefixEnd_8385100 4305586636015248491387633 := by
  unfold tailWord_8385100
  simp only [CollatzResearch.WordTrace]
  refine ⟨152914860961111117956452377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203886481281481490608603169 152914860961111117956452377)
  ·
    refine ⟨114686145720833338467339283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152914860961111117956452377 114686145720833338467339283)
    ·
      refine ⟨172029218581250007701008925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114686145720833338467339283 172029218581250007701008925)
      ·
        refine ⟨64510956967968752887878347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172029218581250007701008925 64510956967968752887878347)
        ·
          refine ⟨96766435451953129331817521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64510956967968752887878347 96766435451953129331817521)
          ·
            refine ⟨72574826588964846998863141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96766435451953129331817521 72574826588964846998863141)
            ·
              refine ⟨13607779985430908812286839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72574826588964846998863141 13607779985430908812286839)
              ·
                refine ⟨20411669978146363218430259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607779985430908812286839 20411669978146363218430259)
                ·
                  refine ⟨30617504967219544827645389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20411669978146363218430259 30617504967219544827645389)
                  ·
                    refine ⟨11481564362707329310367021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30617504967219544827645389 11481564362707329310367021)
                    ·
                      refine ⟨4305586636015248491387633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481564362707329310367021 4305586636015248491387633)
                      ·
                        rfl

theorem cell23_8385100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_8385100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385100 prefixEnd_8385100 := by exact prefixLift 8385100
  have htrace : WordTrace (prefixWord ++ tailWord_8385100) baseStart_8385100 baseEnd_8385100 := by
    simpa [prefixWord, tailWord_8385100, baseEnd_8385100] using wordTrace_append hprefix tailTrace_8385100
  have hstable : (prefixWord ++ tailWord_8385100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385100).length < 2 ^ (prefixWord ++ tailWord_8385100).sum := by decide
  have hdescent : baseEnd_8385100 < baseStart_8385100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385134 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_8385134 : Nat := 118140960795 + 8385134 * 2 ^ 59
def prefixEnd_8385134 : Nat := 4983230072969 + 3 ^ 40 * 8385134 * 2
def baseEnd_8385134 : Nat := 4305604094357501358362477

theorem tailTrace_8385134 : CollatzResearch.WordTrace tailWord_8385134 prefixEnd_8385134 4305604094357501358362477 := by
  unfold tailWord_8385134
  simp only [CollatzResearch.WordTrace]
  refine ⟨38228870250512382464955307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203887308002732706479761637 38228870250512382464955307)
  ·
    refine ⟨57343305375768573697432961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38228870250512382464955307 57343305375768573697432961)
    ·
      refine ⟨43007479031826430273074721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57343305375768573697432961 43007479031826430273074721)
      ·
        refine ⟨32255609273869822704806041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43007479031826430273074721 32255609273869822704806041)
        ·
          refine ⟨24191706955402367028604531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32255609273869822704806041 24191706955402367028604531)
          ·
            refine ⟨36287560433103550542906797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24191706955402367028604531 36287560433103550542906797)
            ·
              refine ⟨13607835162413831453590049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36287560433103550542906797 13607835162413831453590049)
              ·
                refine ⟨10205876371810373590192537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13607835162413831453590049 10205876371810373590192537)
                ·
                  refine ⟨7654407278857780192644403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10205876371810373590192537 7654407278857780192644403)
                  ·
                    refine ⟨11481610918286670288966605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654407278857780192644403 11481610918286670288966605)
                    ·
                      refine ⟨4305604094357501358362477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481610918286670288966605 4305604094357501358362477)
                      ·
                        rfl

theorem cell23_8385134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_8385134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385134 prefixEnd_8385134 := by exact prefixLift 8385134
  have htrace : WordTrace (prefixWord ++ tailWord_8385134) baseStart_8385134 baseEnd_8385134 := by
    simpa [prefixWord, tailWord_8385134, baseEnd_8385134] using wordTrace_append hprefix tailTrace_8385134
  have hstable : (prefixWord ++ tailWord_8385134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385134).length < 2 ^ (prefixWord ++ tailWord_8385134).sum := by decide
  have hdescent : baseEnd_8385134 < baseStart_8385134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385143 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3]
def baseStart_8385143 : Nat := 118140960795 + 8385143 * 2 ^ 59
def prefixEnd_8385143 : Nat := 4983230072969 + 3 ^ 40 * 8385143 * 2
def baseEnd_8385143 : Nat := 4305608715683391823149935

theorem tailTrace_8385143 : CollatzResearch.WordTrace tailWord_8385143 prefixEnd_8385143 4305608715683391823149935 := by
  unfold tailWord_8385143
  simp only [CollatzResearch.WordTrace]
  refine ⟨305831290261066454256720083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203887526840710969504480055 305831290261066454256720083)
  ·
    refine ⟨458746935391599681385080125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305831290261066454256720083 458746935391599681385080125)
    ·
      refine ⟨172030100771849880519405047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458746935391599681385080125 172030100771849880519405047)
      ·
        refine ⟨258045151157774820779107571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172030100771849880519405047 258045151157774820779107571)
        ·
          refine ⟨387067726736662231168661357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258045151157774820779107571 387067726736662231168661357)
          ·
            refine ⟨145150397526248336688248009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387067726736662231168661357 145150397526248336688248009)
            ·
              refine ⟨108862798144686252516186007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145150397526248336688248009 108862798144686252516186007)
              ·
                refine ⟨163294197217029378774279011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108862798144686252516186007 163294197217029378774279011)
                ·
                  refine ⟨244941295825544068161418517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163294197217029378774279011 244941295825544068161418517)
                  ·
                    refine ⟨11481623241822378195066493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 244941295825544068161418517 11481623241822378195066493)
                    ·
                      refine ⟨4305608715683391823149935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481623241822378195066493 4305608715683391823149935)
                      ·
                        rfl

theorem cell23_8385143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_8385143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385143 prefixEnd_8385143 := by exact prefixLift 8385143
  have htrace : WordTrace (prefixWord ++ tailWord_8385143) baseStart_8385143 baseEnd_8385143 := by
    simpa [prefixWord, tailWord_8385143, baseEnd_8385143] using wordTrace_append hprefix tailTrace_8385143
  have hstable : (prefixWord ++ tailWord_8385143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385143).length < 2 ^ (prefixWord ++ tailWord_8385143).sum := by decide
  have hdescent : baseEnd_8385143 < baseStart_8385143 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385157 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_8385157 : Nat := 118140960795 + 8385157 * 2 ^ 59
def prefixEnd_8385157 : Nat := 4983230072969 + 3 ^ 40 * 8385157 * 2
def baseEnd_8385157 : Nat := 4305615904412554768374871

theorem tailTrace_8385157 : CollatzResearch.WordTrace tailWord_8385157 prefixEnd_8385157 4305615904412554768374871 := by
  unfold tailWord_8385157
  simp only [CollatzResearch.WordTrace]
  refine ⟨305831800883015734647729725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203887867255343823098486483 305831800883015734647729725)
  ·
    refine ⟨114686925331130900492898647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305831800883015734647729725 114686925331130900492898647)
    ·
      refine ⟨172030387996696350739347971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114686925331130900492898647 172030387996696350739347971)
      ·
        refine ⟨258045581995044526109021957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172030387996696350739347971 258045581995044526109021957)
        ·
          refine ⟨48383546624070848645441617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258045581995044526109021957 48383546624070848645441617)
          ·
            refine ⟨36287659968053136484081213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48383546624070848645441617 36287659968053136484081213)
            ·
              refine ⟨13607872488019926181530455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36287659968053136484081213 13607872488019926181530455)
              ·
                refine ⟨20411808732029889272295683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607872488019926181530455 20411808732029889272295683)
                ·
                  refine ⟨30617713098044833908443525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20411808732029889272295683 30617713098044833908443525)
                  ·
                    refine ⟨5740821205883406357833161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30617713098044833908443525 5740821205883406357833161)
                    ·
                      refine ⟨4305615904412554768374871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740821205883406357833161 4305615904412554768374871)
                      ·
                        rfl

theorem cell23_8385157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_8385157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385157 prefixEnd_8385157 := by exact prefixLift 8385157
  have htrace : WordTrace (prefixWord ++ tailWord_8385157) baseStart_8385157 baseEnd_8385157 := by
    simpa [prefixWord, tailWord_8385157, baseEnd_8385157] using wordTrace_append hprefix tailTrace_8385157
  have hstable : (prefixWord ++ tailWord_8385157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385157).length < 2 ^ (prefixWord ++ tailWord_8385157).sum := by decide
  have hdescent : baseEnd_8385157 < baseStart_8385157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385193 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_8385193 : Nat := 118140960795 + 8385193 * 2 ^ 59
def prefixEnd_8385193 : Nat := 4983230072969 + 3 ^ 40 * 8385193 * 2
def baseEnd_8385193 : Nat := 1435211463238705542508235

theorem tailTrace_8385193 : CollatzResearch.WordTrace tailWord_8385193 prefixEnd_8385193 1435211463238705542508235 := by
  unfold tailWord_8385193
  simp only [CollatzResearch.WordTrace]
  refine ⟨305833113910885312796040233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203888742607256875197360155 305833113910885312796040233)
  ·
    refine ⟨229374835433163984597030175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305833113910885312796040233 229374835433163984597030175)
    ·
      refine ⟨344062253149745976895545263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229374835433163984597030175 344062253149745976895545263)
      ·
        refine ⟨516093379724618965343317895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344062253149745976895545263 516093379724618965343317895)
        ·
          refine ⟨774140069586928448014976843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516093379724618965343317895 774140069586928448014976843)
          ·
            refine ⟨1161210104380392672022465265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774140069586928448014976843 1161210104380392672022465265)
            ·
              refine ⟨870907578285294504016848949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161210104380392672022465265 870907578285294504016848949)
              ·
                refine ⟨81647585464246359751579589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 870907578285294504016848949 81647585464246359751579589)
                ·
                  refine ⟨15308922274546192453421173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81647585464246359751579589 15308922274546192453421173)
                  ·
                    refine ⟨1435211463238705542508235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15308922274546192453421173 1435211463238705542508235)
                    ·
                      rfl

theorem cell23_8385193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_8385193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385193 prefixEnd_8385193 := by exact prefixLift 8385193
  have htrace : WordTrace (prefixWord ++ tailWord_8385193) baseStart_8385193 baseEnd_8385193 := by
    simpa [prefixWord, tailWord_8385193, baseEnd_8385193] using wordTrace_append hprefix tailTrace_8385193
  have hstable : (prefixWord ++ tailWord_8385193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385193).length < 2 ^ (prefixWord ++ tailWord_8385193).sum := by decide
  have hdescent : baseEnd_8385193 < baseStart_8385193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385197 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 7]
def baseStart_8385197 : Nat := 118140960795 + 8385197 * 2 ^ 59
def prefixEnd_8385197 : Nat := 4983230072969 + 3 ^ 40 * 8385197 * 2
def baseEnd_8385197 : Nat := 478404049293192734652743

theorem tailTrace_8385197 : CollatzResearch.WordTrace tailWord_8385197 prefixEnd_8385197 478404049293192734652743 := by
  unfold tailWord_8385197
  simp only [CollatzResearch.WordTrace]
  refine ⟨305833259802870821479185845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203888839868580547652790563 305833259802870821479185845)
  ·
    refine ⟨28671868106519139513673673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305833259802870821479185845 28671868106519139513673673)
    ·
      refine ⟨21503901079889354635255255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28671868106519139513673673 21503901079889354635255255)
      ·
        refine ⟨32255851619834031952882883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21503901079889354635255255 32255851619834031952882883)
        ·
          refine ⟨48383777429751047929324325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32255851619834031952882883 48383777429751047929324325)
          ·
            refine ⟨9071958268078321486748311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48383777429751047929324325 9071958268078321486748311)
            ·
              refine ⟨13607937402117482230122467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071958268078321486748311 13607937402117482230122467)
              ·
                refine ⟨20411906103176223345183701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607937402117482230122467 20411906103176223345183701)
                ·
                  refine ⟨478404049293192734652743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20411906103176223345183701 478404049293192734652743)
                  ·
                    rfl

theorem cell23_8385197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_8385197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385197 prefixEnd_8385197 := by exact prefixLift 8385197
  have htrace : WordTrace (prefixWord ++ tailWord_8385197) baseStart_8385197 baseEnd_8385197 := by
    simpa [prefixWord, tailWord_8385197, baseEnd_8385197] using wordTrace_append hprefix tailTrace_8385197
  have hstable : (prefixWord ++ tailWord_8385197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385197).length < 2 ^ (prefixWord ++ tailWord_8385197).sum := by decide
  have hdescent : baseEnd_8385197 < baseStart_8385197 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385200 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2]
def baseStart_8385200 : Nat := 118140960795 + 8385200 * 2 ^ 59
def prefixEnd_8385200 : Nat := 4983230072969 + 3 ^ 40 * 8385200 * 2
def baseEnd_8385200 : Nat := 4305637984080698100137173

theorem tailTrace_8385200 : CollatzResearch.WordTrace tailWord_8385200 prefixEnd_8385200 4305637984080698100137173 := by
  unfold tailWord_8385200
  simp only [CollatzResearch.WordTrace]
  refine ⟨152916684610929976495772527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203888912814573301994363369 152916684610929976495772527)
  ·
    refine ⟨229375026916394964743658791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152916684610929976495772527 229375026916394964743658791)
    ·
      refine ⟨344062540374592447115488187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229375026916394964743658791 344062540374592447115488187)
      ·
        refine ⟨516093810561888670673232281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344062540374592447115488187 516093810561888670673232281)
        ·
          refine ⟨387070357921416503004924211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516093810561888670673232281 387070357921416503004924211)
          ·
            refine ⟨580605536882124754507386317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387070357921416503004924211 580605536882124754507386317)
            ·
              refine ⟨217727076330796782940269869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580605536882124754507386317 217727076330796782940269869)
              ·
                refine ⟨81647653624048793602601201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217727076330796782940269869 81647653624048793602601201)
                ·
                  refine ⟨61235740218036595201950901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81647653624048793602601201 61235740218036595201950901)
                  ·
                    refine ⟨5740850645440930800182897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61235740218036595201950901 5740850645440930800182897)
                    ·
                      refine ⟨4305637984080698100137173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5740850645440930800182897 4305637984080698100137173)
                      ·
                        rfl

theorem cell23_8385200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2].length) (baseStart_8385200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385200 prefixEnd_8385200 := by exact prefixLift 8385200
  have htrace : WordTrace (prefixWord ++ tailWord_8385200) baseStart_8385200 baseEnd_8385200 := by
    simpa [prefixWord, tailWord_8385200, baseEnd_8385200] using wordTrace_append hprefix tailTrace_8385200
  have hstable : (prefixWord ++ tailWord_8385200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385200).length < 2 ^ (prefixWord ++ tailWord_8385200).sum := by decide
  have hdescent : baseEnd_8385200 < baseStart_8385200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385203 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7]
def baseStart_8385203 : Nat := 118140960795 + 8385203 * 2 ^ 59
def prefixEnd_8385203 : Nat := 4983230072969 + 3 ^ 40 * 8385203 * 2
def baseEnd_8385203 : Nat := 4305639524522661588399659

theorem tailTrace_8385203 : CollatzResearch.WordTrace tailWord_8385203 prefixEnd_8385203 4305639524522661588399659 := by
  unfold tailWord_8385203
  simp only [CollatzResearch.WordTrace]
  refine ⟨305833478640849084503904263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203888985760566056335936175 305833478640849084503904263)
  ·
    refine ⟨458750217961273626755856395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305833478640849084503904263 458750217961273626755856395)
    ·
      refine ⟨688125326941910440133784593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458750217961273626755856395 688125326941910440133784593)
      ·
        refine ⟨516093995206432830100338445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688125326941910440133784593 516093995206432830100338445)
        ·
          refine ⟨193535248202412311287626917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516093995206432830100338445 193535248202412311287626917)
          ·
            refine ⟨36287859037952308366430047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193535248202412311287626917 36287859037952308366430047)
            ·
              refine ⟨54431788556928462549645071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36287859037952308366430047 54431788556928462549645071)
              ·
                refine ⟨81647682835392693824467607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54431788556928462549645071 81647682835392693824467607)
                ·
                  refine ⟨122471524253089040736701411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81647682835392693824467607 122471524253089040736701411)
                  ·
                    refine ⟨183707286379633561105052117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122471524253089040736701411 183707286379633561105052117)
                    ·
                      refine ⟨4305639524522661588399659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183707286379633561105052117 4305639524522661588399659)
                      ·
                        rfl

theorem cell23_8385203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 7].length) (baseStart_8385203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385203 prefixEnd_8385203 := by exact prefixLift 8385203
  have htrace : WordTrace (prefixWord ++ tailWord_8385203) baseStart_8385203 baseEnd_8385203 := by
    simpa [prefixWord, tailWord_8385203, baseEnd_8385203] using wordTrace_append hprefix tailTrace_8385203
  have hstable : (prefixWord ++ tailWord_8385203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385203).length < 2 ^ (prefixWord ++ tailWord_8385203).sum := by decide
  have hdescent : baseEnd_8385203 < baseStart_8385203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385243 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4]
def baseStart_8385243 : Nat := 118140960795 + 8385243 * 2 ^ 59
def prefixEnd_8385243 : Nat := 4983230072969 + 3 ^ 40 * 8385243 * 2
def baseEnd_8385243 : Nat := 4305660063748841431899475

theorem tailTrace_8385243 : CollatzResearch.WordTrace tailWord_8385243 prefixEnd_8385243 4305660063748841431899475 := by
  unfold tailWord_8385243
  simp only [CollatzResearch.WordTrace]
  refine ⟨305834937560704171335360383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203889958373802780890240255 305834937560704171335360383)
  ·
    refine ⟨458752406341056257003040575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305834937560704171335360383 458752406341056257003040575)
    ·
      refine ⟨688128609511584385504560863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458752406341056257003040575 688128609511584385504560863)
      ·
        refine ⟨1032192914267376578256841295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688128609511584385504560863 1032192914267376578256841295)
        ·
          refine ⟨1548289371401064867385261943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032192914267376578256841295 1548289371401064867385261943)
          ·
            refine ⟨2322434057101597301077892915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548289371401064867385261943 2322434057101597301077892915)
            ·
              refine ⟨3483651085652395951616839373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2322434057101597301077892915 3483651085652395951616839373)
              ·
                refine ⟨1306369157119648481856314765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3483651085652395951616839373 1306369157119648481856314765)
                ·
                  refine ⟨489888433919868180696118037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1306369157119648481856314765 489888433919868180696118037)
                  ·
                    refine ⟨22963520339993820970130533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 489888433919868180696118037 22963520339993820970130533)
                    ·
                      refine ⟨4305660063748841431899475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22963520339993820970130533 4305660063748841431899475)
                      ·
                        rfl

theorem cell23_8385243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 4].length) (baseStart_8385243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385243 prefixEnd_8385243 := by exact prefixLift 8385243
  have htrace : WordTrace (prefixWord ++ tailWord_8385243) baseStart_8385243 baseEnd_8385243 := by
    simpa [prefixWord, tailWord_8385243, baseEnd_8385243] using wordTrace_append hprefix tailTrace_8385243
  have hstable : (prefixWord ++ tailWord_8385243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385243).length < 2 ^ (prefixWord ++ tailWord_8385243).sum := by decide
  have hdescent : baseEnd_8385243 < baseStart_8385243 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385314 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_8385314 : Nat := 118140960795 + 8385314 * 2 ^ 59
def prefixEnd_8385314 : Nat := 4983230072969 + 3 ^ 40 * 8385314 * 2
def baseEnd_8385314 : Nat := 4305696520875310654111649

theorem tailTrace_8385314 : CollatzResearch.WordTrace tailWord_8385314 prefixEnd_8385314 4305696520875310654111649 := by
  unfold tailWord_8385314
  simp only [CollatzResearch.WordTrace]
  refine ⟨76459381785861737615298749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203891684762297966974129997 76459381785861737615298749)
  ·
    refine ⟨28672268169698151605737031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76459381785861737615298749 28672268169698151605737031)
    ·
      refine ⟨43008402254547227408605547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28672268169698151605737031 43008402254547227408605547)
      ·
        refine ⟨64512603381820841112908321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43008402254547227408605547 64512603381820841112908321)
        ·
          refine ⟨48384452536365630834681241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64512603381820841112908321 48384452536365630834681241)
          ·
            refine ⟨36288339402274223126010931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48384452536365630834681241 36288339402274223126010931)
            ·
              refine ⟨54432509103411334689016397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36288339402274223126010931 54432509103411334689016397)
              ·
                refine ⟨20412190913779250508381149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54432509103411334689016397 20412190913779250508381149)
                ·
                  refine ⟨7654571592667218940642931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20412190913779250508381149 7654571592667218940642931)
                  ·
                    refine ⟨11481857389000828410964397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654571592667218940642931 11481857389000828410964397)
                    ·
                      refine ⟨4305696520875310654111649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11481857389000828410964397 4305696520875310654111649)
                      ·
                        rfl

theorem cell23_8385314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_8385314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385314 prefixEnd_8385314 := by exact prefixLift 8385314
  have htrace : WordTrace (prefixWord ++ tailWord_8385314) baseStart_8385314 baseEnd_8385314 := by
    simpa [prefixWord, tailWord_8385314, baseEnd_8385314] using wordTrace_append hprefix tailTrace_8385314
  have hstable : (prefixWord ++ tailWord_8385314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385314).length < 2 ^ (prefixWord ++ tailWord_8385314).sum := by decide
  have hdescent : baseEnd_8385314 < baseStart_8385314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385340 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_8385340 : Nat := 118140960795 + 8385340 * 2 ^ 59
def prefixEnd_8385340 : Nat := 4983230072969 + 3 ^ 40 * 8385340 * 2
def baseEnd_8385340 : Nat := 4305709871372327552386529

theorem tailTrace_8385340 : CollatzResearch.WordTrace tailWord_8385340 prefixEnd_8385340 4305709871372327552386529 := by
  unfold tailWord_8385340
  simp only [CollatzResearch.WordTrace]
  refine ⟨152919237720676378450820737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203892316960901837934427649 152919237720676378450820737)
  ·
    refine ⟨114689428290507283838115553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152919237720676378450820737 114689428290507283838115553)
    ·
      refine ⟨86017071217880462878586665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114689428290507283838115553 86017071217880462878586665)
      ·
        refine ⟨64512803413410347158939999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86017071217880462878586665 64512803413410347158939999)
        ·
          refine ⟨96769205120115520738409999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64512803413410347158939999 96769205120115520738409999)
          ·
            refine ⟨145153807680173281107614999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96769205120115520738409999 145153807680173281107614999)
            ·
              refine ⟨217730711520259921661422499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145153807680173281107614999 217730711520259921661422499)
              ·
                refine ⟨326596067280389882492133749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217730711520259921661422499 326596067280389882492133749)
                ·
                  refine ⟨30618381307536551483637539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326596067280389882492133749 30618381307536551483637539)
                  ·
                    refine ⟨45927571961304827225456309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30618381307536551483637539 45927571961304827225456309)
                    ·
                      refine ⟨4305709871372327552386529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45927571961304827225456309 4305709871372327552386529)
                      ·
                        rfl

theorem cell23_8385340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_8385340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385340 prefixEnd_8385340 := by exact prefixLift 8385340
  have htrace : WordTrace (prefixWord ++ tailWord_8385340) baseStart_8385340 baseEnd_8385340 := by
    simpa [prefixWord, tailWord_8385340, baseEnd_8385340] using wordTrace_append hprefix tailTrace_8385340
  have hstable : (prefixWord ++ tailWord_8385340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385340).length < 2 ^ (prefixWord ++ tailWord_8385340).sum := by decide
  have hdescent : baseEnd_8385340 < baseStart_8385340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385400 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_8385400 : Nat := 118140960795 + 8385400 * 2 ^ 59
def prefixEnd_8385400 : Nat := 4983230072969 + 3 ^ 40 * 8385400 * 2
def baseEnd_8385400 : Nat := 4305740680211597317636253

theorem tailTrace_8385400 : CollatzResearch.WordTrace tailWord_8385400 prefixEnd_8385400 4305740680211597317636253 := by
  unfold tailWord_8385400
  simp only [CollatzResearch.WordTrace]
  refine ⟨152920331910567693574412827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203893775880756924765883769 152920331910567693574412827)
  ·
    refine ⟨229380497865851540361619241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152920331910567693574412827 229380497865851540361619241)
    ·
      refine ⟨172035373399388655271214431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229380497865851540361619241 172035373399388655271214431)
      ·
        refine ⟨258053060099082982906821647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172035373399388655271214431 258053060099082982906821647)
        ·
          refine ⟨387079590148624474360232471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258053060099082982906821647 387079590148624474360232471)
          ·
            refine ⟨580619385222936711540348707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387079590148624474360232471 580619385222936711540348707)
            ·
              refine ⟨870929077834405067310523061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580619385222936711540348707 870929077834405067310523061)
              ·
                refine ⟨81649601046975475060361537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 870929077834405067310523061 81649601046975475060361537)
                ·
                  refine ⟨61237200785231606295271153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81649601046975475060361537 61237200785231606295271153)
                  ·
                    refine ⟨45927900588923704721453365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61237200785231606295271153 45927900588923704721453365)
                    ·
                      refine ⟨4305740680211597317636253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45927900588923704721453365 4305740680211597317636253)
                      ·
                        rfl

theorem cell23_8385400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_8385400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385400 prefixEnd_8385400 := by exact prefixLift 8385400
  have htrace : WordTrace (prefixWord ++ tailWord_8385400) baseStart_8385400 baseEnd_8385400 := by
    simpa [prefixWord, tailWord_8385400, baseEnd_8385400] using wordTrace_append hprefix tailTrace_8385400
  have hstable : (prefixWord ++ tailWord_8385400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385400).length < 2 ^ (prefixWord ++ tailWord_8385400).sum := by decide
  have hdescent : baseEnd_8385400 < baseStart_8385400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385437 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_8385437 : Nat := 118140960795 + 8385437 * 2 ^ 59
def prefixEnd_8385437 : Nat := 4983230072969 + 3 ^ 40 * 8385437 * 2
def baseEnd_8385437 : Nat := 1435253226331937890957861

theorem tailTrace_8385437 : CollatzResearch.WordTrace tailWord_8385437 prefixEnd_8385437 1435253226331937890957861 := by
  unfold tailWord_8385437
  simp only [CollatzResearch.WordTrace]
  refine ⟨305842013322001342467922565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203894675548000894978615043 305842013322001342467922565)
  ·
    refine ⟨57345377497875251712735481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305842013322001342467922565 57345377497875251712735481)
    ·
      refine ⟨43009033123406438784551611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57345377497875251712735481 43009033123406438784551611)
      ·
        refine ⟨64513549685109658176827417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43009033123406438784551611 64513549685109658176827417)
        ·
          refine ⟨48385162263832243632620563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64513549685109658176827417 48385162263832243632620563)
          ·
            refine ⟨72577743395748365448930845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48385162263832243632620563 72577743395748365448930845)
            ·
              refine ⟨27216653773405637043349067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72577743395748365448930845 27216653773405637043349067)
              ·
                refine ⟨40824980660108455565023601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27216653773405637043349067 40824980660108455565023601)
                ·
                  refine ⟨30618735495081341673767701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40824980660108455565023601 30618735495081341673767701)
                  ·
                    refine ⟨1435253226331937890957861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30618735495081341673767701 1435253226331937890957861)
                    ·
                      rfl

theorem cell23_8385437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_8385437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385437 prefixEnd_8385437 := by exact prefixLift 8385437
  have htrace : WordTrace (prefixWord ++ tailWord_8385437) baseStart_8385437 baseEnd_8385437 := by
    simpa [prefixWord, tailWord_8385437, baseEnd_8385437] using wordTrace_append hprefix tailTrace_8385437
  have hstable : (prefixWord ++ tailWord_8385437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385437).length < 2 ^ (prefixWord ++ tailWord_8385437).sum := by decide
  have hdescent : baseEnd_8385437 < baseStart_8385437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385461 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_8385461 : Nat := 118140960795 + 8385461 * 2 ^ 59
def prefixEnd_8385461 : Nat := 4983230072969 + 3 ^ 40 * 8385461 * 2
def baseEnd_8385461 : Nat := 4305772002531521578973473

theorem tailTrace_8385461 : CollatzResearch.WordTrace tailWord_8385461 prefixEnd_8385461 4305772002531521578973473 := by
  unfold tailWord_8385461
  simp only [CollatzResearch.WordTrace]
  refine ⟨305842888673914394566796237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203895259115942929711197491 305842888673914394566796237)
  ·
    refine ⟨114691083252717897962548589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305842888673914394566796237 114691083252717897962548589)
    ·
      refine ⟨43009156219769211735955721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114691083252717897962548589 43009156219769211735955721)
      ·
        refine ⟨32256867164826908801966791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43009156219769211735955721 32256867164826908801966791)
        ·
          refine ⟨48385300747240363202950187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32256867164826908801966791 48385300747240363202950187)
          ·
            refine ⟨72577951120860544804425281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48385300747240363202950187 72577951120860544804425281)
            ·
              refine ⟨54433463340645408603318961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72577951120860544804425281 54433463340645408603318961)
              ·
                refine ⟨40825097505484056452489221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54433463340645408603318961 40825097505484056452489221)
                ·
                  refine ⟨7654705782278260584841729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40825097505484056452489221 7654705782278260584841729)
                  ·
                    refine ⟨5741029336708695438631297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7654705782278260584841729 5741029336708695438631297)
                    ·
                      refine ⟨4305772002531521578973473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741029336708695438631297 4305772002531521578973473)
                      ·
                        rfl

theorem cell23_8385461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_8385461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385461 prefixEnd_8385461 := by exact prefixLift 8385461
  have htrace : WordTrace (prefixWord ++ tailWord_8385461) baseStart_8385461 baseEnd_8385461 := by
    simpa [prefixWord, tailWord_8385461, baseEnd_8385461] using wordTrace_append hprefix tailTrace_8385461
  have hstable : (prefixWord ++ tailWord_8385461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385461).length < 2 ^ (prefixWord ++ tailWord_8385461).sum := by decide
  have hdescent : baseEnd_8385461 < baseStart_8385461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385484 : List Nat := [2, 2, 1, 4, 1, 1, 1, 6, 5]
def baseStart_8385484 : Nat := 118140960795 + 8385484 * 2 ^ 59
def prefixEnd_8385484 : Nat := 4983230072969 + 3 ^ 40 * 8385484 * 2
def baseEnd_8385484 : Nat := 478420423620730554331763

theorem tailTrace_8385484 : CollatzResearch.WordTrace tailWord_8385484 prefixEnd_8385484 478420423620730554331763 := by
  unfold tailWord_8385484
  simp only [CollatzResearch.WordTrace]
  refine ⟨152921863776415534747441753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203895818368554046329922337 152921863776415534747441753)
  ·
    refine ⟨114691397832311651060581315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152921863776415534747441753 114691397832311651060581315)
    ·
      refine ⟨172037096748467476590871973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114691397832311651060581315 172037096748467476590871973)
      ·
        refine ⟨32256955640337651860788495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172037096748467476590871973 32256955640337651860788495)
        ·
          refine ⟨48385433460506477791182743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32256955640337651860788495 48385433460506477791182743)
          ·
            refine ⟨72578150190759716686774115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48385433460506477791182743 72578150190759716686774115)
            ·
              refine ⟨108867225286139575030161173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72578150190759716686774115 108867225286139575030161173)
              ·
                refine ⟨5103151185287792579538805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108867225286139575030161173 5103151185287792579538805)
                ·
                  refine ⟨478420423620730554331763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5103151185287792579538805 478420423620730554331763)
                  ·
                    rfl

theorem cell23_8385484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 6, 5].length) (baseStart_8385484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385484 prefixEnd_8385484 := by exact prefixLift 8385484
  have htrace : WordTrace (prefixWord ++ tailWord_8385484) baseStart_8385484 baseEnd_8385484 := by
    simpa [prefixWord, tailWord_8385484, baseEnd_8385484] using wordTrace_append hprefix tailTrace_8385484
  have hstable : (prefixWord ++ tailWord_8385484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385484).length < 2 ^ (prefixWord ++ tailWord_8385484).sum := by decide
  have hdescent : baseEnd_8385484 < baseStart_8385484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385497 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_8385497 : Nat := 118140960795 + 8385497 * 2 ^ 59
def prefixEnd_8385497 : Nat := 4983230072969 + 3 ^ 40 * 8385497 * 2
def baseEnd_8385497 : Nat := 1435263495945027812707769

theorem tailTrace_8385497 : CollatzResearch.WordTrace tailWord_8385497 prefixEnd_8385497 1435263495945027812707769 := by
  unfold tailWord_8385497
  simp only [CollatzResearch.WordTrace]
  refine ⟨305844201701783972715106745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203896134467855981810071163 305844201701783972715106745)
  ·
    refine ⟨229383151276337979536330059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305844201701783972715106745 229383151276337979536330059)
    ·
      refine ⟨344074726914506969304495089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229383151276337979536330059 344074726914506969304495089)
      ·
        refine ⟨258056045185880226978371317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344074726914506969304495089 258056045185880226978371317)
        ·
          refine ⟨24192754236176271279222311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258056045185880226978371317 24192754236176271279222311)
          ·
            refine ⟨36289131354264406918833467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24192754236176271279222311 36289131354264406918833467)
            ·
              refine ⟨54433697031396610378250201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36289131354264406918833467 54433697031396610378250201)
              ·
                refine ⟨40825272773547457783687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54433697031396610378250201 40825272773547457783687651)
                ·
                  refine ⟨61237909160321186675531477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40825272773547457783687651 61237909160321186675531477)
                  ·
                    refine ⟨1435263495945027812707769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61237909160321186675531477 1435263495945027812707769)
                    ·
                      rfl

theorem cell23_8385497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_8385497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385497 prefixEnd_8385497 := by exact prefixLift 8385497
  have htrace : WordTrace (prefixWord ++ tailWord_8385497) baseStart_8385497 baseEnd_8385497 := by
    simpa [prefixWord, tailWord_8385497, baseEnd_8385497] using wordTrace_append hprefix tailTrace_8385497
  have hstable : (prefixWord ++ tailWord_8385497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385497).length < 2 ^ (prefixWord ++ tailWord_8385497).sum := by decide
  have hdescent : baseEnd_8385497 < baseStart_8385497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385518 : List Nat := [4, 1, 2, 1, 4, 2, 1, 3, 5]
def baseStart_8385518 : Nat := 118140960795 + 8385518 * 2 ^ 59
def prefixEnd_8385518 : Nat := 4983230072969 + 3 ^ 40 * 8385518 * 2
def baseEnd_8385518 : Nat := 478422363436536428440079

theorem tailTrace_8385518 : CollatzResearch.WordTrace tailWord_8385518 prefixEnd_8385518 478422363436536428440079 := by
  unfold tailWord_8385518
  simp only [CollatzResearch.WordTrace]
  refine ⟨38230620954338486662702651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203896645089805262201080805 38230620954338486662702651)
  ·
    refine ⟨57345931431507729994053977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38230620954338486662702651 57345931431507729994053977)
    ·
      refine ⟨43009448573630797495540483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57345931431507729994053977 43009448573630797495540483)
      ·
        refine ⟨64514172860446196243310725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43009448573630797495540483 64514172860446196243310725)
        ·
          refine ⟨12096407411333661795620761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64514172860446196243310725 12096407411333661795620761)
          ·
            refine ⟨9072305558500246346715571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12096407411333661795620761 9072305558500246346715571)
            ·
              refine ⟨13608458337750369520073357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072305558500246346715571 13608458337750369520073357)
              ·
                refine ⟨5103171876656388570027509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13608458337750369520073357 5103171876656388570027509)
                ·
                  refine ⟨478422363436536428440079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5103171876656388570027509 478422363436536428440079)
                  ·
                    rfl

theorem cell23_8385518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_8385518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385518 prefixEnd_8385518 := by exact prefixLift 8385518
  have htrace : WordTrace (prefixWord ++ tailWord_8385518) baseStart_8385518 baseEnd_8385518 := by
    simpa [prefixWord, tailWord_8385518, baseEnd_8385518] using wordTrace_append hprefix tailTrace_8385518
  have hstable : (prefixWord ++ tailWord_8385518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385518).length < 2 ^ (prefixWord ++ tailWord_8385518).sum := by decide
  have hdescent : baseEnd_8385518 < baseStart_8385518 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385568 : List Nat := [2, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8385568 : Nat := 118140960795 + 8385568 * 2 ^ 59
def prefixEnd_8385568 : Nat := 4983230072969 + 3 ^ 40 * 8385568 * 2
def baseEnd_8385568 : Nat := 4305826944961552660335481

theorem tailTrace_8385568 : CollatzResearch.WordTrace tailWord_8385568 prefixEnd_8385568 4305826944961552660335481 := by
  unfold tailWord_8385568
  simp only [CollatzResearch.WordTrace]
  refine ⟨152923395642263375920470679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203897860856351167893960905 152923395642263375920470679)
  ·
    refine ⟨229385093463395063880706019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152923395642263375920470679 229385093463395063880706019)
    ·
      refine ⟨344077640195092595821059029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229385093463395063880706019 344077640195092595821059029)
      ·
        refine ⟨8064319692072482714556071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 344077640195092595821059029 8064319692072482714556071)
        ·
          refine ⟨12096479538108724071834107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064319692072482714556071 12096479538108724071834107)
          ·
            refine ⟨18144719307163086107751161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096479538108724071834107 18144719307163086107751161)
            ·
              refine ⟨13608539480372314580813371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18144719307163086107751161 13608539480372314580813371)
              ·
                refine ⟨20412809220558471871220057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608539480372314580813371 20412809220558471871220057)
                ·
                  refine ⟨15309606915418853903415043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20412809220558471871220057 15309606915418853903415043)
                  ·
                    refine ⟨22964410373128280855122565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15309606915418853903415043 22964410373128280855122565)
                    ·
                      refine ⟨4305826944961552660335481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22964410373128280855122565 4305826944961552660335481)
                      ·
                        rfl

theorem cell23_8385568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8385568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385568 prefixEnd_8385568 := by exact prefixLift 8385568
  have htrace : WordTrace (prefixWord ++ tailWord_8385568) baseStart_8385568 baseEnd_8385568 := by
    simpa [prefixWord, tailWord_8385568, baseEnd_8385568] using wordTrace_append hprefix tailTrace_8385568
  have hstable : (prefixWord ++ tailWord_8385568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385568).length < 2 ^ (prefixWord ++ tailWord_8385568).sum := by decide
  have hdescent : baseEnd_8385568 < baseStart_8385568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385571 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3]
def baseStart_8385571 : Nat := 118140960795 + 8385571 * 2 ^ 59
def prefixEnd_8385571 : Nat := 4983230072969 + 3 ^ 40 * 8385571 * 2
def baseEnd_8385571 : Nat := 4305828485403516148597967

theorem tailTrace_8385571 : CollatzResearch.WordTrace tailWord_8385571 prefixEnd_8385571 4305828485403516148597967 := by
  unfold tailWord_8385571
  simp only [CollatzResearch.WordTrace]
  refine ⟨305846900703515883353300567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203897933802343922235533711 305846900703515883353300567)
  ·
    refine ⟨458770351055273825029950851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305846900703515883353300567 458770351055273825029950851)
    ·
      refine ⟨688155526582910737544926277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458770351055273825029950851 688155526582910737544926277)
      ·
        refine ⟨129029161234295763289673677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 688155526582910737544926277 129029161234295763289673677)
        ·
          refine ⟨48385935462860911233627629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129029161234295763289673677 48385935462860911233627629)
          ·
            refine ⟨18144725798572841712610361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48385935462860911233627629 18144725798572841712610361)
            ·
              refine ⟨13608544348929631284457771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18144725798572841712610361 13608544348929631284457771)
              ·
                refine ⟨20412816523394446926686657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608544348929631284457771 20412816523394446926686657)
                ·
                  refine ⟨15309612392545835195014993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20412816523394446926686657 15309612392545835195014993)
                  ·
                    refine ⟨11482209294409376396261245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15309612392545835195014993 11482209294409376396261245)
                    ·
                      refine ⟨4305828485403516148597967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482209294409376396261245 4305828485403516148597967)
                      ·
                        rfl

theorem cell23_8385571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_8385571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385571 prefixEnd_8385571 := by exact prefixLift 8385571
  have htrace : WordTrace (prefixWord ++ tailWord_8385571) baseStart_8385571 baseEnd_8385571 := by
    simpa [prefixWord, tailWord_8385571, baseEnd_8385571] using wordTrace_append hprefix tailTrace_8385571
  have hstable : (prefixWord ++ tailWord_8385571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385571).length < 2 ^ (prefixWord ++ tailWord_8385571).sum := by decide
  have hdescent : baseEnd_8385571 < baseStart_8385571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385588 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_8385588 : Nat := 118140960795 + 8385588 * 2 ^ 59
def prefixEnd_8385588 : Nat := 4983230072969 + 3 ^ 40 * 8385588 * 2
def baseEnd_8385588 : Nat := 4305837214574642582085389

theorem tailTrace_8385588 : CollatzResearch.WordTrace tailWord_8385588 prefixEnd_8385588 4305837214574642582085389 := by
  unfold tailWord_8385588
  simp only [CollatzResearch.WordTrace]
  refine ⟨152923760372227147628334709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203898347162969530171112945 152923760372227147628334709)
  ·
    refine ⟨14336602534896295090156379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152923760372227147628334709 14336602534896295090156379)
    ·
      refine ⟨21504903802344442635234569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14336602534896295090156379 21504903802344442635234569)
      ·
        refine ⟨16128677851758331976425927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21504903802344442635234569 16128677851758331976425927)
        ·
          refine ⟨24193016777637497964638891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16128677851758331976425927 24193016777637497964638891)
          ·
            refine ⟨36289525166456246946958337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24193016777637497964638891 36289525166456246946958337)
            ·
              refine ⟨27217143874842185210218753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36289525166456246946958337 27217143874842185210218753)
              ·
                refine ⟨20412857906131638907664065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27217143874842185210218753 20412857906131638907664065)
                ·
                  refine ⟨15309643429598729180748049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20412857906131638907664065 15309643429598729180748049)
                  ·
                    refine ⟨11482232572199046885561037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15309643429598729180748049 11482232572199046885561037)
                    ·
                      refine ⟨4305837214574642582085389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482232572199046885561037 4305837214574642582085389)
                      ·
                        rfl

theorem cell23_8385588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_8385588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385588 prefixEnd_8385588 := by exact prefixLift 8385588
  have htrace : WordTrace (prefixWord ++ tailWord_8385588) baseStart_8385588 baseEnd_8385588 := by
    simpa [prefixWord, tailWord_8385588, baseEnd_8385588] using wordTrace_append hprefix tailTrace_8385588
  have hstable : (prefixWord ++ tailWord_8385588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385588).length < 2 ^ (prefixWord ++ tailWord_8385588).sum := by decide
  have hdescent : baseEnd_8385588 < baseStart_8385588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385618 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 3, 1, 3]
def baseStart_8385618 : Nat := 118140960795 + 8385618 * 2 ^ 59
def prefixEnd_8385618 : Nat := 4983230072969 + 3 ^ 40 * 8385618 * 2
def baseEnd_8385618 : Nat := 4305852618994277464710251

theorem tailTrace_8385618 : CollatzResearch.WordTrace tailWord_8385618 prefixEnd_8385618 4305852618994277464710251 := by
  unfold tailWord_8385618
  simp only [CollatzResearch.WordTrace]
  refine ⟨76462153733586402595065377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203899076622897073586841005 76462153733586402595065377)
  ·
    refine ⟨57346615300189801946299033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76462153733586402595065377 57346615300189801946299033)
    ·
      refine ⟨43009961475142351459724275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57346615300189801946299033 43009961475142351459724275)
      ·
        refine ⟨64514942212713527189586413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43009961475142351459724275 64514942212713527189586413)
        ·
          refine ⟨24193103329767572696094905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64514942212713527189586413 24193103329767572696094905)
          ·
            refine ⟨18144827497325679522071179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24193103329767572696094905 18144827497325679522071179)
            ·
              refine ⟨27217241245988519283106769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18144827497325679522071179 27217241245988519283106769)
              ·
                refine ⟨20412930934491389462330077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27217241245988519283106769 20412930934491389462330077)
                ·
                  refine ⟨7654849100434271048373779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20412930934491389462330077 7654849100434271048373779)
                  ·
                    refine ⟨11482273650651406572560669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654849100434271048373779 11482273650651406572560669)
                    ·
                      refine ⟨4305852618994277464710251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482273650651406572560669 4305852618994277464710251)
                      ·
                        rfl

theorem cell23_8385618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_8385618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385618 prefixEnd_8385618 := by exact prefixLift 8385618
  have htrace : WordTrace (prefixWord ++ tailWord_8385618) baseStart_8385618 baseEnd_8385618 := by
    simpa [prefixWord, tailWord_8385618, baseEnd_8385618] using wordTrace_append hprefix tailTrace_8385618
  have hstable : (prefixWord ++ tailWord_8385618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385618).length < 2 ^ (prefixWord ++ tailWord_8385618).sum := by decide
  have hdescent : baseEnd_8385618 < baseStart_8385618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385622 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_8385622 : Nat := 118140960795 + 8385622 * 2 ^ 59
def prefixEnd_8385622 : Nat := 4983230072969 + 3 ^ 40 * 8385622 * 2
def baseEnd_8385622 : Nat := 4305854672916895449060233

theorem tailTrace_8385622 : CollatzResearch.WordTrace tailWord_8385622 prefixEnd_8385622 4305854672916895449060233 := by
  unfold tailWord_8385622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19115547551645694941462945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 203899173884220746042271413 19115547551645694941462945)
  ·
    refine ⟨14336660663734271206097209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19115547551645694941462945 14336660663734271206097209)
    ·
      refine ⟨10752495497800703404572907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14336660663734271206097209 10752495497800703404572907)
      ·
        refine ⟨16128743246701055106859361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10752495497800703404572907 16128743246701055106859361)
        ·
          refine ⟨12096557435025791330144521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16128743246701055106859361 12096557435025791330144521)
          ·
            refine ⟨9072418076269343497608391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12096557435025791330144521 9072418076269343497608391)
            ·
              refine ⟨13608627114404015246412587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072418076269343497608391 13608627114404015246412587)
              ·
                refine ⟨20412940671606022869618881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608627114404015246412587 20412940671606022869618881)
                ·
                  refine ⟨15309705503704517152214161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20412940671606022869618881 15309705503704517152214161)
                  ·
                    refine ⟨11482279127778387864160621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15309705503704517152214161 11482279127778387864160621)
                    ·
                      refine ⟨4305854672916895449060233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482279127778387864160621 4305854672916895449060233)
                      ·
                        rfl

theorem cell23_8385622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_8385622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385622 prefixEnd_8385622 := by exact prefixLift 8385622
  have htrace : WordTrace (prefixWord ++ tailWord_8385622) baseStart_8385622 baseEnd_8385622 := by
    simpa [prefixWord, tailWord_8385622, baseEnd_8385622] using wordTrace_append hprefix tailTrace_8385622
  have hstable : (prefixWord ++ tailWord_8385622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385622).length < 2 ^ (prefixWord ++ tailWord_8385622).sum := by decide
  have hdescent : baseEnd_8385622 < baseStart_8385622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385624 : List Nat := [2, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_8385624 : Nat := 118140960795 + 8385624 * 2 ^ 59
def prefixEnd_8385624 : Nat := 4983230072969 + 3 ^ 40 * 8385624 * 2
def baseEnd_8385624 : Nat := 4305855699878204441235223

theorem tailTrace_8385624 : CollatzResearch.WordTrace tailWord_8385624 prefixEnd_8385624 4305855699878204441235223 := by
  unfold tailWord_8385624
  simp only [CollatzResearch.WordTrace]
  refine ⟨152924416886161936702489963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203899222514882582269986617 152924416886161936702489963)
  ·
    refine ⟨229386625329242905053734945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152924416886161936702489963 229386625329242905053734945)
    ·
      refine ⟨172039968996932178790301209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229386625329242905053734945 172039968996932178790301209)
      ·
        refine ⟨129029976747699134092725907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172039968996932178790301209 129029976747699134092725907)
        ·
          refine ⟨193544965121548701139088861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129029976747699134092725907 193544965121548701139088861)
          ·
            refine ⟨72579361920580762927158323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193544965121548701139088861 72579361920580762927158323)
            ·
              refine ⟨108869042880871144390737485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72579361920580762927158323 108869042880871144390737485)
              ·
                refine ⟨40825891080326679146526557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108869042880871144390737485 40825891080326679146526557)
                ·
                  refine ⟨15309709155122504679947459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40825891080326679146526557 15309709155122504679947459)
                  ·
                    refine ⟨22964563732683757019921189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15309709155122504679947459 22964563732683757019921189)
                    ·
                      refine ⟨4305855699878204441235223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22964563732683757019921189 4305855699878204441235223)
                      ·
                        rfl

theorem cell23_8385624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_8385624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385624 prefixEnd_8385624 := by exact prefixLift 8385624
  have htrace : WordTrace (prefixWord ++ tailWord_8385624) baseStart_8385624 baseEnd_8385624 := by
    simpa [prefixWord, tailWord_8385624, baseEnd_8385624] using wordTrace_append hprefix tailTrace_8385624
  have hstable : (prefixWord ++ tailWord_8385624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385624).length < 2 ^ (prefixWord ++ tailWord_8385624).sum := by decide
  have hdescent : baseEnd_8385624 < baseStart_8385624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385641 : List Nat := [1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_8385641 : Nat := 118140960795 + 8385641 * 2 ^ 59
def prefixEnd_8385641 : Nat := 4983230072969 + 3 ^ 40 * 8385641 * 2
def baseEnd_8385641 : Nat := 4305864429049330874722645

theorem tailTrace_8385641 : CollatzResearch.WordTrace tailWord_8385641 prefixEnd_8385641 4305864429049330874722645 := by
  unfold tailWord_8385641
  simp only [CollatzResearch.WordTrace]
  refine ⟨305849453813262285308348777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203899635875508190205565851 305849453813262285308348777)
  ·
    refine ⟨229387090359946713981261583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305849453813262285308348777 229387090359946713981261583)
    ·
      refine ⟨344080635539920070971892375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229387090359946713981261583 344080635539920070971892375)
      ·
        refine ⟨516120953309880106457838563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344080635539920070971892375 516120953309880106457838563)
        ·
          refine ⟨774181429964820159686757845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516120953309880106457838563 774181429964820159686757845)
          ·
            refine ⟨18144877264800472492658387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 774181429964820159686757845 18144877264800472492658387)
            ·
              refine ⟨27217315897200708738987581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18144877264800472492658387 27217315897200708738987581)
              ·
                refine ⟨10206493461450265777120343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27217315897200708738987581 10206493461450265777120343)
                ·
                  refine ⟨15309740192175398665680515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10206493461450265777120343 15309740192175398665680515)
                  ·
                    refine ⟨22964610288263097998520773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15309740192175398665680515 22964610288263097998520773)
                    ·
                      refine ⟨4305864429049330874722645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22964610288263097998520773 4305864429049330874722645)
                      ·
                        rfl

theorem cell23_8385641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_8385641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385641 prefixEnd_8385641 := by exact prefixLift 8385641
  have htrace : WordTrace (prefixWord ++ tailWord_8385641) baseStart_8385641 baseEnd_8385641 := by
    simpa [prefixWord, tailWord_8385641, baseEnd_8385641] using wordTrace_append hprefix tailTrace_8385641
  have hstable : (prefixWord ++ tailWord_8385641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385641).length < 2 ^ (prefixWord ++ tailWord_8385641).sum := by decide
  have hdescent : baseEnd_8385641 < baseStart_8385641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385644 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_8385644 : Nat := 118140960795 + 8385644 * 2 ^ 59
def prefixEnd_8385644 : Nat := 4983230072969 + 3 ^ 40 * 8385644 * 2
def baseEnd_8385644 : Nat := 4305865969491294362985131

theorem tailTrace_8385644 : CollatzResearch.WordTrace tailWord_8385644 prefixEnd_8385644 4305865969491294362985131 := by
  unfold tailWord_8385644
  simp only [CollatzResearch.WordTrace]
  refine ⟨152924781616125708410353993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203899708821500944547138657 152924781616125708410353993)
  ·
    refine ⟨114693586212094281307765495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152924781616125708410353993 114693586212094281307765495)
    ·
      refine ⟨172040379318141421961648243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114693586212094281307765495 172040379318141421961648243)
      ·
        refine ⟨258060568977212132942472365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172040379318141421961648243 258060568977212132942472365)
        ·
          refine ⟨96772713366454549853427137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258060568977212132942472365 96772713366454549853427137)
          ·
            refine ⟨72579535024840912390070353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96772713366454549853427137 72579535024840912390070353)
            ·
              refine ⟨54434651268630684292552765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72579535024840912390070353 54434651268630684292552765)
              ·
                refine ⟨20412994225736506609707287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54434651268630684292552765 20412994225736506609707287)
                ·
                  refine ⟨30619491338604759914560931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20412994225736506609707287 30619491338604759914560931)
                  ·
                    refine ⟨45929237007907139871841397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30619491338604759914560931 45929237007907139871841397)
                    ·
                      refine ⟨4305865969491294362985131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45929237007907139871841397 4305865969491294362985131)
                      ·
                        rfl

theorem cell23_8385644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_8385644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385644 prefixEnd_8385644 := by exact prefixLift 8385644
  have htrace : WordTrace (prefixWord ++ tailWord_8385644) baseStart_8385644 baseEnd_8385644 := by
    simpa [prefixWord, tailWord_8385644, baseEnd_8385644] using wordTrace_append hprefix tailTrace_8385644
  have hstable : (prefixWord ++ tailWord_8385644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385644).length < 2 ^ (prefixWord ++ tailWord_8385644).sum := by decide
  have hdescent : baseEnd_8385644 < baseStart_8385644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385647 : List Nat := [1, 1, 2, 1, 3, 3, 12]
def baseStart_8385647 : Nat := 118140960795 + 8385647 * 2 ^ 59
def prefixEnd_8385647 : Nat := 4983230072969 + 3 ^ 40 * 8385647 * 2
def baseEnd_8385647 : Nat := 53158858147324171003057

theorem tailTrace_8385647 : CollatzResearch.WordTrace tailWord_8385647 prefixEnd_8385647 53158858147324171003057 := by
  unfold tailWord_8385647
  simp only [CollatzResearch.WordTrace]
  refine ⟨305849672651240548333067195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203899781767493698888711463 305849672651240548333067195)
  ·
    refine ⟨458774508976860822499600793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305849672651240548333067195 458774508976860822499600793)
    ·
      refine ⟨344080881732645616874700595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458774508976860822499600793 344080881732645616874700595)
      ·
        refine ⟨516121322598968425312050893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344080881732645616874700595 516121322598968425312050893)
        ·
          refine ⟨193545495974613159492019085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 516121322598968425312050893 193545495974613159492019085)
          ·
            refine ⟨72579560990479934809507157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193545495974613159492019085 72579560990479934809507157)
            ·
              refine ⟨53158858147324171003057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 72579560990479934809507157 53158858147324171003057)
              ·
                rfl

theorem cell23_8385647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 12].length) (baseStart_8385647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385647 prefixEnd_8385647 := by exact prefixLift 8385647
  have htrace : WordTrace (prefixWord ++ tailWord_8385647) baseStart_8385647 baseEnd_8385647 := by
    simpa [prefixWord, tailWord_8385647, baseEnd_8385647] using wordTrace_append hprefix tailTrace_8385647
  have hstable : (prefixWord ++ tailWord_8385647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385647).length < 2 ^ (prefixWord ++ tailWord_8385647).sum := by decide
  have hdescent : baseEnd_8385647 < baseStart_8385647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385678 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_8385678 : Nat := 118140960795 + 8385678 * 2 ^ 59
def prefixEnd_8385678 : Nat := 4983230072969 + 3 ^ 40 * 8385678 * 2
def baseEnd_8385678 : Nat := 4305883427833547229959975

theorem tailTrace_8385678 : CollatzResearch.WordTrace tailWord_8385678 prefixEnd_8385678 4305883427833547229959975 := by
  unfold tailWord_8385678
  simp only [CollatzResearch.WordTrace]
  refine ⟨38231350414266030078430711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203900535542752160418297125 38231350414266030078430711)
  ·
    refine ⟨57347025621399045117646067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38231350414266030078430711 57347025621399045117646067)
    ·
      refine ⟨86020538432098567676469101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57347025621399045117646067 86020538432098567676469101)
      ·
        refine ⟨32257701912036962878675913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86020538432098567676469101 32257701912036962878675913)
        ·
          refine ⟨24193276434027722159006935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32257701912036962878675913 24193276434027722159006935)
          ·
            refine ⟨36289914651041583238510403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24193276434027722159006935 36289914651041583238510403)
            ·
              refine ⟨54434871976562374857765605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36289914651041583238510403 54434871976562374857765605)
              ·
                refine ⟨10206538495605445285831051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54434871976562374857765605 10206538495605445285831051)
                ·
                  refine ⟨15309807743408167928746577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10206538495605445285831051 15309807743408167928746577)
                  ·
                    refine ⟨11482355807556125946559933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15309807743408167928746577 11482355807556125946559933)
                    ·
                      refine ⟨4305883427833547229959975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482355807556125946559933 4305883427833547229959975)
                      ·
                        rfl

theorem cell23_8385678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_8385678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385678 prefixEnd_8385678 := by exact prefixLift 8385678
  have htrace : WordTrace (prefixWord ++ tailWord_8385678) baseStart_8385678 baseEnd_8385678 := by
    simpa [prefixWord, tailWord_8385678, baseEnd_8385678] using wordTrace_append hprefix tailTrace_8385678
  have hstable : (prefixWord ++ tailWord_8385678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385678).length < 2 ^ (prefixWord ++ tailWord_8385678).sum := by decide
  have hdescent : baseEnd_8385678 < baseStart_8385678 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385692 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 1, 2, 2]
def baseStart_8385692 : Nat := 118140960795 + 8385692 * 2 ^ 59
def prefixEnd_8385692 : Nat := 4983230072969 + 3 ^ 40 * 8385692 * 2
def baseEnd_8385692 : Nat := 4305890616562710175184911

theorem tailTrace_8385692 : CollatzResearch.WordTrace tailWord_8385692 prefixEnd_8385692 4305890616562710175184911 := by
  unfold tailWord_8385692
  simp only [CollatzResearch.WordTrace]
  refine ⟨152925656968038760509227665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203900875957385014012303553 152925656968038760509227665)
  ·
    refine ⟨114694242726029070381920749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152925656968038760509227665 114694242726029070381920749)
    ·
      refine ⟨43010341022260901393220281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114694242726029070381920749 43010341022260901393220281)
      ·
        refine ⟨32257755766695676044915211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43010341022260901393220281 32257755766695676044915211)
        ·
          refine ⟨48386633650043514067372817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32257755766695676044915211 48386633650043514067372817)
          ·
            refine ⟨36289975237532635550529613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48386633650043514067372817 36289975237532635550529613)
            ·
              refine ⟨13608740714074738331448605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36289975237532635550529613 13608740714074738331448605)
              ·
                refine ⟨5103277767778026874293227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13608740714074738331448605 5103277767778026874293227)
                ·
                  refine ⟨7654916651667040311439841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103277767778026874293227 7654916651667040311439841)
                  ·
                    refine ⟨5741187488750280233579881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7654916651667040311439841 5741187488750280233579881)
                    ·
                      refine ⟨4305890616562710175184911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741187488750280233579881 4305890616562710175184911)
                      ·
                        rfl

theorem cell23_8385692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_8385692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385692 prefixEnd_8385692 := by exact prefixLift 8385692
  have htrace : WordTrace (prefixWord ++ tailWord_8385692) baseStart_8385692 baseEnd_8385692 := by
    simpa [prefixWord, tailWord_8385692, baseEnd_8385692] using wordTrace_append hprefix tailTrace_8385692
  have hstable : (prefixWord ++ tailWord_8385692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385692).length < 2 ^ (prefixWord ++ tailWord_8385692).sum := by decide
  have hdescent : baseEnd_8385692 < baseStart_8385692 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385698 : List Nat := [3, 3, 1, 3, 3, 1, 9]
def baseStart_8385698 : Nat := 118140960795 + 8385698 * 2 ^ 59
def prefixEnd_8385698 : Nat := 4983230072969 + 3 ^ 40 * 8385698 * 2
def baseEnd_8385698 : Nat := 53159181449958483354443

theorem tailTrace_8385698 : CollatzResearch.WordTrace tailWord_8385698 prefixEnd_8385698 53159181449958483354443 := by
  unfold tailWord_8385698
  simp only [CollatzResearch.WordTrace]
  refine ⟨76462883193513946010793437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203901021849370522695449165 76462883193513946010793437)
  ·
    refine ⟨28673581197567729754047539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76462883193513946010793437 28673581197567729754047539)
    ·
      refine ⟨43010371796351594631071309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28673581197567729754047539 43010371796351594631071309)
      ·
        refine ⟨16128889423631847986651741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43010371796351594631071309 16128889423631847986651741)
        ·
          refine ⟨6048333533861942994994403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16128889423631847986651741 6048333533861942994994403)
          ·
            refine ⟨9072500300792914492491605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048333533861942994994403 9072500300792914492491605)
            ·
              refine ⟨53159181449958483354443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 9072500300792914492491605 53159181449958483354443)
              ·
                rfl

theorem cell23_8385698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 9].length) (baseStart_8385698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385698 prefixEnd_8385698 := by exact prefixLift 8385698
  have htrace : WordTrace (prefixWord ++ tailWord_8385698) baseStart_8385698 baseEnd_8385698 := by
    simpa [prefixWord, tailWord_8385698, baseEnd_8385698] using wordTrace_append hprefix tailTrace_8385698
  have hstable : (prefixWord ++ tailWord_8385698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385698).length < 2 ^ (prefixWord ++ tailWord_8385698).sum := by decide
  have hdescent : baseEnd_8385698 < baseStart_8385698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385709 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_8385709 : Nat := 118140960795 + 8385709 * 2 ^ 59
def prefixEnd_8385709 : Nat := 4983230072969 + 3 ^ 40 * 8385709 * 2
def baseEnd_8385709 : Nat := 4305899345733836608672333

theorem tailTrace_8385709 : CollatzResearch.WordTrace tailWord_8385709 prefixEnd_8385709 4305899345733836608672333 := by
  unfold tailWord_8385709
  simp only [CollatzResearch.WordTrace]
  refine ⟨305851933977015932921824181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203901289318010621947882787 305851933977015932921824181)
  ·
    refine ⟨28673618810345243711421017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305851933977015932921824181 28673618810345243711421017)
    ·
      refine ⟨21505214107758932783565763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28673618810345243711421017 21505214107758932783565763)
      ·
        refine ⟨32257821161638399175348645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21505214107758932783565763 32257821161638399175348645)
        ·
          refine ⟨6048341467807199845377871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32257821161638399175348645 6048341467807199845377871)
          ·
            refine ⟨9072512201710799768066807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048341467807199845377871 9072512201710799768066807)
            ·
              refine ⟨13608768302566199652100211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072512201710799768066807 13608768302566199652100211)
              ·
                refine ⟨20413152453849299478150317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608768302566199652100211 20413152453849299478150317)
                ·
                  refine ⟨7654932170193487304306369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20413152453849299478150317 7654932170193487304306369)
                  ·
                    refine ⟨5741199127645115478229777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7654932170193487304306369 5741199127645115478229777)
                    ·
                      refine ⟨4305899345733836608672333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741199127645115478229777 4305899345733836608672333)
                      ·
                        rfl

theorem cell23_8385709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_8385709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385709 prefixEnd_8385709 := by exact prefixLift 8385709
  have htrace : WordTrace (prefixWord ++ tailWord_8385709) baseStart_8385709 baseEnd_8385709 := by
    simpa [prefixWord, tailWord_8385709, baseEnd_8385709] using wordTrace_append hprefix tailTrace_8385709
  have hstable : (prefixWord ++ tailWord_8385709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385709).length < 2 ^ (prefixWord ++ tailWord_8385709).sum := by decide
  have hdescent : baseEnd_8385709 < baseStart_8385709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385725 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 2, 1, 3]
def baseStart_8385725 : Nat := 118140960795 + 8385725 * 2 ^ 59
def prefixEnd_8385725 : Nat := 4983230072969 + 3 ^ 40 * 8385725 * 2
def baseEnd_8385725 : Nat := 4305907561424308546072259

theorem tailTrace_8385725 : CollatzResearch.WordTrace tailWord_8385725 prefixEnd_8385725 4305907561424308546072259 := by
  unfold tailWord_8385725
  simp only [CollatzResearch.WordTrace]
  refine ⟨305852517544957967654406629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203901678363305311769604419 305852517544957967654406629)
  ·
    refine ⟨57347347039679618935201243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305852517544957967654406629 57347347039679618935201243)
    ·
      refine ⟨86021020559519428402801865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57347347039679618935201243 86021020559519428402801865)
      ·
        refine ⟨64515765419639571302101399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86021020559519428402801865 64515765419639571302101399)
        ·
          refine ⟨96773648129459356953152099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64515765419639571302101399 96773648129459356953152099)
          ·
            refine ⟨145160472194189035429728149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96773648129459356953152099 145160472194189035429728149)
            ·
              refine ⟨6804397134102611035768507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145160472194189035429728149 6804397134102611035768507)
              ·
                refine ⟨10206595701153916553652761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804397134102611035768507 10206595701153916553652761)
                ·
                  refine ⟨7654946775865437415239571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10206595701153916553652761 7654946775865437415239571)
                  ·
                    refine ⟨11482420163798156122859357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7654946775865437415239571 11482420163798156122859357)
                    ·
                      refine ⟨4305907561424308546072259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482420163798156122859357 4305907561424308546072259)
                      ·
                        rfl

theorem cell23_8385725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_8385725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385725 prefixEnd_8385725 := by exact prefixLift 8385725
  have htrace : WordTrace (prefixWord ++ tailWord_8385725) baseStart_8385725 baseEnd_8385725 := by
    simpa [prefixWord, tailWord_8385725, baseEnd_8385725] using wordTrace_append hprefix tailTrace_8385725
  have hstable : (prefixWord ++ tailWord_8385725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385725).length < 2 ^ (prefixWord ++ tailWord_8385725).sum := by decide
  have hdescent : baseEnd_8385725 < baseStart_8385725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385752 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_8385752 : Nat := 118140960795 + 8385752 * 2 ^ 59
def prefixEnd_8385752 : Nat := 4983230072969 + 3 ^ 40 * 8385752 * 2
def baseEnd_8385752 : Nat := 4305921425401979940434635

theorem tailTrace_8385752 : CollatzResearch.WordTrace tailWord_8385752 prefixEnd_8385752 4305921425401979940434635 := by
  unfold tailWord_8385752
  simp only [CollatzResearch.WordTrace]
  refine ⟨152926751157930075632819755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203902334877240100843759673 152926751157930075632819755)
  ·
    refine ⟨229390126736895113449229633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152926751157930075632819755 229390126736895113449229633)
    ·
      refine ⟨172042595052671335086922225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229390126736895113449229633 172042595052671335086922225)
      ·
        refine ⟨129031946289503501315191669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172042595052671335086922225 129031946289503501315191669)
        ·
          refine ⟨12096744964640953248299219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129031946289503501315191669 12096744964640953248299219)
          ·
            refine ⟨18145117446961429872448829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096744964640953248299219 18145117446961429872448829)
            ·
              refine ⟨6804419042610536202168311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18145117446961429872448829 6804419042610536202168311)
              ·
                refine ⟨10206628563915804303252467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804419042610536202168311 10206628563915804303252467)
                ·
                  refine ⟨15309942845873706454878701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10206628563915804303252467 15309942845873706454878701)
                  ·
                    refine ⟨5741228567202639920579513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15309942845873706454878701 5741228567202639920579513)
                    ·
                      refine ⟨4305921425401979940434635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741228567202639920579513 4305921425401979940434635)
                      ·
                        rfl

theorem cell23_8385752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_8385752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385752 prefixEnd_8385752 := by exact prefixLift 8385752
  have htrace : WordTrace (prefixWord ++ tailWord_8385752) baseStart_8385752 baseEnd_8385752 := by
    simpa [prefixWord, tailWord_8385752, baseEnd_8385752] using wordTrace_append hprefix tailTrace_8385752
  have hstable : (prefixWord ++ tailWord_8385752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385752).length < 2 ^ (prefixWord ++ tailWord_8385752).sum := by decide
  have hdescent : baseEnd_8385752 < baseStart_8385752 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385764 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_8385764 : Nat := 118140960795 + 8385764 * 2 ^ 59
def prefixEnd_8385764 : Nat := 4983230072969 + 3 ^ 40 * 8385764 * 2
def baseEnd_8385764 : Nat := 4305927587169833893484579

theorem tailTrace_8385764 : CollatzResearch.WordTrace tailWord_8385764 prefixEnd_8385764 4305927587169833893484579 := by
  unfold tailWord_8385764
  simp only [CollatzResearch.WordTrace]
  refine ⟨152926969995908338657538173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203902626661211118210050897 152926969995908338657538173)
  ·
    refine ⟨57347613748465626996576815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152926969995908338657538173 57347613748465626996576815)
    ·
      refine ⟨86021420622698440494865223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57347613748465626996576815 86021420622698440494865223)
      ·
        refine ⟨129032130934047660742297835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86021420622698440494865223 129032130934047660742297835)
        ·
          refine ⟨193548196401071491113446753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129032130934047660742297835 193548196401071491113446753)
          ·
            refine ⟨145161147300803618335085065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193548196401071491113446753 145161147300803618335085065)
            ·
              refine ⟨108870860475602713751313799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145161147300803618335085065 108870860475602713751313799)
              ·
                refine ⟨163306290713404070626970699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108870860475602713751313799 163306290713404070626970699)
                ·
                  refine ⟨244959436070106105940456049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163306290713404070626970699 244959436070106105940456049)
                  ·
                    refine ⟨183719577052579579455342037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 244959436070106105940456049 183719577052579579455342037)
                    ·
                      refine ⟨4305927587169833893484579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 183719577052579579455342037 4305927587169833893484579)
                      ·
                        rfl

theorem cell23_8385764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_8385764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385764 prefixEnd_8385764 := by exact prefixLift 8385764
  have htrace : WordTrace (prefixWord ++ tailWord_8385764) baseStart_8385764 baseEnd_8385764 := by
    simpa [prefixWord, tailWord_8385764, baseEnd_8385764] using wordTrace_append hprefix tailTrace_8385764
  have hstable : (prefixWord ++ tailWord_8385764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385764).length < 2 ^ (prefixWord ++ tailWord_8385764).sum := by decide
  have hdescent : baseEnd_8385764 < baseStart_8385764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385778 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 2, 2, 4]
def baseStart_8385778 : Nat := 118140960795 + 8385778 * 2 ^ 59
def prefixEnd_8385778 : Nat := 4983230072969 + 3 ^ 40 * 8385778 * 2
def baseEnd_8385778 : Nat := 4305934775898996838709515

theorem tailTrace_8385778 : CollatzResearch.WordTrace tailWord_8385778 prefixEnd_8385778 4305934775898996838709515 := by
  unfold tailWord_8385778
  simp only [CollatzResearch.WordTrace]
  refine ⟨76463612653441489426521497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203902967075843971804057325 76463612653441489426521497)
  ·
    refine ⟨57347709490081117069891123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76463612653441489426521497 57347709490081117069891123)
    ·
      refine ⟨86021564235121675604836685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57347709490081117069891123 86021564235121675604836685)
      ·
        refine ⟨32258086588170628351813757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86021564235121675604836685 32258086588170628351813757)
        ·
          refine ⟨12096782470563985631930159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32258086588170628351813757 12096782470563985631930159)
          ·
            refine ⟨18145173705845978447895239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12096782470563985631930159 18145173705845978447895239)
            ·
              refine ⟨27217760558768967671842859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18145173705845978447895239 27217760558768967671842859)
              ·
                refine ⟨40826640838153451507764289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27217760558768967671842859 40826640838153451507764289)
                ·
                  refine ⟨30619980628615088630823217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40826640838153451507764289 30619980628615088630823217)
                  ·
                    refine ⟨22964985471461316473117413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30619980628615088630823217 22964985471461316473117413)
                    ·
                      refine ⟨4305934775898996838709515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22964985471461316473117413 4305934775898996838709515)
                      ·
                        rfl

theorem cell23_8385778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_8385778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385778 prefixEnd_8385778 := by exact prefixLift 8385778
  have htrace : WordTrace (prefixWord ++ tailWord_8385778) baseStart_8385778 baseEnd_8385778 := by
    simpa [prefixWord, tailWord_8385778, baseEnd_8385778] using wordTrace_append hprefix tailTrace_8385778
  have hstable : (prefixWord ++ tailWord_8385778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385778).length < 2 ^ (prefixWord ++ tailWord_8385778).sum := by decide
  have hdescent : baseEnd_8385778 < baseStart_8385778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385865 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 1, 4]
def baseStart_8385865 : Nat := 118140960795 + 8385865 * 2 ^ 59
def prefixEnd_8385865 : Nat := 4983230072969 + 3 ^ 40 * 8385865 * 2
def baseEnd_8385865 : Nat := 1435326482905312666107205

theorem tailTrace_8385865 : CollatzResearch.WordTrace tailWord_8385865 prefixEnd_8385865 1435326482905312666107205 := by
  unfold tailWord_8385865
  simp only [CollatzResearch.WordTrace]
  refine ⟨305857623764450771564503049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203905082509633847709668699 305857623764450771564503049)
  ·
    refine ⟨229393217823338078673377287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305857623764450771564503049 229393217823338078673377287)
    ·
      refine ⟨344089826735007118010065931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229393217823338078673377287 344089826735007118010065931)
      ·
        refine ⟨516134740102510677015098897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344089826735007118010065931 516134740102510677015098897)
        ·
          refine ⟨387101055076883007761324173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516134740102510677015098897 387101055076883007761324173)
          ·
            refine ⟨145162895653831127910496565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387101055076883007761324173 145162895653831127910496565)
            ·
              refine ⟨13609021467546668241609053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145162895653831127910496565 13609021467546668241609053)
              ·
                refine ⟨5103383050330000590603395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13609021467546668241609053 5103383050330000590603395)
                ·
                  refine ⟨7655074575495000885905093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103383050330000590603395 7655074575495000885905093)
                  ·
                    refine ⟨1435326482905312666107205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7655074575495000885905093 1435326482905312666107205)
                    ·
                      rfl

theorem cell23_8385865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 1, 4].length) (baseStart_8385865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385865 prefixEnd_8385865 := by exact prefixLift 8385865
  have htrace : WordTrace (prefixWord ++ tailWord_8385865) baseStart_8385865 baseEnd_8385865 := by
    simpa [prefixWord, tailWord_8385865, baseEnd_8385865] using wordTrace_append hprefix tailTrace_8385865
  have hstable : (prefixWord ++ tailWord_8385865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385865).length < 2 ^ (prefixWord ++ tailWord_8385865).sum := by decide
  have hdescent : baseEnd_8385865 < baseStart_8385865 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385915 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 2, 3, 2]
def baseStart_8385915 : Nat := 118140960795 + 8385915 * 2 ^ 59
def prefixEnd_8385915 : Nat := 4983230072969 + 3 ^ 40 * 8385915 * 2
def baseEnd_8385915 : Nat := 4306005122748662802696385

theorem tailTrace_8385915 : CollatzResearch.WordTrace tailWord_8385915 prefixEnd_8385915 4306005122748662802696385 := by
  unfold tailWord_8385915
  simp only [CollatzResearch.WordTrace]
  refine ⟨305859447414269630103823199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203906298276179753402548799 305859447414269630103823199)
  ·
    refine ⟨458789171121404445155734799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305859447414269630103823199 458789171121404445155734799)
    ·
      refine ⟨688183756682106667733602199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458789171121404445155734799 688183756682106667733602199)
      ·
        refine ⟨1032275635023160001600403299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688183756682106667733602199 1032275635023160001600403299)
        ·
          refine ⟨1548413452534740002400604949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032275635023160001600403299 1548413452534740002400604949)
          ·
            refine ⟨72581880587565937612528357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1548413452534740002400604949 72581880587565937612528357)
            ·
              refine ⟨13609102610168613302349067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72581880587565937612528357 13609102610168613302349067)
              ·
                refine ⟨20413653915252919953523601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13609102610168613302349067 20413653915252919953523601)
                ·
                  refine ⟨15310240436439689965142701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20413653915252919953523601 15310240436439689965142701)
                  ·
                    refine ⟨5741340163664883736928513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15310240436439689965142701 5741340163664883736928513)
                    ·
                      refine ⟨4306005122748662802696385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741340163664883736928513 4306005122748662802696385)
                      ·
                        rfl

theorem cell23_8385915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3, 2].length) (baseStart_8385915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385915 prefixEnd_8385915 := by exact prefixLift 8385915
  have htrace : WordTrace (prefixWord ++ tailWord_8385915) baseStart_8385915 baseEnd_8385915 := by
    simpa [prefixWord, tailWord_8385915, baseEnd_8385915] using wordTrace_append hprefix tailTrace_8385915
  have hstable : (prefixWord ++ tailWord_8385915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385915).length < 2 ^ (prefixWord ++ tailWord_8385915).sum := by decide
  have hdescent : baseEnd_8385915 < baseStart_8385915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8385941 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_8385941 : Nat := 118140960795 + 8385941 * 2 ^ 59
def prefixEnd_8385941 : Nat := 4983230072969 + 3 ^ 40 * 8385941 * 2
def baseEnd_8385941 : Nat := 4306018473245679700971265

theorem tailTrace_8385941 : CollatzResearch.WordTrace tailWord_8385941 prefixEnd_8385941 4306018473245679700971265 := by
  unfold tailWord_8385941
  simp only [CollatzResearch.WordTrace]
  refine ⟨305860395712175436544269677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203906930474783624362846451 305860395712175436544269677)
  ·
    refine ⟨114697648392065788704101129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305860395712175436544269677 114697648392065788704101129)
    ·
      refine ⟨86023236294049341528075847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114697648392065788704101129 86023236294049341528075847)
      ·
        refine ⟨129034854441074012292113771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86023236294049341528075847 129034854441074012292113771)
        ·
          refine ⟨193552281661611018438170657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129034854441074012292113771 193552281661611018438170657)
          ·
            refine ⟨145164211246208263828627993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193552281661611018438170657 145164211246208263828627993)
            ·
              refine ⟨108873158434656197871470995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145164211246208263828627993 108873158434656197871470995)
              ·
                refine ⟨163309737651984296807206493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108873158434656197871470995 163309737651984296807206493)
                ·
                  refine ⟨61241151619494111302702435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163309737651984296807206493 61241151619494111302702435)
                  ·
                    refine ⟨91861727429241166954053653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61241151619494111302702435 91861727429241166954053653)
                    ·
                      refine ⟨4306018473245679700971265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91861727429241166954053653 4306018473245679700971265)
                      ·
                        rfl

theorem cell23_8385941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_8385941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8385941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8385941 prefixEnd_8385941 := by exact prefixLift 8385941
  have htrace : WordTrace (prefixWord ++ tailWord_8385941) baseStart_8385941 baseEnd_8385941 := by
    simpa [prefixWord, tailWord_8385941, baseEnd_8385941] using wordTrace_append hprefix tailTrace_8385941
  have hstable : (prefixWord ++ tailWord_8385941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8385941).length < 2 ^ (prefixWord ++ tailWord_8385941).sum := by decide
  have hdescent : baseEnd_8385941 < baseStart_8385941 := by decide
  rcases family_descends (prefixWord ++ tailWord_8385941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386069 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_8386069 : Nat := 118140960795 + 8386069 * 2 ^ 59
def prefixEnd_8386069 : Nat := 4983230072969 + 3 ^ 40 * 8386069 * 2
def baseEnd_8386069 : Nat := 4306084198769455200170677

theorem tailTrace_8386069 : CollatzResearch.WordTrace tailWord_8386069 prefixEnd_8386069 4306084198769455200170677 := by
  unfold tailWord_8386069
  simp only [CollatzResearch.WordTrace]
  refine ⟨305865064255711714404929261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203910042837141142936619507 305865064255711714404929261)
  ·
    refine ⟨114699399095891892901848473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305865064255711714404929261 114699399095891892901848473)
    ·
      refine ⟨86024549321918919676386355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114699399095891892901848473 86024549321918919676386355)
      ·
        refine ⟨129036823982878379514579533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86024549321918919676386355 129036823982878379514579533)
        ·
          refine ⟨48388808993579392317967325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129036823982878379514579533 48388808993579392317967325)
          ·
            refine ⟨18145803372592272119237747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48388808993579392317967325 18145803372592272119237747)
            ·
              refine ⟨27218705058888408178856621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18145803372592272119237747 27218705058888408178856621)
              ·
                refine ⟨10207014397083153067071233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27218705058888408178856621 10207014397083153067071233)
                ·
                  refine ⟨7655260797812364800303425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10207014397083153067071233 7655260797812364800303425)
                  ·
                    refine ⟨5741445598359273600227569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7655260797812364800303425 5741445598359273600227569)
                    ·
                      refine ⟨4306084198769455200170677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741445598359273600227569 4306084198769455200170677)
                      ·
                        rfl

theorem cell23_8386069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_8386069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386069 prefixEnd_8386069 := by exact prefixLift 8386069
  have htrace : WordTrace (prefixWord ++ tailWord_8386069) baseStart_8386069 baseEnd_8386069 := by
    simpa [prefixWord, tailWord_8386069, baseEnd_8386069] using wordTrace_append hprefix tailTrace_8386069
  have hstable : (prefixWord ++ tailWord_8386069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386069).length < 2 ^ (prefixWord ++ tailWord_8386069).sum := by decide
  have hdescent : baseEnd_8386069 < baseStart_8386069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386105 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_8386105 : Nat := 118140960795 + 8386105 * 2 ^ 59
def prefixEnd_8386105 : Nat := 4983230072969 + 3 ^ 40 * 8386105 * 2
def baseEnd_8386105 : Nat := 1435367561357672353106837

theorem tailTrace_8386105 : CollatzResearch.WordTrace tailWord_8386105 prefixEnd_8386105 1435367561357672353106837 := by
  unfold tailWord_8386105
  simp only [CollatzResearch.WordTrace]
  refine ⟨305866377283581292553239769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203910918189054195035493179 305866377283581292553239769)
  ·
    refine ⟨229399782962685969414929827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305866377283581292553239769 229399782962685969414929827)
    ·
      refine ⟨344099674444028954122394741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229399782962685969414929827 344099674444028954122394741)
      ·
        refine ⟨32259344479127714448974507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344099674444028954122394741 32259344479127714448974507)
        ·
          refine ⟨48389016718691571673461761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32259344479127714448974507 48389016718691571673461761)
          ·
            refine ⟨36291762539018678755096321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48389016718691571673461761 36291762539018678755096321)
            ·
              refine ⟨27218821904264009066322241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36291762539018678755096321 27218821904264009066322241)
              ·
                refine ⟨20414116428198006799741681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27218821904264009066322241 20414116428198006799741681)
                ·
                  refine ⟨15310587321148505099806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20414116428198006799741681 15310587321148505099806261)
                  ·
                    refine ⟨1435367561357672353106837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15310587321148505099806261 1435367561357672353106837)
                    ·
                      rfl

theorem cell23_8386105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_8386105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386105 prefixEnd_8386105 := by exact prefixLift 8386105
  have htrace : WordTrace (prefixWord ++ tailWord_8386105) baseStart_8386105 baseEnd_8386105 := by
    simpa [prefixWord, tailWord_8386105, baseEnd_8386105] using wordTrace_append hprefix tailTrace_8386105
  have hstable : (prefixWord ++ tailWord_8386105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386105).length < 2 ^ (prefixWord ++ tailWord_8386105).sum := by decide
  have hdescent : baseEnd_8386105 < baseStart_8386105 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386135 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 5, 4]
def baseStart_8386135 : Nat := 118140960795 + 8386135 * 2 ^ 59
def prefixEnd_8386135 : Nat := 4983230072969 + 3 ^ 40 * 8386135 * 2
def baseEnd_8386135 : Nat := 1435372696164217313981791

theorem tailTrace_8386135 : CollatzResearch.WordTrace tailWord_8386135 prefixEnd_8386135 1435372696164217313981791 := by
  unfold tailWord_8386135
  simp only [CollatzResearch.WordTrace]
  refine ⟨305867471473472607676831859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203911647648981738451221239 305867471473472607676831859)
  ·
    refine ⟨458801207210208911515247789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305867471473472607676831859 458801207210208911515247789)
    ·
      refine ⟨172050452703828341818217921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458801207210208911515247789 172050452703828341818217921)
      ·
        refine ⟨129037839527871256363663441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172050452703828341818217921 129037839527871256363663441)
        ·
          refine ⟨96778379645903442272747581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129037839527871256363663441 96778379645903442272747581)
          ·
            refine ⟨36291892367213790852280343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96778379645903442272747581 36291892367213790852280343)
            ·
              refine ⟨54437838550820686278420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36291892367213790852280343 54437838550820686278420515)
              ·
                refine ⟨81656757826231029417630773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54437838550820686278420515 81656757826231029417630773)
                ·
                  refine ⟨7655321046209159007902885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81656757826231029417630773 7655321046209159007902885)
                  ·
                    refine ⟨1435372696164217313981791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7655321046209159007902885 1435372696164217313981791)
                    ·
                      rfl

theorem cell23_8386135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_8386135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386135 prefixEnd_8386135 := by exact prefixLift 8386135
  have htrace : WordTrace (prefixWord ++ tailWord_8386135) baseStart_8386135 baseEnd_8386135 := by
    simpa [prefixWord, tailWord_8386135, baseEnd_8386135] using wordTrace_append hprefix tailTrace_8386135
  have hstable : (prefixWord ++ tailWord_8386135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386135).length < 2 ^ (prefixWord ++ tailWord_8386135).sum := by decide
  have hdescent : baseEnd_8386135 < baseStart_8386135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386138 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_8386138 : Nat := 118140960795 + 8386138 * 2 ^ 59
def prefixEnd_8386138 : Nat := 4983230072969 + 3 ^ 40 * 8386138 * 2
def baseEnd_8386138 : Nat := 4306119628934615430207859

theorem tailTrace_8386138 : CollatzResearch.WordTrace tailWord_8386138 prefixEnd_8386138 4306119628934615430207859 := by
  unfold tailWord_8386138
  simp only [CollatzResearch.WordTrace]
  refine ⟨76466895223115434797297767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203911720594974492792794045 76466895223115434797297767)
  ·
    refine ⟨114700342834673152195946651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76466895223115434797297767 114700342834673152195946651)
    ·
      refine ⟨172050514252009728293919977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114700342834673152195946651 172050514252009728293919977)
      ·
        refine ⟨129037885689007296220439983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172050514252009728293919977 129037885689007296220439983)
        ·
          refine ⟨193556828533510944330659975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129037885689007296220439983 193556828533510944330659975)
          ·
            refine ⟨290335242800266416495989963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193556828533510944330659975 290335242800266416495989963)
            ·
              refine ⟨435502864200399624743984945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290335242800266416495989963 435502864200399624743984945)
              ·
                refine ⟨326627148150299718557988709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435502864200399624743984945 326627148150299718557988709)
                ·
                  refine ⟨61242590278181197229622883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326627148150299718557988709 61242590278181197229622883)
                  ·
                    refine ⟨91863885417271795844434325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61242590278181197229622883 91863885417271795844434325)
                    ·
                      refine ⟨4306119628934615430207859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91863885417271795844434325 4306119628934615430207859)
                      ·
                        rfl

theorem cell23_8386138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_8386138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386138 prefixEnd_8386138 := by exact prefixLift 8386138
  have htrace : WordTrace (prefixWord ++ tailWord_8386138) baseStart_8386138 baseEnd_8386138 := by
    simpa [prefixWord, tailWord_8386138, baseEnd_8386138] using wordTrace_append hprefix tailTrace_8386138
  have hstable : (prefixWord ++ tailWord_8386138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386138).length < 2 ^ (prefixWord ++ tailWord_8386138).sum := by decide
  have hdescent : baseEnd_8386138 < baseStart_8386138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386145 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_8386145 : Nat := 118140960795 + 8386145 * 2 ^ 59
def prefixEnd_8386145 : Nat := 4983230072969 + 3 ^ 40 * 8386145 * 2
def baseEnd_8386145 : Nat := 4306123223299196902820327

theorem tailTrace_8386145 : CollatzResearch.WordTrace tailWord_8386145 prefixEnd_8386145 4306123223299196902820327 := by
  unfold tailWord_8386145
  simp only [CollatzResearch.WordTrace]
  refine ⟨305867836203436379384695889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203911890802290919589797259 305867836203436379384695889)
  ·
    refine ⟨229400877152577284538521917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305867836203436379384695889 229400877152577284538521917)
    ·
      refine ⟨86025328932216481701945719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229400877152577284538521917 86025328932216481701945719)
      ·
        refine ⟨129037993398324722552918579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86025328932216481701945719 129037993398324722552918579)
        ·
          refine ⟨193556990097487083829377869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129037993398324722552918579 193556990097487083829377869)
          ·
            refine ⟨72583871286557656436016701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193556990097487083829377869 72583871286557656436016701)
            ·
              refine ⟨27218951732459121163506263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72583871286557656436016701 27218951732459121163506263)
              ·
                refine ⟨40828427598688681745259395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27218951732459121163506263 40828427598688681745259395)
                ·
                  refine ⟨61242641398033022617889093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40828427598688681745259395 61242641398033022617889093)
                  ·
                    refine ⟨11482995262131191740854205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61242641398033022617889093 11482995262131191740854205)
                    ·
                      refine ⟨4306123223299196902820327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11482995262131191740854205 4306123223299196902820327)
                      ·
                        rfl

theorem cell23_8386145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_8386145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386145 prefixEnd_8386145 := by exact prefixLift 8386145
  have htrace : WordTrace (prefixWord ++ tailWord_8386145) baseStart_8386145 baseEnd_8386145 := by
    simpa [prefixWord, tailWord_8386145, baseEnd_8386145] using wordTrace_append hprefix tailTrace_8386145
  have hstable : (prefixWord ++ tailWord_8386145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386145).length < 2 ^ (prefixWord ++ tailWord_8386145).sum := by decide
  have hdescent : baseEnd_8386145 < baseStart_8386145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386212 : List Nat := [2, 3, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_8386212 : Nat := 118140960795 + 8386212 * 2 ^ 59
def prefixEnd_8386212 : Nat := 4983230072969 + 3 ^ 40 * 8386212 * 2
def baseEnd_8386212 : Nat := 1435385875501016046894173

theorem tailTrace_8386212 : CollatzResearch.WordTrace tailWord_8386212 prefixEnd_8386212 1435385875501016046894173 := by
  unfold tailWord_8386212
  simp only [CollatzResearch.WordTrace]
  refine ⟨152935139947096824913692445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203913519929462433218256593 152935139947096824913692445)
  ·
    refine ⟨57350677480161309342634667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152935139947096824913692445 57350677480161309342634667)
    ·
      refine ⟨86026016220241964013952001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57350677480161309342634667 86026016220241964013952001)
      ·
        refine ⟨64519512165181473010464001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86026016220241964013952001 64519512165181473010464001)
        ·
          refine ⟨48389634123886104757848001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64519512165181473010464001 48389634123886104757848001)
          ·
            refine ⟨36292225592914578568386001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48389634123886104757848001 36292225592914578568386001)
            ·
              refine ⟨27219169194685933926289501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36292225592914578568386001 27219169194685933926289501)
              ·
                refine ⟨10207188448007225222358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27219169194685933926289501 10207188448007225222358563)
                ·
                  refine ⟨15310782672010837833537845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207188448007225222358563 15310782672010837833537845)
                  ·
                    refine ⟨1435385875501016046894173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15310782672010837833537845 1435385875501016046894173)
                    ·
                      rfl

theorem cell23_8386212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_8386212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386212 prefixEnd_8386212 := by exact prefixLift 8386212
  have htrace : WordTrace (prefixWord ++ tailWord_8386212) baseStart_8386212 baseEnd_8386212 := by
    simpa [prefixWord, tailWord_8386212, baseEnd_8386212] using wordTrace_append hprefix tailTrace_8386212
  have hstable : (prefixWord ++ tailWord_8386212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386212).length < 2 ^ (prefixWord ++ tailWord_8386212).sum := by decide
  have hdescent : baseEnd_8386212 < baseStart_8386212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386246 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_8386246 : Nat := 118140960795 + 8386246 * 2 ^ 59
def prefixEnd_8386246 : Nat := 4983230072969 + 3 ^ 40 * 8386246 * 2
def baseEnd_8386246 : Nat := 1435391694948433669219121

theorem tailTrace_8386246 : CollatzResearch.WordTrace tailWord_8386246 prefixEnd_8386246 1435391694948433669219121 := by
  unfold tailWord_8386246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558484999252202301066331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203914346650713649089415061 9558484999252202301066331)
  ·
    refine ⟨14337727498878303451599497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9558484999252202301066331 14337727498878303451599497)
    ·
      refine ⟨10753295624158727588699623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14337727498878303451599497 10753295624158727588699623)
      ·
        refine ⟨16129943436238091383049435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753295624158727588699623 16129943436238091383049435)
        ·
          refine ⟨24194915154357137074574153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129943436238091383049435 24194915154357137074574153)
          ·
            refine ⟨18146186365767852805930615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24194915154357137074574153 18146186365767852805930615)
            ·
              refine ⟨27219279548651779208895923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18146186365767852805930615 27219279548651779208895923)
              ·
                refine ⟨40828919322977668813343885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27219279548651779208895923 40828919322977668813343885)
                ·
                  refine ⟨15310844746116625805003957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40828919322977668813343885 15310844746116625805003957)
                  ·
                    refine ⟨1435391694948433669219121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15310844746116625805003957 1435391694948433669219121)
                    ·
                      rfl

theorem cell23_8386246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_8386246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386246 prefixEnd_8386246 := by exact prefixLift 8386246
  have htrace : WordTrace (prefixWord ++ tailWord_8386246) baseStart_8386246 baseEnd_8386246 := by
    simpa [prefixWord, tailWord_8386246, baseEnd_8386246] using wordTrace_append hprefix tailTrace_8386246
  have hstable : (prefixWord ++ tailWord_8386246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386246).length < 2 ^ (prefixWord ++ tailWord_8386246).sum := by decide
  have hdescent : baseEnd_8386246 < baseStart_8386246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386253 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_8386253 : Nat := 118140960795 + 8386253 * 2 ^ 59
def prefixEnd_8386253 : Nat := 4983230072969 + 3 ^ 40 * 8386253 * 2
def baseEnd_8386253 : Nat := 4306178679209882480269831

theorem tailTrace_8386253 : CollatzResearch.WordTrace tailWord_8386253 prefixEnd_8386253 4306178679209882480269831 := by
  unfold tailWord_8386253
  simp only [CollatzResearch.WordTrace]
  refine ⟨305871775287045113829627413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203914516858030075886418275 305871775287045113829627413)
  ·
    refine ⟨14337739466580239710763785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 305871775287045113829627413 14337739466580239710763785)
    ·
      refine ⟨10753304599935179783072839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14337739466580239710763785 10753304599935179783072839)
      ·
        refine ⟨16129956899902769674609259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753304599935179783072839 16129956899902769674609259)
        ·
          refine ⟨24194935349854154511913889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129956899902769674609259 24194935349854154511913889)
          ·
            refine ⟨18146201512390615883935417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24194935349854154511913889 18146201512390615883935417)
            ·
              refine ⟨13609651134292961912951563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18146201512390615883935417 13609651134292961912951563)
              ·
                refine ⟨20414476701439442869427345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13609651134292961912951563 20414476701439442869427345)
                ·
                  refine ⟨15310857526079582152070509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20414476701439442869427345 15310857526079582152070509)
                  ·
                    refine ⟨5741571572279843307026441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15310857526079582152070509 5741571572279843307026441)
                    ·
                      refine ⟨4306178679209882480269831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741571572279843307026441 4306178679209882480269831)
                      ·
                        rfl

theorem cell23_8386253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_8386253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386253 prefixEnd_8386253 := by exact prefixLift 8386253
  have htrace : WordTrace (prefixWord ++ tailWord_8386253) baseStart_8386253 baseEnd_8386253 := by
    simpa [prefixWord, tailWord_8386253, baseEnd_8386253] using wordTrace_append hprefix tailTrace_8386253
  have hstable : (prefixWord ++ tailWord_8386253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386253).length < 2 ^ (prefixWord ++ tailWord_8386253).sum := by decide
  have hdescent : baseEnd_8386253 < baseStart_8386253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386283 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 1, 2, 2]
def baseStart_8386283 : Nat := 118140960795 + 8386283 * 2 ^ 59
def prefixEnd_8386283 : Nat := 4983230072969 + 3 ^ 40 * 8386283 * 2
def baseEnd_8386283 : Nat := 4306194083629517362894693

theorem tailTrace_8386283 : CollatzResearch.WordTrace tailWord_8386283 prefixEnd_8386283 4306194083629517362894693 := by
  unfold tailWord_8386283
  simp only [CollatzResearch.WordTrace]
  refine ⟨305872869476936428953219503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203915246317957619302146335 305872869476936428953219503)
  ·
    refine ⟨458809304215404643429829255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305872869476936428953219503 458809304215404643429829255)
    ·
      refine ⟨688213956323106965144743883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458809304215404643429829255 688213956323106965144743883)
      ·
        refine ⟨1032320934484660447717115825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688213956323106965144743883 1032320934484660447717115825)
        ·
          refine ⟨774240700863495335787836869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032320934484660447717115825 774240700863495335787836869)
          ·
            refine ⟨145170131411905375460219413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774240700863495335787836869 145170131411905375460219413)
            ·
              refine ⟨6804849909933064474697785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145170131411905375460219413 6804849909933064474697785)
              ·
                refine ⟨5103637432449798356023339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6804849909933064474697785 5103637432449798356023339)
                ·
                  refine ⟨7655456148674697534035009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103637432449798356023339 7655456148674697534035009)
                  ·
                    refine ⟨5741592111506023150526257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7655456148674697534035009 5741592111506023150526257)
                    ·
                      refine ⟨4306194083629517362894693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741592111506023150526257 4306194083629517362894693)
                      ·
                        rfl

theorem cell23_8386283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 2, 2].length) (baseStart_8386283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386283 prefixEnd_8386283 := by exact prefixLift 8386283
  have htrace : WordTrace (prefixWord ++ tailWord_8386283) baseStart_8386283 baseEnd_8386283 := by
    simpa [prefixWord, tailWord_8386283, baseEnd_8386283] using wordTrace_append hprefix tailTrace_8386283
  have hstable : (prefixWord ++ tailWord_8386283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386283).length < 2 ^ (prefixWord ++ tailWord_8386283).sum := by decide
  have hdescent : baseEnd_8386283 < baseStart_8386283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386350 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_8386350 : Nat := 118140960795 + 8386350 * 2 ^ 59
def prefixEnd_8386350 : Nat := 4983230072969 + 3 ^ 40 * 8386350 * 2
def baseEnd_8386350 : Nat := 4306228486833368600756885

theorem tailTrace_8386350 : CollatzResearch.WordTrace tailWord_8386350 prefixEnd_8386350 4306228486833368600756885 := by
  unfold tailWord_8386350
  simp only [CollatzResearch.WordTrace]
  refine ⟨38234414145961712424488563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203916875445129132930605669 38234414145961712424488563)
  ·
    refine ⟨57351621218942568636732845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38234414145961712424488563 57351621218942568636732845)
    ·
      refine ⟨21506857957103463238774817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57351621218942568636732845 21506857957103463238774817)
      ·
        refine ⟨16130143467827597429081113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21506857957103463238774817 16130143467827597429081113)
        ·
          refine ⟨12097607600870698071810835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130143467827597429081113 12097607600870698071810835)
          ·
            refine ⟨18146411401306047107716253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12097607600870698071810835 18146411401306047107716253)
            ·
              refine ⟨6804904275489767665393595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18146411401306047107716253 6804904275489767665393595)
              ·
                refine ⟨10207356413234651498090393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804904275489767665393595 10207356413234651498090393)
                ·
                  refine ⟨7655517309925988623567795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10207356413234651498090393 7655517309925988623567795)
                  ·
                    refine ⟨11483275964888982935351693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7655517309925988623567795 11483275964888982935351693)
                    ·
                      refine ⟨4306228486833368600756885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11483275964888982935351693 4306228486833368600756885)
                      ·
                        rfl

theorem cell23_8386350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_8386350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386350 prefixEnd_8386350 := by exact prefixLift 8386350
  have htrace : WordTrace (prefixWord ++ tailWord_8386350) baseStart_8386350 baseEnd_8386350 := by
    simpa [prefixWord, tailWord_8386350, baseEnd_8386350] using wordTrace_append hprefix tailTrace_8386350
  have hstable : (prefixWord ++ tailWord_8386350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386350).length < 2 ^ (prefixWord ++ tailWord_8386350).sum := by decide
  have hdescent : baseEnd_8386350 < baseStart_8386350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386362 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_8386362 : Nat := 118140960795 + 8386362 * 2 ^ 59
def prefixEnd_8386362 : Nat := 4983230072969 + 3 ^ 40 * 8386362 * 2
def baseEnd_8386362 : Nat := 478470516511246950422981

theorem tailTrace_8386362 : CollatzResearch.WordTrace tailWord_8386362 prefixEnd_8386362 478470516511246950422981 := by
  unfold tailWord_8386362
  simp only [CollatzResearch.WordTrace]
  refine ⟨76468937710912556361336335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203917167229100150296896893 76468937710912556361336335)
  ·
    refine ⟨114703406566368834542004503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76468937710912556361336335 114703406566368834542004503)
    ·
      refine ⟨172055109849553251813006755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114703406566368834542004503 172055109849553251813006755)
      ·
        refine ⟨258082664774329877719510133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172055109849553251813006755 258082664774329877719510133)
        ·
          refine ⟨24195249822593426036204075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258082664774329877719510133 24195249822593426036204075)
          ·
            refine ⟨36292874733890139054306113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24195249822593426036204075 36292874733890139054306113)
            ·
              refine ⟨27219656050417604290729585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36292874733890139054306113 27219656050417604290729585)
              ·
                refine ⟨20414742037813203218047189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27219656050417604290729585 20414742037813203218047189)
                ·
                  refine ⟨478470516511246950422981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20414742037813203218047189 478470516511246950422981)
                  ·
                    rfl

theorem cell23_8386362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_8386362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386362 prefixEnd_8386362 := by exact prefixLift 8386362
  have htrace : WordTrace (prefixWord ++ tailWord_8386362) baseStart_8386362 baseEnd_8386362 := by
    simpa [prefixWord, tailWord_8386362, baseEnd_8386362] using wordTrace_append hprefix tailTrace_8386362
  have hstable : (prefixWord ++ tailWord_8386362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386362).length < 2 ^ (prefixWord ++ tailWord_8386362).sum := by decide
  have hdescent : baseEnd_8386362 < baseStart_8386362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386396 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 7]
def baseStart_8386396 : Nat := 118140960795 + 8386396 * 2 ^ 59
def prefixEnd_8386396 : Nat := 4983230072969 + 3 ^ 40 * 8386396 * 2
def baseEnd_8386396 : Nat := 478472456327052824531297

theorem tailTrace_8386396 : CollatzResearch.WordTrace tailWord_8386396 prefixEnd_8386396 478472456327052824531297 := by
  unfold tailWord_8386396
  simp only [CollatzResearch.WordTrace]
  refine ⟨152938495462763524626041521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203917993950351366168055361 152938495462763524626041521)
  ·
    refine ⟨114703871597072643469531141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152938495462763524626041521 114703871597072643469531141)
    ·
      refine ⟨21506975924451120650537089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114703871597072643469531141 21506975924451120650537089)
      ·
        refine ⟨16130231943338340487902817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21506975924451120650537089 16130231943338340487902817)
        ·
          refine ⟨12097673957503755365927113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130231943338340487902817 12097673957503755365927113)
          ·
            refine ⟨9073255468127816524445335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12097673957503755365927113 9073255468127816524445335)
            ·
              refine ⟨13609883202191724786668003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073255468127816524445335 13609883202191724786668003)
              ·
                refine ⟨20414824803287587180002005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13609883202191724786668003 20414824803287587180002005)
                ·
                  refine ⟨478472456327052824531297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20414824803287587180002005 478472456327052824531297)
                  ·
                    rfl

theorem cell23_8386396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 7].length) (baseStart_8386396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386396 prefixEnd_8386396 := by exact prefixLift 8386396
  have htrace : WordTrace (prefixWord ++ tailWord_8386396) baseStart_8386396 baseEnd_8386396 := by
    simpa [prefixWord, tailWord_8386396, baseEnd_8386396] using wordTrace_append hprefix tailTrace_8386396
  have hstable : (prefixWord ++ tailWord_8386396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386396).length < 2 ^ (prefixWord ++ tailWord_8386396).sum := by decide
  have hdescent : baseEnd_8386396 < baseStart_8386396 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386429 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 4, 4, 2]
def baseStart_8386429 : Nat := 118140960795 + 8386429 * 2 ^ 59
def prefixEnd_8386429 : Nat := 4983230072969 + 3 ^ 40 * 8386429 * 2
def baseEnd_8386429 : Nat := 4306269051805073791669021

theorem tailTrace_8386429 : CollatzResearch.WordTrace tailWord_8386429 prefixEnd_8386429 4306269051805073791669021 := by
  unfold tailWord_8386429
  simp only [CollatzResearch.WordTrace]
  refine ⟨305878194534407495888034341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203918796356271663925356227 305878194534407495888034341)
  ·
    refine ⟨57352161475201405479006439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305878194534407495888034341 57352161475201405479006439)
    ·
      refine ⟨86028242212802108218509659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57352161475201405479006439 86028242212802108218509659)
      ·
        refine ⟨129042363319203162327764489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86028242212802108218509659 129042363319203162327764489)
        ·
          refine ⟨96781772489402371745823367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129042363319203162327764489 96781772489402371745823367)
          ·
            refine ⟨145172658734103557618735051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96781772489402371745823367 145172658734103557618735051)
            ·
              refine ⟨217758988101155336428102577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145172658734103557618735051 217758988101155336428102577)
              ·
                refine ⟨163319241075866502321076933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217758988101155336428102577 163319241075866502321076933)
                ·
                  refine ⟨30622357701724969185201925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163319241075866502321076933 30622357701724969185201925)
                  ·
                    refine ⟨5741692069073431722225361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30622357701724969185201925 5741692069073431722225361)
                    ·
                      refine ⟨4306269051805073791669021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741692069073431722225361 4306269051805073791669021)
                      ·
                        rfl

theorem cell23_8386429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_8386429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386429 prefixEnd_8386429 := by exact prefixLift 8386429
  have htrace : WordTrace (prefixWord ++ tailWord_8386429) baseStart_8386429 baseEnd_8386429 := by
    simpa [prefixWord, tailWord_8386429, baseEnd_8386429] using wordTrace_append hprefix tailTrace_8386429
  have hstable : (prefixWord ++ tailWord_8386429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386429).length < 2 ^ (prefixWord ++ tailWord_8386429).sum := by decide
  have hdescent : baseEnd_8386429 < baseStart_8386429 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386449 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_8386449 : Nat := 118140960795 + 8386449 * 2 ^ 59
def prefixEnd_8386449 : Nat := 4983230072969 + 3 ^ 40 * 8386449 * 2
def baseEnd_8386449 : Nat := 4306279321418163713418929

theorem tailTrace_8386449 : CollatzResearch.WordTrace tailWord_8386449 prefixEnd_8386449 4306279321418163713418929 := by
  unfold tailWord_8386449
  simp only [CollatzResearch.WordTrace]
  refine ⟨305878923994335039303762401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203919282662890026202508267 305878923994335039303762401)
  ·
    refine ⟨229409192995751279477821801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305878923994335039303762401 229409192995751279477821801)
    ·
      refine ⟨172056894746813459608366351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229409192995751279477821801 172056894746813459608366351)
      ·
        refine ⟨258085342120220189412549527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172056894746813459608366351 258085342120220189412549527)
        ·
          refine ⟨387128013180330284118824291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258085342120220189412549527 387128013180330284118824291)
          ·
            refine ⟨580692019770495426178236437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387128013180330284118824291 580692019770495426178236437)
            ·
              refine ⟨27219938426741973102104833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 580692019770495426178236437 27219938426741973102104833)
              ·
                refine ⟨20414953820056479826578625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27219938426741973102104833 20414953820056479826578625)
                ·
                  refine ⟨15311215365042359869933969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20414953820056479826578625 15311215365042359869933969)
                  ·
                    refine ⟨11483411523781769902450477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15311215365042359869933969 11483411523781769902450477)
                    ·
                      refine ⟨4306279321418163713418929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11483411523781769902450477 4306279321418163713418929)
                      ·
                        rfl

theorem cell23_8386449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_8386449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386449 prefixEnd_8386449 := by exact prefixLift 8386449
  have htrace : WordTrace (prefixWord ++ tailWord_8386449) baseStart_8386449 baseEnd_8386449 := by
    simpa [prefixWord, tailWord_8386449, baseEnd_8386449] using wordTrace_append hprefix tailTrace_8386449
  have hstable : (prefixWord ++ tailWord_8386449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386449).length < 2 ^ (prefixWord ++ tailWord_8386449).sum := by decide
  have hdescent : baseEnd_8386449 < baseStart_8386449 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386506 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_8386506 : Nat := 118140960795 + 8386506 * 2 ^ 59
def prefixEnd_8386506 : Nat := 4983230072969 + 3 ^ 40 * 8386506 * 2
def baseEnd_8386506 : Nat := 4306308589815469990406167

theorem tailTrace_8386506 : CollatzResearch.WordTrace tailWord_8386506 prefixEnd_8386506 4306308589815469990406167 := by
  unfold tailWord_8386506
  simp only [CollatzResearch.WordTrace]
  refine ⟨76470250738782134509646843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203920668636752358692391581 76470250738782134509646843)
  ·
    refine ⟨114705376108173201764470265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76470250738782134509646843 114705376108173201764470265)
    ·
      refine ⟨86029032081129901323352699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114705376108173201764470265 86029032081129901323352699)
      ·
        refine ⟨129043548121694851985029049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86029032081129901323352699 129043548121694851985029049)
        ·
          refine ⟨96782661091271138988771787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129043548121694851985029049 96782661091271138988771787)
          ·
            refine ⟨145173991636906708483157681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96782661091271138988771787 145173991636906708483157681)
            ·
              refine ⟨108880493727680031362368261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145173991636906708483157681 108880493727680031362368261)
              ·
                refine ⟨20415092573940005880444049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108880493727680031362368261 20415092573940005880444049)
                ·
                  refine ⟨15311319430455004410333037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20415092573940005880444049 15311319430455004410333037)
                  ·
                    refine ⟨5741744786420626653874889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15311319430455004410333037 5741744786420626653874889)
                    ·
                      refine ⟨4306308589815469990406167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741744786420626653874889 4306308589815469990406167)
                      ·
                        rfl

theorem cell23_8386506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_8386506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386506 prefixEnd_8386506 := by exact prefixLift 8386506
  have htrace : WordTrace (prefixWord ++ tailWord_8386506) baseStart_8386506 baseEnd_8386506 := by
    simpa [prefixWord, tailWord_8386506, baseEnd_8386506] using wordTrace_append hprefix tailTrace_8386506
  have hstable : (prefixWord ++ tailWord_8386506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386506).length < 2 ^ (prefixWord ++ tailWord_8386506).sum := by decide
  have hdescent : baseEnd_8386506 < baseStart_8386506 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386512 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_8386512 : Nat := 118140960795 + 8386512 * 2 ^ 59
def prefixEnd_8386512 : Nat := 4983230072969 + 3 ^ 40 * 8386512 * 2
def baseEnd_8386512 : Nat := 1435437223566465655643713

theorem tailTrace_8386512 : CollatzResearch.WordTrace tailWord_8386512 prefixEnd_8386512 1435437223566465655643713 := by
  unfold tailWord_8386512
  simp only [CollatzResearch.WordTrace]
  refine ⟨152940610896553400531652895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203920814528737867375537193 152940610896553400531652895)
  ·
    refine ⟨229410916344830100797479343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152940610896553400531652895 229410916344830100797479343)
    ·
      refine ⟨344116374517245151196219015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229410916344830100797479343 344116374517245151196219015)
      ·
        refine ⟨516174561775867726794328523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344116374517245151196219015 516174561775867726794328523)
        ·
          refine ⟨774261842663801590191492785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516174561775867726794328523 774261842663801590191492785)
          ·
            refine ⟨580696381997851192643619589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774261842663801590191492785 580696381997851192643619589)
            ·
              refine ⟨108880571624597098620678673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 580696381997851192643619589 108880571624597098620678673)
              ·
                refine ⟨81660428718447823965509005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108880571624597098620678673 81660428718447823965509005)
                ·
                  refine ⟨30622660769417933987065877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81660428718447823965509005 30622660769417933987065877)
                  ·
                    refine ⟨1435437223566465655643713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30622660769417933987065877 1435437223566465655643713)
                    ·
                      rfl

theorem cell23_8386512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_8386512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386512 prefixEnd_8386512 := by exact prefixLift 8386512
  have htrace : WordTrace (prefixWord ++ tailWord_8386512) baseStart_8386512 baseEnd_8386512 := by
    simpa [prefixWord, tailWord_8386512, baseEnd_8386512] using wordTrace_append hprefix tailTrace_8386512
  have hstable : (prefixWord ++ tailWord_8386512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386512).length < 2 ^ (prefixWord ++ tailWord_8386512).sum := by decide
  have hdescent : baseEnd_8386512 < baseStart_8386512 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386529 : List Nat := [1, 2, 3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_8386529 : Nat := 118140960795 + 8386529 * 2 ^ 59
def prefixEnd_8386529 : Nat := 4983230072969 + 3 ^ 40 * 8386529 * 2
def baseEnd_8386529 : Nat := 1435440133290174466806187

theorem tailTrace_8386529 : CollatzResearch.WordTrace tailWord_8386529 prefixEnd_8386529 1435440133290174466806187 := by
  unfold tailWord_8386529
  simp only [CollatzResearch.WordTrace]
  refine ⟨305881841834045212966674641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203921227889363475311116427 305881841834045212966674641)
  ·
    refine ⟨229411381375533909725005981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305881841834045212966674641 229411381375533909725005981)
    ·
      refine ⟨86029268015825216146877243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229411381375533909725005981 86029268015825216146877243)
      ·
        refine ⟨129043902023737824220315865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86029268015825216146877243 129043902023737824220315865)
        ·
          refine ⟨96782926517803368165236899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129043902023737824220315865 96782926517803368165236899)
          ·
            refine ⟨145174389776705052247855349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96782926517803368165236899 145174389776705052247855349)
            ·
              refine ⟨13610099041566098648236439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145174389776705052247855349 13610099041566098648236439)
              ·
                refine ⟨20415148562349147972354659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13610099041566098648236439 20415148562349147972354659)
                ·
                  refine ⟨30622722843523721958531989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20415148562349147972354659 30622722843523721958531989)
                  ·
                    refine ⟨1435440133290174466806187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30622722843523721958531989 1435440133290174466806187)
                    ·
                      rfl

theorem cell23_8386529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_8386529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386529 prefixEnd_8386529 := by exact prefixLift 8386529
  have htrace : WordTrace (prefixWord ++ tailWord_8386529) baseStart_8386529 baseEnd_8386529 := by
    simpa [prefixWord, tailWord_8386529, baseEnd_8386529] using wordTrace_append hprefix tailTrace_8386529
  have hstable : (prefixWord ++ tailWord_8386529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386529).length < 2 ^ (prefixWord ++ tailWord_8386529).sum := by decide
  have hdescent : baseEnd_8386529 < baseStart_8386529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386539 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3]
def baseStart_8386539 : Nat := 118140960795 + 8386539 * 2 ^ 59
def prefixEnd_8386539 : Nat := 4983230072969 + 3 ^ 40 * 8386539 * 2
def baseEnd_8386539 : Nat := 4306325534677068361293515

theorem tailTrace_8386539 : CollatzResearch.WordTrace tailWord_8386539 prefixEnd_8386539 4306325534677068361293515 := by
  unfold tailWord_8386539
  simp only [CollatzResearch.WordTrace]
  refine ⟨305882206564008984674538671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203921471042672656449692447 305882206564008984674538671)
  ·
    refine ⟨458823309846013477011808007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305882206564008984674538671 458823309846013477011808007)
    ·
      refine ⟨688234964769020215517712011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458823309846013477011808007 688234964769020215517712011)
      ·
        refine ⟨1032352447153530323276568017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688234964769020215517712011 1032352447153530323276568017)
        ·
          refine ⟨774264335365147742457426013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1032352447153530323276568017 774264335365147742457426013)
          ·
            refine ⟨290349125761930403421534755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774264335365147742457426013 290349125761930403421534755)
            ·
              refine ⟨435523688642895605132302133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290349125761930403421534755 435523688642895605132302133)
              ·
                refine ⟨40830345810271462981153325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435523688642895605132302133 40830345810271462981153325)
                ·
                  refine ⟨15311379678851798617932497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40830345810271462981153325 15311379678851798617932497)
                  ·
                    refine ⟨11483534759138848963449373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15311379678851798617932497 11483534759138848963449373)
                    ·
                      refine ⟨4306325534677068361293515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11483534759138848963449373 4306325534677068361293515)
                      ·
                        rfl

theorem cell23_8386539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 3].length) (baseStart_8386539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386539 prefixEnd_8386539 := by exact prefixLift 8386539
  have htrace : WordTrace (prefixWord ++ tailWord_8386539) baseStart_8386539 baseEnd_8386539 := by
    simpa [prefixWord, tailWord_8386539, baseEnd_8386539] using wordTrace_append hprefix tailTrace_8386539
  have hstable : (prefixWord ++ tailWord_8386539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386539).length < 2 ^ (prefixWord ++ tailWord_8386539).sum := by decide
  have hdescent : baseEnd_8386539 < baseStart_8386539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386556 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 1, 2, 3]
def baseStart_8386556 : Nat := 118140960795 + 8386556 * 2 ^ 59
def prefixEnd_8386556 : Nat := 4983230072969 + 3 ^ 40 * 8386556 * 2
def baseEnd_8386556 : Nat := 4306334263848194794780937

theorem tailTrace_8386556 : CollatzResearch.WordTrace tailWord_8386556 prefixEnd_8386556 4306334263848194794780937 := by
  unfold tailWord_8386556
  simp only [CollatzResearch.WordTrace]
  refine ⟨152941413302473698288953761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203921884403298264385271681 152941413302473698288953761)
  ·
    refine ⟨114706059976855273716715321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152941413302473698288953761 114706059976855273716715321)
    ·
      refine ⟨86029544982641455287536491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114706059976855273716715321 86029544982641455287536491)
      ·
        refine ⟨129044317473962182931304737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86029544982641455287536491 129044317473962182931304737)
        ·
          refine ⟨96783238105471637198478553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129044317473962182931304737 96783238105471637198478553)
          ·
            refine ⟨72587428579103727898858915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96783238105471637198478553 72587428579103727898858915)
            ·
              refine ⟨108881142868655591848288373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72587428579103727898858915 108881142868655591848288373)
              ·
                refine ⟨10207607143936461735777035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108881142868655591848288373 10207607143936461735777035)
                ·
                  refine ⟨15311410715904692603665553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207607143936461735777035 15311410715904692603665553)
                  ·
                    refine ⟨11483558036928519452749165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15311410715904692603665553 11483558036928519452749165)
                    ·
                      refine ⟨4306334263848194794780937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11483558036928519452749165 4306334263848194794780937)
                      ·
                        rfl

theorem cell23_8386556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 2, 3].length) (baseStart_8386556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386556 prefixEnd_8386556 := by exact prefixLift 8386556
  have htrace : WordTrace (prefixWord ++ tailWord_8386556) baseStart_8386556 baseEnd_8386556 := by
    simpa [prefixWord, tailWord_8386556, baseEnd_8386556] using wordTrace_append hprefix tailTrace_8386556
  have hstable : (prefixWord ++ tailWord_8386556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386556).length < 2 ^ (prefixWord ++ tailWord_8386556).sum := by decide
  have hdescent : baseEnd_8386556 < baseStart_8386556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386564 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_8386564 : Nat := 118140960795 + 8386564 * 2 ^ 59
def prefixEnd_8386564 : Nat := 4983230072969 + 3 ^ 40 * 8386564 * 2
def baseEnd_8386564 : Nat := 4306338371693430763480901

theorem tailTrace_8386564 : CollatzResearch.WordTrace tailWord_8386564 prefixEnd_8386564 4306338371693430763480901 := by
  unfold tailWord_8386564
  simp only [CollatzResearch.WordTrace]
  refine ⟨152941559194459206972099373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203922078925945609296132497 152941559194459206972099373)
  ·
    refine ⟨57353084697922202614537265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152941559194459206972099373 57353084697922202614537265)
    ·
      refine ⟨43014813523441651960902949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57353084697922202614537265 43014813523441651960902949)
      ·
        refine ⟨8065277535645309742669303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43014813523441651960902949 8065277535645309742669303)
        ·
          refine ⟨12097916303467964614003955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065277535645309742669303 12097916303467964614003955)
          ·
            refine ⟨18146874455201946921005933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12097916303467964614003955 18146874455201946921005933)
            ·
              refine ⟨6805077920700730095377225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18146874455201946921005933 6805077920700730095377225)
              ·
                refine ⟨5103808440525547571532919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805077920700730095377225 5103808440525547571532919)
                ·
                  refine ⟨7655712660788321357299379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103808440525547571532919 7655712660788321357299379)
                  ·
                    refine ⟨11483568991182482035949069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7655712660788321357299379 11483568991182482035949069)
                    ·
                      refine ⟨4306338371693430763480901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11483568991182482035949069 4306338371693430763480901)
                      ·
                        rfl

theorem cell23_8386564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_8386564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386564 prefixEnd_8386564 := by exact prefixLift 8386564
  have htrace : WordTrace (prefixWord ++ tailWord_8386564) baseStart_8386564 baseEnd_8386564 := by
    simpa [prefixWord, tailWord_8386564, baseEnd_8386564] using wordTrace_append hprefix tailTrace_8386564
  have hstable : (prefixWord ++ tailWord_8386564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386564).length < 2 ^ (prefixWord ++ tailWord_8386564).sum := by decide
  have hdescent : baseEnd_8386564 < baseStart_8386564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386613 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_8386613 : Nat := 118140960795 + 8386613 * 2 ^ 59
def prefixEnd_8386613 : Nat := 4983230072969 + 3 ^ 40 * 8386613 * 2
def baseEnd_8386613 : Nat := 4306363532245501071768175

theorem tailTrace_8386613 : CollatzResearch.WordTrace tailWord_8386613 prefixEnd_8386613 4306363532245501071768175 := by
  unfold tailWord_8386613
  simp only [CollatzResearch.WordTrace]
  refine ⟨305884905565740895312732493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203923270377160596875154995 305884905565740895312732493)
  ·
    refine ⟨114706839587152835742274685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305884905565740895312732493 114706839587152835742274685)
    ·
      refine ⟨43015064845182313403353007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114706839587152835742274685 43015064845182313403353007)
      ·
        refine ⟨64522597267773470105029511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43015064845182313403353007 64522597267773470105029511)
        ·
          refine ⟨96783895901660205157544267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64522597267773470105029511 96783895901660205157544267)
          ·
            refine ⟨145175843852490307736316401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96783895901660205157544267 145175843852490307736316401)
            ·
              refine ⟨108881882889367730802237301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145175843852490307736316401 108881882889367730802237301)
              ·
                refine ⟨10207676520878224762709747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108881882889367730802237301 10207676520878224762709747)
                ·
                  refine ⟨15311514781317337144064621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207676520878224762709747 15311514781317337144064621)
                  ·
                    refine ⟨5741818042994001429024233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15311514781317337144064621 5741818042994001429024233)
                    ·
                      refine ⟨4306363532245501071768175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741818042994001429024233 4306363532245501071768175)
                      ·
                        rfl

theorem cell23_8386613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_8386613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386613 prefixEnd_8386613 := by exact prefixLift 8386613
  have htrace : WordTrace (prefixWord ++ tailWord_8386613) baseStart_8386613 baseEnd_8386613 := by
    simpa [prefixWord, tailWord_8386613, baseEnd_8386613] using wordTrace_append hprefix tailTrace_8386613
  have hstable : (prefixWord ++ tailWord_8386613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386613).length < 2 ^ (prefixWord ++ tailWord_8386613).sum := by decide
  have hdescent : baseEnd_8386613 < baseStart_8386613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386630 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_8386630 : Nat := 118140960795 + 8386630 * 2 ^ 59
def prefixEnd_8386630 : Nat := 4983230072969 + 3 ^ 40 * 8386630 * 2
def baseEnd_8386630 : Nat := 4306372261416627505255597

theorem tailTrace_8386630 : CollatzResearch.WordTrace tailWord_8386630 prefixEnd_8386630 4306372261416627505255597 := by
  unfold tailWord_8386630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9558922675208728350503167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203923683737786204810734229 9558922675208728350503167)
  ·
    refine ⟨14338384012813092525754751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9558922675208728350503167 14338384012813092525754751)
    ·
      refine ⟨21507576019219638788632127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14338384012813092525754751 21507576019219638788632127)
      ·
        refine ⟨32261364028829458182948191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21507576019219638788632127 32261364028829458182948191)
        ·
          refine ⟨48392046043244187274422287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32261364028829458182948191 48392046043244187274422287)
          ·
            refine ⟨72588069064866280911633431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48392046043244187274422287 72588069064866280911633431)
            ·
              refine ⟨108882103597299421367450147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72588069064866280911633431 108882103597299421367450147)
              ·
                refine ⟨163323155395949132051175221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108882103597299421367450147 163323155395949132051175221)
                ·
                  refine ⟨15311545818370231129797677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163323155395949132051175221 15311545818370231129797677)
                  ·
                    refine ⟨5741829681888836673674129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15311545818370231129797677 5741829681888836673674129)
                    ·
                      refine ⟨4306372261416627505255597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741829681888836673674129 4306372261416627505255597)
                      ·
                        rfl

theorem cell23_8386630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_8386630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386630 prefixEnd_8386630 := by exact prefixLift 8386630
  have htrace : WordTrace (prefixWord ++ tailWord_8386630) baseStart_8386630 baseEnd_8386630 := by
    simpa [prefixWord, tailWord_8386630, baseEnd_8386630] using wordTrace_append hprefix tailTrace_8386630
  have hstable : (prefixWord ++ tailWord_8386630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386630).length < 2 ^ (prefixWord ++ tailWord_8386630).sum := by decide
  have hdescent : baseEnd_8386630 < baseStart_8386630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386639 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_8386639 : Nat := 118140960795 + 8386639 * 2 ^ 59
def prefixEnd_8386639 : Nat := 4983230072969 + 3 ^ 40 * 8386639 * 2
def baseEnd_8386639 : Nat := 4306376882742517970043055

theorem tailTrace_8386639 : CollatzResearch.WordTrace tailWord_8386639 prefixEnd_8386639 4306376882742517970043055 := by
  unfold tailWord_8386639
  simp only [CollatzResearch.WordTrace]
  refine ⟨305885853863646701753178971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203923902575764467835452647 305885853863646701753178971)
  ·
    refine ⟨458828780795470052629768457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305885853863646701753178971 458828780795470052629768457)
    ·
      refine ⟨344121585596602539472326343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458828780795470052629768457 344121585596602539472326343)
      ·
        refine ⟨516182378394903809208489515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344121585596602539472326343 516182378394903809208489515)
        ·
          refine ⟨774273567592355713812734273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516182378394903809208489515 774273567592355713812734273)
          ·
            refine ⟨580705175694266785359550705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774273567592355713812734273 580705175694266785359550705)
            ·
              refine ⟨435528881770700089019663029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580705175694266785359550705 435528881770700089019663029)
              ·
                refine ⟨40830832666003133345593409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435528881770700089019663029 40830832666003133345593409)
                ·
                  refine ⟨30623124499502350009195057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40830832666003133345593409 30623124499502350009195057)
                  ·
                    refine ⟨22967343374626762506896293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30623124499502350009195057 22967343374626762506896293)
                    ·
                      refine ⟨4306376882742517970043055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22967343374626762506896293 4306376882742517970043055)
                      ·
                        rfl

theorem cell23_8386639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_8386639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386639 prefixEnd_8386639 := by exact prefixLift 8386639
  have htrace : WordTrace (prefixWord ++ tailWord_8386639) baseStart_8386639 baseEnd_8386639 := by
    simpa [prefixWord, tailWord_8386639, baseEnd_8386639] using wordTrace_append hprefix tailTrace_8386639
  have hstable : (prefixWord ++ tailWord_8386639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386639).length < 2 ^ (prefixWord ++ tailWord_8386639).sum := by decide
  have hdescent : baseEnd_8386639 < baseStart_8386639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386649 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 7]
def baseStart_8386649 : Nat := 118140960795 + 8386649 * 2 ^ 59
def prefixEnd_8386649 : Nat := 4983230072969 + 3 ^ 40 * 8386649 * 2
def baseEnd_8386649 : Nat := 478486890838784770102001

theorem tailTrace_8386649 : CollatzResearch.WordTrace tailWord_8386649 prefixEnd_8386649 478486890838784770102001 := by
  unfold tailWord_8386649
  simp only [CollatzResearch.WordTrace]
  refine ⟨305886218593610473461043001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203924145729073648974028667 305886218593610473461043001)
  ·
    refine ⟨229414663945207855095782251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305886218593610473461043001 229414663945207855095782251)
    ·
      refine ⟨344121995917811782643673377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229414663945207855095782251 344121995917811782643673377)
      ·
        refine ⟨258091496938358836982755033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344121995917811782643673377 258091496938358836982755033)
        ·
          refine ⟨193568622703769127737066275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258091496938358836982755033 193568622703769127737066275)
          ·
            refine ⟨290352934055653691605599413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193568622703769127737066275 290352934055653691605599413)
            ·
              refine ⟨27220587567717533588024945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 290352934055653691605599413 27220587567717533588024945)
              ·
                refine ⟨20415440675788150191018709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27220587567717533588024945 20415440675788150191018709)
                ·
                  refine ⟨478486890838784770102001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20415440675788150191018709 478486890838784770102001)
                  ·
                    rfl

theorem cell23_8386649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_8386649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386649 prefixEnd_8386649 := by exact prefixLift 8386649
  have htrace : WordTrace (prefixWord ++ tailWord_8386649) baseStart_8386649 baseEnd_8386649 := by
    simpa [prefixWord, tailWord_8386649, baseEnd_8386649] using wordTrace_append hprefix tailTrace_8386649
  have hstable : (prefixWord ++ tailWord_8386649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386649).length < 2 ^ (prefixWord ++ tailWord_8386649).sum := by decide
  have hdescent : baseEnd_8386649 < baseStart_8386649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386696 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_8386696 : Nat := 118140960795 + 8386696 * 2 ^ 59
def prefixEnd_8386696 : Nat := 4983230072969 + 3 ^ 40 * 8386696 * 2
def baseEnd_8386696 : Nat := 1435468717046608082343431

theorem tailTrace_8386696 : CollatzResearch.WordTrace tailWord_8386696 prefixEnd_8386696 1435468717046608082343431 := by
  unfold tailWord_8386696
  simp only [CollatzResearch.WordTrace]
  refine ⟨152943966412220100244001971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203925288549626800325335961 152943966412220100244001971)
  ·
    refine ⟨229415949618330150366002957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152943966412220100244001971 229415949618330150366002957)
    ·
      refine ⟨86030981106873806387251109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229415949618330150366002957 86030981106873806387251109)
      ·
        refine ⟨16130808957538838697609583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86030981106873806387251109 16130808957538838697609583)
        ·
          refine ⟨24196213436308258046414375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16130808957538838697609583 24196213436308258046414375)
          ·
            refine ⟨36294320154462387069621563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24196213436308258046414375 36294320154462387069621563)
            ·
              refine ⟨54441480231693580604432345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36294320154462387069621563 54441480231693580604432345)
              ·
                refine ⟨40831110173770185453324259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54441480231693580604432345 40831110173770185453324259)
                ·
                  refine ⟨61246665260655278179986389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40831110173770185453324259 61246665260655278179986389)
                  ·
                    refine ⟨1435468717046608082343431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 61246665260655278179986389 1435468717046608082343431)
                    ·
                      rfl

theorem cell23_8386696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_8386696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386696 prefixEnd_8386696 := by exact prefixLift 8386696
  have htrace : WordTrace (prefixWord ++ tailWord_8386696) baseStart_8386696 baseEnd_8386696 := by
    simpa [prefixWord, tailWord_8386696, baseEnd_8386696] using wordTrace_append hprefix tailTrace_8386696
  have hstable : (prefixWord ++ tailWord_8386696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386696).length < 2 ^ (prefixWord ++ tailWord_8386696).sum := by decide
  have hdescent : baseEnd_8386696 < baseStart_8386696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386709 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_8386709 : Nat := 118140960795 + 8386709 * 2 ^ 59
def prefixEnd_8386709 : Nat := 4983230072969 + 3 ^ 40 * 8386709 * 2
def baseEnd_8386709 : Nat := 1435470942129444232055911

theorem tailTrace_8386709 : CollatzResearch.WordTrace tailWord_8386709 prefixEnd_8386709 1435470942129444232055911 := by
  unfold tailWord_8386709
  simp only [CollatzResearch.WordTrace]
  refine ⟨305888406973393103708227181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203925604648928735805484787 305888406973393103708227181)
  ·
    refine ⟨114708152615022413890585193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305888406973393103708227181 114708152615022413890585193)
    ·
      refine ⟨86031114461266810417938895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114708152615022413890585193 86031114461266810417938895)
      ·
        refine ⟨129046671691900215626908343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86031114461266810417938895 129046671691900215626908343)
        ·
          refine ⟨193570007537850323440362515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129046671691900215626908343 193570007537850323440362515)
          ·
            refine ⟨290355011306775485160543773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193570007537850323440362515 290355011306775485160543773)
            ·
              refine ⟨108883129240040806935203915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290355011306775485160543773 108883129240040806935203915)
              ·
                refine ⟨163324693860061210402805873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108883129240040806935203915 163324693860061210402805873)
                ·
                  refine ⟨122493520395045907802104405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163324693860061210402805873 122493520395045907802104405)
                  ·
                    refine ⟨1435470942129444232055911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 122493520395045907802104405 1435470942129444232055911)
                    ·
                      rfl

theorem cell23_8386709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_8386709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386709 prefixEnd_8386709 := by exact prefixLift 8386709
  have htrace : WordTrace (prefixWord ++ tailWord_8386709) baseStart_8386709 baseEnd_8386709 := by
    simpa [prefixWord, tailWord_8386709, baseEnd_8386709] using wordTrace_append hprefix tailTrace_8386709
  have hstable : (prefixWord ++ tailWord_8386709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386709).length < 2 ^ (prefixWord ++ tailWord_8386709).sum := by decide
  have hdescent : baseEnd_8386709 < baseStart_8386709 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386716 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_8386716 : Nat := 118140960795 + 8386716 * 2 ^ 59
def prefixEnd_8386716 : Nat := 4983230072969 + 3 ^ 40 * 8386716 * 2
def baseEnd_8386716 : Nat := 4306416420752914168780201

theorem tailTrace_8386716 : CollatzResearch.WordTrace tailWord_8386716 prefixEnd_8386716 4306416420752914168780201 := by
  unfold tailWord_8386716
  simp only [CollatzResearch.WordTrace]
  refine ⟨152944331142183871951866001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203925774856245162602488001 152944331142183871951866001)
  ·
    refine ⟨114708248356637903963899501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152944331142183871951866001 114708248356637903963899501)
    ·
      refine ⟨43015593133739213986462313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114708248356637903963899501 43015593133739213986462313)
      ·
        refine ⟨32261694850304410489846735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43015593133739213986462313 32261694850304410489846735)
        ·
          refine ⟨48392542275456615734770103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32261694850304410489846735 48392542275456615734770103)
          ·
            refine ⟨72588813413184923602155155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48392542275456615734770103 72588813413184923602155155)
            ·
              refine ⟨108883220119777385403232733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72588813413184923602155155 108883220119777385403232733)
              ·
                refine ⟨40831207544916519526212275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108883220119777385403232733 40831207544916519526212275)
                ·
                  refine ⟨61246811317374779289318413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40831207544916519526212275 61246811317374779289318413)
                  ·
                    refine ⟨22967554244015542233494405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61246811317374779289318413 22967554244015542233494405)
                    ·
                      refine ⟨4306416420752914168780201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22967554244015542233494405 4306416420752914168780201)
                      ·
                        rfl

theorem cell23_8386716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_8386716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386716 prefixEnd_8386716 := by exact prefixLift 8386716
  have htrace : WordTrace (prefixWord ++ tailWord_8386716) baseStart_8386716 baseEnd_8386716 := by
    simpa [prefixWord, tailWord_8386716, baseEnd_8386716] using wordTrace_append hprefix tailTrace_8386716
  have hstable : (prefixWord ++ tailWord_8386716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386716).length < 2 ^ (prefixWord ++ tailWord_8386716).sum := by decide
  have hdescent : baseEnd_8386716 < baseStart_8386716 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386730 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 2, 5]
def baseStart_8386730 : Nat := 118140960795 + 8386730 * 2 ^ 59
def prefixEnd_8386730 : Nat := 4983230072969 + 3 ^ 40 * 8386730 * 2
def baseEnd_8386730 : Nat := 1435474536494025704668379

theorem tailTrace_8386730 : CollatzResearch.WordTrace tailWord_8386730 prefixEnd_8386730 1435474536494025704668379 := by
  unfold tailWord_8386730
  simp only [CollatzResearch.WordTrace]
  refine ⟨76472293226579256073685411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203926115270878016196494429 76472293226579256073685411)
  ·
    refine ⟨114708439839868884110528117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76472293226579256073685411 114708439839868884110528117)
    ·
      refine ⟨10753916234987707885362011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114708439839868884110528117 10753916234987707885362011)
      ·
        refine ⟨16130874352481561828043017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753916234987707885362011 16130874352481561828043017)
        ·
          refine ⟨12098155764361171371032263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130874352481561828043017 12098155764361171371032263)
          ·
            refine ⟨18147233646541757056548395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098155764361171371032263 18147233646541757056548395)
            ·
              refine ⟨27220850469812635584822593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18147233646541757056548395 27220850469812635584822593)
              ·
                refine ⟨20415637852359476688616945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27220850469812635584822593 20415637852359476688616945)
                ·
                  refine ⟨15311728389269607516462709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20415637852359476688616945 15311728389269607516462709)
                  ·
                    refine ⟨1435474536494025704668379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15311728389269607516462709 1435474536494025704668379)
                    ·
                      rfl

theorem cell23_8386730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_8386730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386730 prefixEnd_8386730 := by exact prefixLift 8386730
  have htrace : WordTrace (prefixWord ++ tailWord_8386730) baseStart_8386730 baseEnd_8386730 := by
    simpa [prefixWord, tailWord_8386730, baseEnd_8386730] using wordTrace_append hprefix tailTrace_8386730
  have hstable : (prefixWord ++ tailWord_8386730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386730).length < 2 ^ (prefixWord ++ tailWord_8386730).sum := by decide
  have hdescent : baseEnd_8386730 < baseStart_8386730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386733 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_8386733 : Nat := 118140960795 + 8386733 * 2 ^ 59
def prefixEnd_8386733 : Nat := 4983230072969 + 3 ^ 40 * 8386733 * 2
def baseEnd_8386733 : Nat := 4306425149924040602267623

theorem tailTrace_8386733 : CollatzResearch.WordTrace tailWord_8386733 prefixEnd_8386733 4306425149924040602267623 := by
  unfold tailWord_8386733
  simp only [CollatzResearch.WordTrace]
  refine ⟨305889282325306155807100853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203926188216870770538067235 305889282325306155807100853)
  ·
    refine ⟨28677120217997452106915705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305889282325306155807100853 28677120217997452106915705)
    ·
      refine ⟨21507840163498089080186779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28677120217997452106915705 21507840163498089080186779)
      ·
        refine ⟨32261760245247133620280169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21507840163498089080186779 32261760245247133620280169)
        ·
          refine ⟨24196320183935350215210127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32261760245247133620280169 24196320183935350215210127)
          ·
            refine ⟨36294480275903025322815191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24196320183935350215210127 36294480275903025322815191)
            ·
              refine ⟨54441720413854537984222787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36294480275903025322815191 54441720413854537984222787)
              ·
                refine ⟨81662580620781806976334181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54441720413854537984222787 81662580620781806976334181)
                ·
                  refine ⟨15311733866396588808062659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81662580620781806976334181 15311733866396588808062659)
                  ·
                    refine ⟨22967600799594883212093989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15311733866396588808062659 22967600799594883212093989)
                    ·
                      refine ⟨4306425149924040602267623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22967600799594883212093989 4306425149924040602267623)
                      ·
                        rfl

theorem cell23_8386733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_8386733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386733 prefixEnd_8386733 := by exact prefixLift 8386733
  have htrace : WordTrace (prefixWord ++ tailWord_8386733) baseStart_8386733 baseEnd_8386733 := by
    simpa [prefixWord, tailWord_8386733, baseEnd_8386733] using wordTrace_append hprefix tailTrace_8386733
  have hstable : (prefixWord ++ tailWord_8386733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386733).length < 2 ^ (prefixWord ++ tailWord_8386733).sum := by decide
  have hdescent : baseEnd_8386733 < baseStart_8386733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386734 : List Nat := [4, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_8386734 : Nat := 118140960795 + 8386734 * 2 ^ 59
def prefixEnd_8386734 : Nat := 4983230072969 + 3 ^ 40 * 8386734 * 2
def baseEnd_8386734 : Nat := 478491740378299455372791

theorem tailTrace_8386734 : CollatzResearch.WordTrace tailWord_8386734 prefixEnd_8386734 478491740378299455372791 := by
  unfold tailWord_8386734
  simp only [CollatzResearch.WordTrace]
  refine ⟨38236164849787816622235907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203926212532201688651924837 38236164849787816622235907)
  ·
    refine ⟨57354247274681724933353861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38236164849787816622235907 57354247274681724933353861)
    ·
      refine ⟨10753921364002823425003849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57354247274681724933353861 10753921364002823425003849)
      ·
        refine ⟨8065441023002117568752887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10753921364002823425003849 8065441023002117568752887)
        ·
          refine ⟨12098161534503176353129331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065441023002117568752887 12098161534503176353129331)
          ·
            refine ⟨18147242301754764529693997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098161534503176353129331 18147242301754764529693997)
            ·
              refine ⟨6805215863158036698635249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18147242301754764529693997 6805215863158036698635249)
              ·
                refine ⟨5103911897368527523976437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805215863158036698635249 5103911897368527523976437)
                ·
                  refine ⟨478491740378299455372791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5103911897368527523976437 478491740378299455372791)
                  ·
                    rfl

theorem cell23_8386734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_8386734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386734 prefixEnd_8386734 := by exact prefixLift 8386734
  have htrace : WordTrace (prefixWord ++ tailWord_8386734) baseStart_8386734 baseEnd_8386734 := by
    simpa [prefixWord, tailWord_8386734, baseEnd_8386734] using wordTrace_append hprefix tailTrace_8386734
  have hstable : (prefixWord ++ tailWord_8386734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386734).length < 2 ^ (prefixWord ++ tailWord_8386734).sum := by decide
  have hdescent : baseEnd_8386734 < baseStart_8386734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386743 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 3, 4]
def baseStart_8386743 : Nat := 118140960795 + 8386743 * 2 ^ 59
def prefixEnd_8386743 : Nat := 4983230072969 + 3 ^ 40 * 8386743 * 2
def baseEnd_8386743 : Nat := 1435476761576861854380859

theorem tailTrace_8386743 : CollatzResearch.WordTrace tailWord_8386743 prefixEnd_8386743 1435476761576861854380859 := by
  unfold tailWord_8386743
  simp only [CollatzResearch.WordTrace]
  refine ⟨305889647055269927514964883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203926431370179951676643255 305889647055269927514964883)
  ·
    refine ⟨458834470582904891272447325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305889647055269927514964883 458834470582904891272447325)
    ·
      refine ⟨172062926468589334227167747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458834470582904891272447325 172062926468589334227167747)
      ·
        refine ⟨258094389702884001340751621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172062926468589334227167747 258094389702884001340751621)
        ·
          refine ⟨48392698069290750251390929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258094389702884001340751621 48392698069290750251390929)
          ·
            refine ⟨36294523551968062688543197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48392698069290750251390929 36294523551968062688543197)
            ·
              refine ⟨13610446331988023508203699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36294523551968062688543197 13610446331988023508203699)
              ·
                refine ⟨20415669497982035262305549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13610446331988023508203699 20415669497982035262305549)
                ·
                  refine ⟨7655876061743263223364581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20415669497982035262305549 7655876061743263223364581)
                  ·
                    refine ⟨1435476761576861854380859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7655876061743263223364581 1435476761576861854380859)
                    ·
                      rfl

theorem cell23_8386743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_8386743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386743 prefixEnd_8386743 := by exact prefixLift 8386743
  have htrace : WordTrace (prefixWord ++ tailWord_8386743) baseStart_8386743 baseEnd_8386743 := by
    simpa [prefixWord, tailWord_8386743, baseEnd_8386743] using wordTrace_append hprefix tailTrace_8386743
  have hstable : (prefixWord ++ tailWord_8386743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386743).length < 2 ^ (prefixWord ++ tailWord_8386743).sum := by decide
  have hdescent : baseEnd_8386743 < baseStart_8386743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386770 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 2, 2, 3]
def baseStart_8386770 : Nat := 118140960795 + 8386770 * 2 ^ 59
def prefixEnd_8386770 : Nat := 4983230072969 + 3 ^ 40 * 8386770 * 2
def baseEnd_8386770 : Nat := 4306444148708256957504953

theorem tailTrace_8386770 : CollatzResearch.WordTrace tailWord_8386770 prefixEnd_8386770 4306444148708256957504953 := by
  unfold tailWord_8386770
  simp only [CollatzResearch.WordTrace]
  refine ⟨76472657956543027781549441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203927087884114740750798509 76472657956543027781549441)
  ·
    refine ⟨57354493467407270836162081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76472657956543027781549441 57354493467407270836162081)
    ·
      refine ⟨43015870100555453127121561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57354493467407270836162081 43015870100555453127121561)
      ·
        refine ⟨32261902575416589845341171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43015870100555453127121561 32261902575416589845341171)
        ·
          refine ⟨48392853863124884768011757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32261902575416589845341171 48392853863124884768011757)
          ·
            refine ⟨18147320198671831788004409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48392853863124884768011757 18147320198671831788004409)
            ·
              refine ⟨13610490149003873841003307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18147320198671831788004409 13610490149003873841003307)
              ·
                refine ⟨20415735223505810761504961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13610490149003873841003307 20415735223505810761504961)
                ·
                  refine ⟨15311801417629358071128721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20415735223505810761504961 15311801417629358071128721)
                  ·
                    refine ⟨11483851063222018553346541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15311801417629358071128721 11483851063222018553346541)
                    ·
                      refine ⟨4306444148708256957504953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11483851063222018553346541 4306444148708256957504953)
                      ·
                        rfl

theorem cell23_8386770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_8386770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386770 prefixEnd_8386770 := by exact prefixLift 8386770
  have htrace : WordTrace (prefixWord ++ tailWord_8386770) baseStart_8386770 baseEnd_8386770 := by
    simpa [prefixWord, tailWord_8386770, baseEnd_8386770] using wordTrace_append hprefix tailTrace_8386770
  have hstable : (prefixWord ++ tailWord_8386770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386770).length < 2 ^ (prefixWord ++ tailWord_8386770).sum := by decide
  have hdescent : baseEnd_8386770 < baseStart_8386770 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386816 : List Nat := [2, 1, 1, 2, 1, 1, 5, 3, 1, 6]
def baseStart_8386816 : Nat := 118140960795 + 8386816 * 2 ^ 59
def prefixEnd_8386816 : Nat := 4983230072969 + 3 ^ 40 * 8386816 * 2
def baseEnd_8386816 : Nat := 1435489256272787925843247

theorem tailTrace_8386816 : CollatzResearch.WordTrace tailWord_8386816 prefixEnd_8386816 1435489256272787925843247 := by
  unfold tailWord_8386816
  simp only [CollatzResearch.WordTrace]
  refine ⟨152946154792002730491186151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203928206389336973988248201 152946154792002730491186151)
  ·
    refine ⟨229419232188004095736779227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152946154792002730491186151 229419232188004095736779227)
    ·
      refine ⟨344128848282006143605168841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229419232188004095736779227 344128848282006143605168841)
      ·
        refine ⟨258096636211504607703876631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344128848282006143605168841 258096636211504607703876631)
        ·
          refine ⟨387144954317256911555814947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258096636211504607703876631 387144954317256911555814947)
          ·
            refine ⟨580717431475885367333722421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387144954317256911555814947 580717431475885367333722421)
            ·
              refine ⟨54442259200864253187536477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 580717431475885367333722421 54442259200864253187536477)
              ·
                refine ⟨20415847200324094945326179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54442259200864253187536477 20415847200324094945326179)
                ·
                  refine ⟨30623770800486142417989269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20415847200324094945326179 30623770800486142417989269)
                  ·
                    refine ⟨1435489256272787925843247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30623770800486142417989269 1435489256272787925843247)
                    ·
                      rfl

theorem cell23_8386816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_8386816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386816 prefixEnd_8386816 := by exact prefixLift 8386816
  have htrace : WordTrace (prefixWord ++ tailWord_8386816) baseStart_8386816 baseEnd_8386816 := by
    simpa [prefixWord, tailWord_8386816, baseEnd_8386816] using wordTrace_append hprefix tailTrace_8386816
  have hstable : (prefixWord ++ tailWord_8386816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386816).length < 2 ^ (prefixWord ++ tailWord_8386816).sum := by decide
  have hdescent : baseEnd_8386816 < baseStart_8386816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386840 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2]
def baseStart_8386840 : Nat := 118140960795 + 8386840 * 2 ^ 59
def prefixEnd_8386840 : Nat := 4983230072969 + 3 ^ 40 * 8386840 * 2
def baseEnd_8386840 : Nat := 4306480092354071683629631

theorem tailTrace_8386840 : CollatzResearch.WordTrace tailWord_8386840 prefixEnd_8386840 4306480092354071683629631 := by
  unfold tailWord_8386840
  simp only [CollatzResearch.WordTrace]
  refine ⟨152946592467959256540622987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203928789957279008720830649 152946592467959256540622987)
  ·
    refine ⟨229419888701938884810934481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152946592467959256540622987 229419888701938884810934481)
    ·
      refine ⟨172064916526454163608200861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229419888701938884810934481 172064916526454163608200861)
      ·
        refine ⟨64524343697420311353075323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172064916526454163608200861 64524343697420311353075323)
        ·
          refine ⟨96786515546130467029612985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64524343697420311353075323 96786515546130467029612985)
          ·
            refine ⟨72589886659597850272209739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96786515546130467029612985 72589886659597850272209739)
            ·
              refine ⟨108884829989396775408314609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72589886659597850272209739 108884829989396775408314609)
              ·
                refine ⟨81663622492047581556235957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108884829989396775408314609 81663622492047581556235957)
                ·
                  refine ⟨7655964608629460770897121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81663622492047581556235957 7655964608629460770897121)
                  ·
                    refine ⟨5741973456472095578172841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7655964608629460770897121 5741973456472095578172841)
                    ·
                      refine ⟨4306480092354071683629631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5741973456472095578172841 4306480092354071683629631)
                      ·
                        rfl

theorem cell23_8386840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_8386840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386840 prefixEnd_8386840 := by exact prefixLift 8386840
  have htrace : WordTrace (prefixWord ++ tailWord_8386840) baseStart_8386840 baseEnd_8386840 := by
    simpa [prefixWord, tailWord_8386840, baseEnd_8386840] using wordTrace_append hprefix tailTrace_8386840
  have hstable : (prefixWord ++ tailWord_8386840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386840).length < 2 ^ (prefixWord ++ tailWord_8386840).sum := by decide
  have hdescent : baseEnd_8386840 < baseStart_8386840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386850 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 4, 4]
def baseStart_8386850 : Nat := 118140960795 + 8386850 * 2 ^ 59
def prefixEnd_8386850 : Nat := 4983230072969 + 3 ^ 40 * 8386850 * 2
def baseEnd_8386850 : Nat := 1435495075720205548168195

theorem tailTrace_8386850 : CollatzResearch.WordTrace tailWord_8386850 prefixEnd_8386850 1435495075720205548168195 := by
  unfold tailWord_8386850
  simp only [CollatzResearch.WordTrace]
  refine ⟨76473387416470571197277501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203929033110588189859406669 76473387416470571197277501)
  ·
    refine ⟨28677520281176464198979063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76473387416470571197277501 28677520281176464198979063)
    ·
      refine ⟨43016280421764696298468595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28677520281176464198979063 43016280421764696298468595)
      ·
        refine ⟨64524420632647044447702893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43016280421764696298468595 64524420632647044447702893)
        ·
          refine ⟨24196657737242641667888585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64524420632647044447702893 24196657737242641667888585)
          ·
            refine ⟨18147493302931981250916439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24196657737242641667888585 18147493302931981250916439)
            ·
              refine ⟨27221239954397971876374659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18147493302931981250916439 27221239954397971876374659)
              ·
                refine ⟨40831859931596957814561989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27221239954397971876374659 40831859931596957814561989)
                ·
                  refine ⟨7655973737174429590230373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40831859931596957814561989 7655973737174429590230373)
                  ·
                    refine ⟨1435495075720205548168195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7655973737174429590230373 1435495075720205548168195)
                    ·
                      rfl

theorem cell23_8386850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_8386850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386850 prefixEnd_8386850 := by exact prefixLift 8386850
  have htrace : WordTrace (prefixWord ++ tailWord_8386850) baseStart_8386850 baseEnd_8386850 := by
    simpa [prefixWord, tailWord_8386850, baseEnd_8386850] using wordTrace_append hprefix tailTrace_8386850
  have hstable : (prefixWord ++ tailWord_8386850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386850).length < 2 ^ (prefixWord ++ tailWord_8386850).sum := by decide
  have hdescent : baseEnd_8386850 < baseStart_8386850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386908 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 3, 2, 2]
def baseStart_8386908 : Nat := 118140960795 + 8386908 * 2 ^ 59
def prefixEnd_8386908 : Nat := 4983230072969 + 3 ^ 40 * 8386908 * 2
def baseEnd_8386908 : Nat := 4306515009038577417579319

theorem tailTrace_8386908 : CollatzResearch.WordTrace tailWord_8386908 prefixEnd_8386908 4306515009038577417579319 := by
  unfold tailWord_8386908
  simp only [CollatzResearch.WordTrace]
  refine ⟨152947832549836080347360689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203930443399781440463147585 152947832549836080347360689)
  ·
    refine ⟨114710874412377060260520517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152947832549836080347360689 114710874412377060260520517)
    ·
      refine ⟨21508288952320698798847597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114710874412377060260520517 21508288952320698798847597)
      ·
        refine ⟨8065608357120262049567849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21508288952320698798847597 8065608357120262049567849)
        ·
          refine ⟨6049206267840196537175887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8065608357120262049567849 6049206267840196537175887)
          ·
            refine ⟨9073809401760294805763831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049206267840196537175887 9073809401760294805763831)
            ·
              refine ⟨13610714102640442208645747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9073809401760294805763831 13610714102640442208645747)
              ·
                refine ⟨20416071153960663312968621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13610714102640442208645747 20416071153960663312968621)
                ·
                  refine ⟨7656026682735248742363233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20416071153960663312968621 7656026682735248742363233)
                  ·
                    refine ⟨5742020012051436556772425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7656026682735248742363233 5742020012051436556772425)
                    ·
                      refine ⟨4306515009038577417579319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742020012051436556772425 4306515009038577417579319)
                      ·
                        rfl

theorem cell23_8386908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_8386908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386908 prefixEnd_8386908 := by exact prefixLift 8386908
  have htrace : WordTrace (prefixWord ++ tailWord_8386908) baseStart_8386908 baseEnd_8386908 := by
    simpa [prefixWord, tailWord_8386908, baseEnd_8386908] using wordTrace_append hprefix tailTrace_8386908
  have hstable : (prefixWord ++ tailWord_8386908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386908).length < 2 ^ (prefixWord ++ tailWord_8386908).sum := by decide
  have hdescent : baseEnd_8386908 < baseStart_8386908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386947 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 1, 4, 2]
def baseStart_8386947 : Nat := 118140960795 + 8386947 * 2 ^ 59
def prefixEnd_8386947 : Nat := 4983230072969 + 3 ^ 40 * 8386947 * 2
def baseEnd_8386947 : Nat := 4306535034784102764991639

theorem tailTrace_8386947 : CollatzResearch.WordTrace tailWord_8386947 prefixEnd_8386947 4306535034784102764991639 := by
  unfold tailWord_8386947
  simp only [CollatzResearch.WordTrace]
  refine ⟨305897087546530870355391095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203931391697687246903594063 305897087546530870355391095)
  ·
    refine ⟨458845631319796305533086643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305897087546530870355391095 458845631319796305533086643)
    ·
      refine ⟨688268446979694458299629965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458845631319796305533086643 688268446979694458299629965)
      ·
        refine ⟨258100667617385421862361237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 688268446979694458299629965 258100667617385421862361237)
        ·
          refine ⟨12098468794564941649798183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 258100667617385421862361237 12098468794564941649798183)
          ·
            refine ⟨18147703191847412474697275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098468794564941649798183 18147703191847412474697275)
            ·
              refine ⟨27221554787771118712045913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18147703191847412474697275 27221554787771118712045913)
              ·
                refine ⟨20416166090828339034034435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27221554787771118712045913 20416166090828339034034435)
                ·
                  refine ⟨30624249136242508551051653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20416166090828339034034435 30624249136242508551051653)
                  ·
                    refine ⟨5742046713045470353322185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30624249136242508551051653 5742046713045470353322185)
                    ·
                      refine ⟨4306535034784102764991639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742046713045470353322185 4306535034784102764991639)
                      ·
                        rfl

theorem cell23_8386947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4, 2].length) (baseStart_8386947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386947 prefixEnd_8386947 := by exact prefixLift 8386947
  have htrace : WordTrace (prefixWord ++ tailWord_8386947) baseStart_8386947 baseEnd_8386947 := by
    simpa [prefixWord, tailWord_8386947, baseEnd_8386947] using wordTrace_append hprefix tailTrace_8386947
  have hstable : (prefixWord ++ tailWord_8386947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386947).length < 2 ^ (prefixWord ++ tailWord_8386947).sum := by decide
  have hdescent : baseEnd_8386947 < baseStart_8386947 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8386977 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_8386977 : Nat := 118140960795 + 8386977 * 2 ^ 59
def prefixEnd_8386977 : Nat := 4983230072969 + 3 ^ 40 * 8386977 * 2
def baseEnd_8386977 : Nat := 4306550439203737647616501

theorem tailTrace_8386977 : CollatzResearch.WordTrace tailWord_8386977 prefixEnd_8386977 4306550439203737647616501 := by
  unfold tailWord_8386977
  simp only [CollatzResearch.WordTrace]
  refine ⟨305898181736422185478983185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203932121157614790319322123 305898181736422185478983185)
  ·
    refine ⟨229423636302316639109237389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305898181736422185478983185 229423636302316639109237389)
    ·
      refine ⟨86033863613368739665964021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229423636302316639109237389 86033863613368739665964021)
      ·
        refine ⟨8065674713753319343684127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86033863613368739665964021 8065674713753319343684127)
        ·
          refine ⟨12098512070629979015526191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065674713753319343684127 12098512070629979015526191)
          ·
            refine ⟨18147768105944968523289287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098512070629979015526191 18147768105944968523289287)
            ·
              refine ⟨27221652158917452784933931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18147768105944968523289287 27221652158917452784933931)
              ·
                refine ⟨40832478238376179177400897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27221652158917452784933931 40832478238376179177400897)
                ·
                  refine ⟨30624358678782134383050673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40832478238376179177400897 30624358678782134383050673)
                  ·
                    refine ⟨22968269009086600787288005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30624358678782134383050673 22968269009086600787288005)
                    ·
                      refine ⟨4306550439203737647616501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22968269009086600787288005 4306550439203737647616501)
                      ·
                        rfl

theorem cell23_8386977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_8386977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8386977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8386977 prefixEnd_8386977 := by exact prefixLift 8386977
  have htrace : WordTrace (prefixWord ++ tailWord_8386977) baseStart_8386977 baseEnd_8386977 := by
    simpa [prefixWord, tailWord_8386977, baseEnd_8386977] using wordTrace_append hprefix tailTrace_8386977
  have hstable : (prefixWord ++ tailWord_8386977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8386977).length < 2 ^ (prefixWord ++ tailWord_8386977).sum := by decide
  have hdescent : baseEnd_8386977 < baseStart_8386977 := by decide
  rcases family_descends (prefixWord ++ tailWord_8386977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387003 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4]
def baseStart_8387003 : Nat := 118140960795 + 8387003 * 2 ^ 59
def prefixEnd_8387003 : Nat := 4983230072969 + 3 ^ 40 * 8387003 * 2
def baseEnd_8387003 : Nat := 4306563789700754545891381

theorem tailTrace_8387003 : CollatzResearch.WordTrace tailWord_8387003 prefixEnd_8387003 4306563789700754545891381 := by
  unfold tailWord_8387003
  simp only [CollatzResearch.WordTrace]
  refine ⟨305899130034327991919429663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203932753356218661279619775 305899130034327991919429663)
  ·
    refine ⟨458848695051491987879144495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305899130034327991919429663 458848695051491987879144495)
    ·
      refine ⟨688273042577237981818716743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458848695051491987879144495 688273042577237981818716743)
      ·
        refine ⟨1032409563865856972728075115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688273042577237981818716743 1032409563865856972728075115)
        ·
          refine ⟨1548614345798785459092112673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032409563865856972728075115 1548614345798785459092112673)
          ·
            refine ⟨1161460759349089094319084505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1548614345798785459092112673 1161460759349089094319084505)
            ·
              refine ⟨871095569511816820739313379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1161460759349089094319084505 871095569511816820739313379)
              ·
                refine ⟨1306643354267725231108970069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871095569511816820739313379 1306643354267725231108970069)
                ·
                  refine ⟨15312226807824905052058243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1306643354267725231108970069 15312226807824905052058243)
                  ·
                    refine ⟨22968340211737357578087365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15312226807824905052058243 22968340211737357578087365)
                    ·
                      refine ⟨4306563789700754545891381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22968340211737357578087365 4306563789700754545891381)
                      ·
                        rfl

theorem cell23_8387003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 4].length) (baseStart_8387003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387003 prefixEnd_8387003 := by exact prefixLift 8387003
  have htrace : WordTrace (prefixWord ++ tailWord_8387003) baseStart_8387003 baseEnd_8387003 := by
    simpa [prefixWord, tailWord_8387003, baseEnd_8387003] using wordTrace_append hprefix tailTrace_8387003
  have hstable : (prefixWord ++ tailWord_8387003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387003).length < 2 ^ (prefixWord ++ tailWord_8387003).sum := by decide
  have hdescent : baseEnd_8387003 < baseStart_8387003 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387033 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_8387033 : Nat := 118140960795 + 8387033 * 2 ^ 59
def prefixEnd_8387033 : Nat := 4983230072969 + 3 ^ 40 * 8387033 * 2
def baseEnd_8387033 : Nat := 4306579194120389428516243

theorem tailTrace_8387033 : CollatzResearch.WordTrace tailWord_8387033 prefixEnd_8387033 4306579194120389428516243 := by
  unfold tailWord_8387033
  simp only [CollatzResearch.WordTrace]
  refine ⟨305900224224219307043021753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203933482816146204695347835 305900224224219307043021753)
  ·
    refine ⟨229425168168164480282266315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305900224224219307043021753 229425168168164480282266315)
    ·
      refine ⟨344137752252246720423399473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229425168168164480282266315 344137752252246720423399473)
      ·
        refine ⟨258103314189185040317549605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344137752252246720423399473 258103314189185040317549605)
        ·
          refine ⟨48394371410472195059540551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258103314189185040317549605 48394371410472195059540551)
          ·
            refine ⟨72591557115708292589310827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48394371410472195059540551 72591557115708292589310827)
            ·
              refine ⟨108887335673562438883966241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72591557115708292589310827 108887335673562438883966241)
              ·
                refine ⟨81665501755171829162974681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108887335673562438883966241 81665501755171829162974681)
                ·
                  refine ⟨61249126316378871872231011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81665501755171829162974681 61249126316378871872231011)
                  ·
                    refine ⟨91873689474568307808346517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61249126316378871872231011 91873689474568307808346517)
                    ·
                      refine ⟨4306579194120389428516243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 91873689474568307808346517 4306579194120389428516243)
                      ·
                        rfl

theorem cell23_8387033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_8387033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387033 prefixEnd_8387033 := by exact prefixLift 8387033
  have htrace : WordTrace (prefixWord ++ tailWord_8387033) baseStart_8387033 baseEnd_8387033 := by
    simpa [prefixWord, tailWord_8387033, baseEnd_8387033] using wordTrace_append hprefix tailTrace_8387033
  have hstable : (prefixWord ++ tailWord_8387033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387033).length < 2 ^ (prefixWord ++ tailWord_8387033).sum := by decide
  have hdescent : baseEnd_8387033 < baseStart_8387033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387037 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_8387037 : Nat := 118140960795 + 8387037 * 2 ^ 59
def prefixEnd_8387037 : Nat := 4983230072969 + 3 ^ 40 * 8387037 * 2
def baseEnd_8387037 : Nat := 4306581248043007412866225

theorem tailTrace_8387037 : CollatzResearch.WordTrace tailWord_8387037 prefixEnd_8387037 4306581248043007412866225 := by
  unfold tailWord_8387037
  simp only [CollatzResearch.WordTrace]
  refine ⟨305900370116204815726167365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203933580077469877150778243 305900370116204815726167365)
  ·
    refine ⟨57356319396788402948656381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305900370116204815726167365 57356319396788402948656381)
    ·
      refine ⟨21508619773795651105746143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57356319396788402948656381 21508619773795651105746143)
      ·
        refine ⟨32262929660693476658619215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21508619773795651105746143 32262929660693476658619215)
        ·
          refine ⟨48394394491040214987928823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32262929660693476658619215 48394394491040214987928823)
          ·
            refine ⟨72591591736560322481893235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48394394491040214987928823 72591591736560322481893235)
            ·
              refine ⟨108887387604840483722839853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72591591736560322481893235 108887387604840483722839853)
              ·
                refine ⟨40832770351815181396064945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108887387604840483722839853 40832770351815181396064945)
                ·
                  refine ⟨30624577763861386047048709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40832770351815181396064945 30624577763861386047048709)
                  ·
                    refine ⟨5742108330724009883821633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30624577763861386047048709 5742108330724009883821633)
                    ·
                      refine ⟨4306581248043007412866225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742108330724009883821633 4306581248043007412866225)
                      ·
                        rfl

theorem cell23_8387037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_8387037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387037 prefixEnd_8387037 := by exact prefixLift 8387037
  have htrace : WordTrace (prefixWord ++ tailWord_8387037) baseStart_8387037 baseEnd_8387037 := by
    simpa [prefixWord, tailWord_8387037, baseEnd_8387037] using wordTrace_append hprefix tailTrace_8387037
  have hstable : (prefixWord ++ tailWord_8387037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387037).length < 2 ^ (prefixWord ++ tailWord_8387037).sum := by decide
  have hdescent : baseEnd_8387037 < baseStart_8387037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387107 : List Nat := [1, 1, 1, 4, 4, 1, 3, 2, 1, 5]
def baseStart_8387107 : Nat := 118140960795 + 8387107 * 2 ^ 59
def prefixEnd_8387107 : Nat := 4983230072969 + 3 ^ 40 * 8387107 * 2
def baseEnd_8387107 : Nat := 1435539063896274046330301

theorem tailTrace_8387107 : CollatzResearch.WordTrace tailWord_8387107 prefixEnd_8387107 1435539063896274046330301 := by
  unfold tailWord_8387107
  simp only [CollatzResearch.WordTrace]
  refine ⟨305902923225951217681215575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203935282150634145120810383 305902923225951217681215575)
  ·
    refine ⟨458854384838926826521823363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305902923225951217681215575 458854384838926826521823363)
    ·
      refine ⟨688281577258390239782735045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458854384838926826521823363 688281577258390239782735045)
      ·
        refine ⟨129052795735948169959262821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 688281577258390239782735045 129052795735948169959262821)
        ·
          refine ⟨24197399200490281867361779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129052795735948169959262821 24197399200490281867361779)
          ·
            refine ⟨36296098800735422801042669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24197399200490281867361779 36296098800735422801042669)
            ·
              refine ⟨13611037050275783550391001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36296098800735422801042669 13611037050275783550391001)
              ·
                refine ⟨10208277787706837662793251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13611037050275783550391001 10208277787706837662793251)
                ·
                  refine ⟨15312416681560256494189877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208277787706837662793251 15312416681560256494189877)
                  ·
                    refine ⟨1435539063896274046330301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15312416681560256494189877 1435539063896274046330301)
                    ·
                      rfl

theorem cell23_8387107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 5].length) (baseStart_8387107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387107 prefixEnd_8387107 := by exact prefixLift 8387107
  have htrace : WordTrace (prefixWord ++ tailWord_8387107) baseStart_8387107 baseEnd_8387107 := by
    simpa [prefixWord, tailWord_8387107, baseEnd_8387107] using wordTrace_append hprefix tailTrace_8387107
  have hstable : (prefixWord ++ tailWord_8387107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387107).length < 2 ^ (prefixWord ++ tailWord_8387107).sum := by decide
  have hdescent : baseEnd_8387107 < baseStart_8387107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387114 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_8387114 : Nat := 118140960795 + 8387114 * 2 ^ 59
def prefixEnd_8387114 : Nat := 4983230072969 + 3 ^ 40 * 8387114 * 2
def baseEnd_8387114 : Nat := 4306620786053403611603371

theorem tailTrace_8387114 : CollatzResearch.WordTrace tailWord_8387114 prefixEnd_8387114 4306620786053403611603371 := by
  unfold tailWord_8387114
  simp only [CollatzResearch.WordTrace]
  refine ⟨76475794634231464469180099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203935452357950571917813597 76475794634231464469180099)
  ·
    refine ⟨114713691951347196703770149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76475794634231464469180099 114713691951347196703770149)
    ·
      refine ⟨21508817240877599381956903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114713691951347196703770149 21508817240877599381956903)
      ·
        refine ⟨32263225861316399072935355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21508817240877599381956903 32263225861316399072935355)
        ·
          refine ⟨48394838791974598609403033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263225861316399072935355 48394838791974598609403033)
          ·
            refine ⟨36296129093980948957052275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48394838791974598609403033 36296129093980948957052275)
            ·
              refine ⟨54444193640971423435578413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36296129093980948957052275 54444193640971423435578413)
              ·
                refine ⟨20416572615364283788341905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54444193640971423435578413 20416572615364283788341905)
                ·
                  refine ⟨15312429461523212841256429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20416572615364283788341905 15312429461523212841256429)
                  ·
                    refine ⟨5742161048071204815471161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15312429461523212841256429 5742161048071204815471161)
                    ·
                      refine ⟨4306620786053403611603371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742161048071204815471161 4306620786053403611603371)
                      ·
                        rfl

theorem cell23_8387114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_8387114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387114 prefixEnd_8387114 := by exact prefixLift 8387114
  have htrace : WordTrace (prefixWord ++ tailWord_8387114) baseStart_8387114 baseEnd_8387114 := by
    simpa [prefixWord, tailWord_8387114, baseEnd_8387114] using wordTrace_append hprefix tailTrace_8387114
  have hstable : (prefixWord ++ tailWord_8387114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387114).length < 2 ^ (prefixWord ++ tailWord_8387114).sum := by decide
  have hdescent : baseEnd_8387114 < baseStart_8387114 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387120 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 6, 4]
def baseStart_8387120 : Nat := 118140960795 + 8387120 * 2 ^ 59
def prefixEnd_8387120 : Nat := 4983230072969 + 3 ^ 40 * 8387120 * 2
def baseEnd_8387120 : Nat := 1435541288979110196042781

theorem tailTrace_8387120 : CollatzResearch.WordTrace tailWord_8387120 prefixEnd_8387120 1435541288979110196042781 := by
  unfold tailWord_8387120
  simp only [CollatzResearch.WordTrace]
  refine ⟨152951698687452060450719407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203935598249936080600959209 152951698687452060450719407)
  ·
    refine ⟨229427548031178090676079111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152951698687452060450719407 229427548031178090676079111)
    ·
      refine ⟨344141322046767136014118667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229427548031178090676079111 344141322046767136014118667)
      ·
        refine ⟨516211983070150704021178001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344141322046767136014118667 516211983070150704021178001)
        ·
          refine ⟨387158987302613028015883501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516211983070150704021178001 387158987302613028015883501)
          ·
            refine ⟨145184620238479885505956313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387158987302613028015883501 145184620238479885505956313)
            ·
              refine ⟨108888465178859914129467235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145184620238479885505956313 108888465178859914129467235)
              ·
                refine ⟨163332697768289871194200853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108888465178859914129467235 163332697768289871194200853)
                ·
                  refine ⟨7656220207888587712228165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 163332697768289871194200853 7656220207888587712228165)
                  ·
                    refine ⟨1435541288979110196042781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656220207888587712228165 1435541288979110196042781)
                    ·
                      rfl

theorem cell23_8387120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 6, 4].length) (baseStart_8387120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387120 prefixEnd_8387120 := by exact prefixLift 8387120
  have htrace : WordTrace (prefixWord ++ tailWord_8387120) baseStart_8387120 baseEnd_8387120 := by
    simpa [prefixWord, tailWord_8387120, baseEnd_8387120] using wordTrace_append hprefix tailTrace_8387120
  have hstable : (prefixWord ++ tailWord_8387120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387120).length < 2 ^ (prefixWord ++ tailWord_8387120).sum := by decide
  have hdescent : baseEnd_8387120 < baseStart_8387120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387150 : List Nat := [4, 1, 1, 1, 1, 2, 5, 8]
def baseStart_8387150 : Nat := 118140960795 + 8387150 * 2 ^ 59
def prefixEnd_8387150 : Nat := 4983230072969 + 3 ^ 40 * 8387150 * 2
def baseEnd_8387150 : Nat := 159505158198406128546415

theorem tailTrace_8387150 : CollatzResearch.WordTrace tailWord_8387150 prefixEnd_8387150 159505158198406128546415 := by
  unfold tailWord_8387150
  simp only [CollatzResearch.WordTrace]
  refine ⟨38238061445599429503128863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 203936327709863624016687269 38238061445599429503128863)
  ·
    refine ⟨57357092168399144254693295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38238061445599429503128863 57357092168399144254693295)
    ·
      refine ⟨86035638252598716382039943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57357092168399144254693295 86035638252598716382039943)
      ·
        refine ⟨129053457378898074573059915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86035638252598716382039943 129053457378898074573059915)
        ·
          refine ⟨193580186068347111859589873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129053457378898074573059915 193580186068347111859589873)
          ·
            refine ⟨145185139551260333894692405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193580186068347111859589873 145185139551260333894692405)
            ·
              refine ⟨13611106832930656302627413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145185139551260333894692405 13611106832930656302627413)
              ·
                refine ⟨159505158198406128546415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13611106832930656302627413 159505158198406128546415)
                ·
                  rfl

theorem cell23_8387150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_8387150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387150 prefixEnd_8387150 := by exact prefixLift 8387150
  have htrace : WordTrace (prefixWord ++ tailWord_8387150) baseStart_8387150 baseEnd_8387150 := by
    simpa [prefixWord, tailWord_8387150, baseEnd_8387150] using wordTrace_append hprefix tailTrace_8387150
  have hstable : (prefixWord ++ tailWord_8387150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387150).length < 2 ^ (prefixWord ++ tailWord_8387150).sum := by decide
  have hdescent : baseEnd_8387150 < baseStart_8387150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387177 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 3]
def baseStart_8387177 : Nat := 118140960795 + 8387177 * 2 ^ 59
def prefixEnd_8387177 : Nat := 4983230072969 + 3 ^ 40 * 8387177 * 2
def baseEnd_8387177 : Nat := 4306653135334636865115581

theorem tailTrace_8387177 : CollatzResearch.WordTrace tailWord_8387177 prefixEnd_8387177 4306653135334636865115581 := by
  unfold tailWord_8387177
  simp only [CollatzResearch.WordTrace]
  refine ⟨305905476335697619636263785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203936984223798413090842523 305905476335697619636263785)
  ·
    refine ⟨229429107251773214727197839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305905476335697619636263785 229429107251773214727197839)
    ·
      refine ⟨344143660877659822090796759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229429107251773214727197839 344143660877659822090796759)
      ·
        refine ⟨516215491316489733136195139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344143660877659822090796759 516215491316489733136195139)
        ·
          refine ⟨774323236974734599704292709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516215491316489733136195139 774323236974734599704292709)
          ·
            refine ⟨145185606932762737444554883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774323236974734599704292709 145185606932762737444554883)
            ·
              refine ⟨217778410399144106166832325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145185606932762737444554883 217778410399144106166832325)
              ·
                refine ⟨40833451949839519906281061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217778410399144106166832325 40833451949839519906281061)
                ·
                  refine ⟨7656272240594909982427699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40833451949839519906281061 7656272240594909982427699)
                  ·
                    refine ⟨11484408360892364973641549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7656272240594909982427699 11484408360892364973641549)
                    ·
                      refine ⟨4306653135334636865115581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11484408360892364973641549 4306653135334636865115581)
                      ·
                        rfl

theorem cell23_8387177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_8387177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387177 prefixEnd_8387177 := by exact prefixLift 8387177
  have htrace : WordTrace (prefixWord ++ tailWord_8387177) baseStart_8387177 baseEnd_8387177 := by
    simpa [prefixWord, tailWord_8387177, baseEnd_8387177] using wordTrace_append hprefix tailTrace_8387177
  have hstable : (prefixWord ++ tailWord_8387177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387177).length < 2 ^ (prefixWord ++ tailWord_8387177).sum := by decide
  have hdescent : baseEnd_8387177 < baseStart_8387177 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387178 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_8387178 : Nat := 118140960795 + 8387178 * 2 ^ 59
def prefixEnd_8387178 : Nat := 4983230072969 + 3 ^ 40 * 8387178 * 2
def baseEnd_8387178 : Nat := 4306653648815291361203077

theorem tailTrace_8387178 : CollatzResearch.WordTrace tailWord_8387178 prefixEnd_8387178 4306653648815291361203077 := by
  unfold tailWord_8387178
  simp only [CollatzResearch.WordTrace]
  refine ⟨76476378202173499201762547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203937008539129331204700125 76476378202173499201762547)
  ·
    refine ⟨114714567303260248802643821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76476378202173499201762547 114714567303260248802643821)
    ·
      refine ⟨43017962738722593300991433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114714567303260248802643821 43017962738722593300991433)
      ·
        refine ⟨32263472054041944975743575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43017962738722593300991433 32263472054041944975743575)
        ·
          refine ⟨48395208081062917463615363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263472054041944975743575 48395208081062917463615363)
          ·
            refine ⟨72592812121594376195423045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48395208081062917463615363 72592812121594376195423045)
            ·
              refine ⟨13611152272798945536641821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72592812121594376195423045 13611152272798945536641821)
              ·
                refine ⟨5104182102299604576240683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13611152272798945536641821 5104182102299604576240683)
                ·
                  refine ⟨7656273153449406864361025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104182102299604576240683 7656273153449406864361025)
                  ·
                    refine ⟨5742204865087055148270769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7656273153449406864361025 5742204865087055148270769)
                    ·
                      refine ⟨4306653648815291361203077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742204865087055148270769 4306653648815291361203077)
                      ·
                        rfl

theorem cell23_8387178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_8387178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387178 prefixEnd_8387178 := by exact prefixLift 8387178
  have htrace : WordTrace (prefixWord ++ tailWord_8387178) baseStart_8387178 baseEnd_8387178 := by
    simpa [prefixWord, tailWord_8387178, baseEnd_8387178] using wordTrace_append hprefix tailTrace_8387178
  have hstable : (prefixWord ++ tailWord_8387178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387178).length < 2 ^ (prefixWord ++ tailWord_8387178).sum := by decide
  have hdescent : baseEnd_8387178 < baseStart_8387178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387181 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_8387181 : Nat := 118140960795 + 8387181 * 2 ^ 59
def prefixEnd_8387181 : Nat := 4983230072969 + 3 ^ 40 * 8387181 * 2
def baseEnd_8387181 : Nat := 4306655189257254849465563

theorem tailTrace_8387181 : CollatzResearch.WordTrace tailWord_8387181 prefixEnd_8387181 4306655189257254849465563 := by
  unfold tailWord_8387181
  simp only [CollatzResearch.WordTrace]
  refine ⟨305905622227683128319409397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203937081485122085546272931 305905622227683128319409397)
  ·
    refine ⟨28678652083845293279944631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 305905622227683128319409397 28678652083845293279944631)
    ·
      refine ⟨43017978125767939919916947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28678652083845293279944631 43017978125767939919916947)
      ·
        refine ⟨64526967188651909879875421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43017978125767939919916947 64526967188651909879875421)
        ·
          refine ⟨24197612695744466204953283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64526967188651909879875421 24197612695744466204953283)
          ·
            refine ⟨36296419043616699307429925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24197612695744466204953283 36296419043616699307429925)
            ·
              refine ⟨6805578570678131120143111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36296419043616699307429925 6805578570678131120143111)
              ·
                refine ⟨10208367856017196680214667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805578570678131120143111 10208367856017196680214667)
                ·
                  refine ⟨15312551784025795020322001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208367856017196680214667 15312551784025795020322001)
                  ·
                    refine ⟨11484413838019346265241501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15312551784025795020322001 11484413838019346265241501)
                    ·
                      refine ⟨4306655189257254849465563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11484413838019346265241501 4306655189257254849465563)
                      ·
                        rfl

theorem cell23_8387181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_8387181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387181 prefixEnd_8387181 := by exact prefixLift 8387181
  have htrace : WordTrace (prefixWord ++ tailWord_8387181) baseStart_8387181 baseEnd_8387181 := by
    simpa [prefixWord, tailWord_8387181, baseEnd_8387181] using wordTrace_append hprefix tailTrace_8387181
  have hstable : (prefixWord ++ tailWord_8387181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387181).length < 2 ^ (prefixWord ++ tailWord_8387181).sum := by decide
  have hdescent : baseEnd_8387181 < baseStart_8387181 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 5, 3, 2]
def baseStart_8387187 : Nat := 118140960795 + 8387187 * 2 ^ 59
def prefixEnd_8387187 : Nat := 4983230072969 + 3 ^ 40 * 8387187 * 2
def baseEnd_8387187 : Nat := 4306658270141181825990535

theorem tailTrace_8387187 : CollatzResearch.WordTrace tailWord_8387187 prefixEnd_8387187 4306658270141181825990535 := by
  unfold tailWord_8387187
  simp only [CollatzResearch.WordTrace]
  refine ⟨305905841065661391344127815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203937227377107594229418543 305905841065661391344127815)
  ·
    refine ⟨458858761598492087016191723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305905841065661391344127815 458858761598492087016191723)
    ·
      refine ⟨688288142397738130524287585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458858761598492087016191723 688288142397738130524287585)
      ·
        refine ⟨516216106798303597893215689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 688288142397738130524287585 516216106798303597893215689)
        ·
          refine ⟨387162080098727698419911767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516216106798303597893215689 387162080098727698419911767)
          ·
            refine ⟨580743120148091547629867651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387162080098727698419911767 580743120148091547629867651)
            ·
              refine ⟨871114680222137321444801477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580743120148091547629867651 871114680222137321444801477)
              ·
                refine ⟨163334002541650747770900277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 871114680222137321444801477 163334002541650747770900277)
                ·
                  refine ⟨15312562738279757603521901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 163334002541650747770900277 15312562738279757603521901)
                  ·
                    refine ⟨5742211026854909101320713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15312562738279757603521901 5742211026854909101320713)
                    ·
                      refine ⟨4306658270141181825990535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742211026854909101320713 4306658270141181825990535)
                      ·
                        rfl

theorem cell23_8387187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3, 2].length) (baseStart_8387187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387187 prefixEnd_8387187 := by exact prefixLift 8387187
  have htrace : WordTrace (prefixWord ++ tailWord_8387187) baseStart_8387187 baseEnd_8387187 := by
    simpa [prefixWord, tailWord_8387187, baseEnd_8387187] using wordTrace_append hprefix tailTrace_8387187
  have hstable : (prefixWord ++ tailWord_8387187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387187).length < 2 ^ (prefixWord ++ tailWord_8387187).sum := by decide
  have hdescent : baseEnd_8387187 < baseStart_8387187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9]
def baseStart_8387250 : Nat := 118140960795 + 8387250 * 2 ^ 59
def prefixEnd_8387250 : Nat := 4983230072969 + 3 ^ 40 * 8387250 * 2
def baseEnd_8387250 : Nat := 4306690619422415079502745

theorem tailTrace_8387250 : CollatzResearch.WordTrace tailWord_8387250 prefixEnd_8387250 4306690619422415079502745 := by
  unfold tailWord_8387250
  simp only [CollatzResearch.WordTrace]
  refine ⟨76477034716108288275917801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203938759242955435402447469 76477034716108288275917801)
  ·
    refine ⟨57357776037081216206938351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76477034716108288275917801 57357776037081216206938351)
    ·
      refine ⟨86036664055621824310407527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57357776037081216206938351 86036664055621824310407527)
      ·
        refine ⟨129054996083432736465611291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86036664055621824310407527 129054996083432736465611291)
        ·
          refine ⟨193582494125149104698416937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129054996083432736465611291 193582494125149104698416937)
          ·
            refine ⟨145186870593861828523812703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193582494125149104698416937 145186870593861828523812703)
            ·
              refine ⟨217780305890792742785719055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145186870593861828523812703 217780305890792742785719055)
              ·
                refine ⟨326670458836189114178578583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217780305890792742785719055 326670458836189114178578583)
                ·
                  refine ⟨490005688254283671267867875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 326670458836189114178578583 490005688254283671267867875)
                  ·
                    refine ⟨735008532381425506901801813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 490005688254283671267867875 735008532381425506901801813)
                    ·
                      refine ⟨4306690619422415079502745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 735008532381425506901801813 4306690619422415079502745)
                      ·
                        rfl

theorem cell23_8387250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_8387250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387250 prefixEnd_8387250 := by exact prefixLift 8387250
  have htrace : WordTrace (prefixWord ++ tailWord_8387250) baseStart_8387250 baseEnd_8387250 := by
    simpa [prefixWord, tailWord_8387250, baseEnd_8387250] using wordTrace_append hprefix tailTrace_8387250
  have hstable : (prefixWord ++ tailWord_8387250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387250).length < 2 ^ (prefixWord ++ tailWord_8387250).sum := by decide
  have hdescent : baseEnd_8387250 < baseStart_8387250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387268 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_8387268 : Nat := 118140960795 + 8387268 * 2 ^ 59
def prefixEnd_8387268 : Nat := 4983230072969 + 3 ^ 40 * 8387268 * 2
def baseEnd_8387268 : Nat := 4306699862074196009077663

theorem tailTrace_8387268 : CollatzResearch.WordTrace tailWord_8387268 prefixEnd_8387268 4306699862074196009077663 := by
  unfold tailWord_8387268
  simp only [CollatzResearch.WordTrace]
  refine ⟨152954397689183971088913229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203939196918911961451884305 152954397689183971088913229)
  ·
    refine ⟨57357899133443989158342461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152954397689183971088913229 57357899133443989158342461)
    ·
      refine ⟨21509212175041495934378423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57357899133443989158342461 21509212175041495934378423)
      ·
        refine ⟨32263818262562243901567635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21509212175041495934378423 32263818262562243901567635)
        ·
          refine ⟨48395727393843365852351453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263818262562243901567635 48395727393843365852351453)
          ·
            refine ⟨18148397772691262194631795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48395727393843365852351453 18148397772691262194631795)
            ·
              refine ⟨27222596659036893291947693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148397772691262194631795 27222596659036893291947693)
              ·
                refine ⟨10208473747138834984480385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27222596659036893291947693 10208473747138834984480385)
                ·
                  refine ⟨7656355310354126238360289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10208473747138834984480385 7656355310354126238360289)
                  ·
                    refine ⟨5742266482765594678770217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7656355310354126238360289 5742266482765594678770217)
                    ·
                      refine ⟨4306699862074196009077663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742266482765594678770217 4306699862074196009077663)
                      ·
                        rfl

theorem cell23_8387268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_8387268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387268 prefixEnd_8387268 := by exact prefixLift 8387268
  have htrace : WordTrace (prefixWord ++ tailWord_8387268) baseStart_8387268 baseEnd_8387268 := by
    simpa [prefixWord, tailWord_8387268, baseEnd_8387268] using wordTrace_append hprefix tailTrace_8387268
  have hstable : (prefixWord ++ tailWord_8387268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387268).length < 2 ^ (prefixWord ++ tailWord_8387268).sum := by decide
  have hdescent : baseEnd_8387268 < baseStart_8387268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387287 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 2, 5]
def baseStart_8387287 : Nat := 118140960795 + 8387287 * 2 ^ 59
def prefixEnd_8387287 : Nat := 4983230072969 + 3 ^ 40 * 8387287 * 2
def baseEnd_8387287 : Nat := 1435569872735543811580025

theorem tailTrace_8387287 : CollatzResearch.WordTrace tailWord_8387287 prefixEnd_8387287 1435569872735543811580025 := by
  unfold tailWord_8387287
  simp only [CollatzResearch.WordTrace]
  refine ⟨305909488365299108422768115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203939658910199405615178743 305909488365299108422768115)
  ·
    refine ⟨458864232547948662634152173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305909488365299108422768115 458864232547948662634152173)
    ·
      refine ⟨172074087205480748487807065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458864232547948662634152173 172074087205480748487807065)
      ·
        refine ⟨129055565404110561365855299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172074087205480748487807065 129055565404110561365855299)
        ·
          refine ⟨193583348106165842048782949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129055565404110561365855299 193583348106165842048782949)
          ·
            refine ⟨36296877769906095384146803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193583348106165842048782949 36296877769906095384146803)
            ·
              refine ⟨54445316654859143076220205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36296877769906095384146803 54445316654859143076220205)
              ·
                refine ⟨20416993745572178653582577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54445316654859143076220205 20416993745572178653582577)
                ·
                  refine ⟨15312745309179133990186933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20416993745572178653582577 15312745309179133990186933)
                  ·
                    refine ⟨1435569872735543811580025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15312745309179133990186933 1435569872735543811580025)
                    ·
                      rfl

theorem cell23_8387287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_8387287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387287 prefixEnd_8387287 := by exact prefixLift 8387287
  have htrace : WordTrace (prefixWord ++ tailWord_8387287) baseStart_8387287 baseEnd_8387287 := by
    simpa [prefixWord, tailWord_8387287, baseEnd_8387287] using wordTrace_append hprefix tailTrace_8387287
  have hstable : (prefixWord ++ tailWord_8387287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387287).length < 2 ^ (prefixWord ++ tailWord_8387287).sum := by decide
  have hdescent : baseEnd_8387287 < baseStart_8387287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387297 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_8387297 : Nat := 118140960795 + 8387297 * 2 ^ 59
def prefixEnd_8387297 : Nat := 4983230072969 + 3 ^ 40 * 8387297 * 2
def baseEnd_8387297 : Nat := 4306714753013176395615029

theorem tailTrace_8387297 : CollatzResearch.WordTrace tailWord_8387297 prefixEnd_8387297 4306714753013176395615029 := by
  unfold tailWord_8387297
  simp only [CollatzResearch.WordTrace]
  refine ⟨305909853095262880130632145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203939902063508586753754763 305909853095262880130632145)
  ·
    refine ⟨229432389821447160097974109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305909853095262880130632145 229432389821447160097974109)
    ·
      refine ⟨86037146183042685036740291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229432389821447160097974109 86037146183042685036740291)
      ·
        refine ⟨129055719274564027555110437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86037146183042685036740291 129055719274564027555110437)
        ·
          refine ⟨24197947363980755166583207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129055719274564027555110437 24197947363980755166583207)
          ·
            refine ⟨36296921045971132749874811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24197947363980755166583207 36296921045971132749874811)
            ·
              refine ⟨54445381568956699124812217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36296921045971132749874811 54445381568956699124812217)
              ·
                refine ⟨40834036176717524343609163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54445381568956699124812217 40834036176717524343609163)
                ·
                  refine ⟨61251054265076286515413745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40834036176717524343609163 61251054265076286515413745)
                  ·
                    refine ⟨45938290698807214886560309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61251054265076286515413745 45938290698807214886560309)
                    ·
                      refine ⟨4306714753013176395615029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45938290698807214886560309 4306714753013176395615029)
                      ·
                        rfl

theorem cell23_8387297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_8387297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387297 prefixEnd_8387297 := by exact prefixLift 8387297
  have htrace : WordTrace (prefixWord ++ tailWord_8387297) baseStart_8387297 baseEnd_8387297 := by
    simpa [prefixWord, tailWord_8387297, baseEnd_8387297] using wordTrace_append hprefix tailTrace_8387297
  have hstable : (prefixWord ++ tailWord_8387297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387297).length < 2 ^ (prefixWord ++ tailWord_8387297).sum := by decide
  have hdescent : baseEnd_8387297 < baseStart_8387297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387324 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_8387324 : Nat := 118140960795 + 8387324 * 2 ^ 59
def prefixEnd_8387324 : Nat := 4983230072969 + 3 ^ 40 * 8387324 * 2
def baseEnd_8387324 : Nat := 4306728616990847789977405

theorem tailTrace_8387324 : CollatzResearch.WordTrace tailWord_8387324 prefixEnd_8387324 4306728616990847789977405 := by
  unfold tailWord_8387324
  simp only [CollatzResearch.WordTrace]
  refine ⟨152955418933082531870932513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203940558577443375827910017 152955418933082531870932513)
  ·
    refine ⟨114716564199811898903199385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152955418933082531870932513 114716564199811898903199385)
    ·
      refine ⟨86037423149858924177399539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114716564199811898903199385 86037423149858924177399539)
      ·
        refine ⟨129056134724788386266099309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86037423149858924177399539 129056134724788386266099309)
        ·
          refine ⟨48396050521795644849787241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129056134724788386266099309 48396050521795644849787241)
          ·
            refine ⟨36297037891346733637340431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48396050521795644849787241 36297037891346733637340431)
            ·
              refine ⟨54445556837020100456010647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36297037891346733637340431 54445556837020100456010647)
              ·
                refine ⟨81668335255530150684015971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54445556837020100456010647 81668335255530150684015971)
                ·
                  refine ⟨122502502883295226026023957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81668335255530150684015971 122502502883295226026023957)
                  ·
                    refine ⟨5742304822654463719969873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122502502883295226026023957 5742304822654463719969873)
                    ·
                      refine ⟨4306728616990847789977405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742304822654463719969873 4306728616990847789977405)
                      ·
                        rfl

theorem cell23_8387324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_8387324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387324 prefixEnd_8387324 := by exact prefixLift 8387324
  have htrace : WordTrace (prefixWord ++ tailWord_8387324) baseStart_8387324 baseEnd_8387324 := by
    simpa [prefixWord, tailWord_8387324, baseEnd_8387324] using wordTrace_append hprefix tailTrace_8387324
  have hstable : (prefixWord ++ tailWord_8387324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387324).length < 2 ^ (prefixWord ++ tailWord_8387324).sum := by decide
  have hdescent : baseEnd_8387324 < baseStart_8387324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387327 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_8387327 : Nat := 118140960795 + 8387327 * 2 ^ 59
def prefixEnd_8387327 : Nat := 4983230072969 + 3 ^ 40 * 8387327 * 2
def baseEnd_8387327 : Nat := 4306730157432811278239891

theorem tailTrace_8387327 : CollatzResearch.WordTrace tailWord_8387327 prefixEnd_8387327 4306730157432811278239891 := by
  unfold tailWord_8387327
  simp only [CollatzResearch.WordTrace]
  refine ⟨305910947285154195254224235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203940631523436130169482823 305910947285154195254224235)
  ·
    refine ⟨458866420927731292881336353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305910947285154195254224235 458866420927731292881336353)
    ·
      refine ⟨344149815695798469661002265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458866420927731292881336353 344149815695798469661002265)
      ·
        refine ⟨258112361771848852245751699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344149815695798469661002265 258112361771848852245751699)
        ·
          refine ⟨387168542657773278368627549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258112361771848852245751699 387168542657773278368627549)
          ·
            refine ⟨145188203496664979388235331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 387168542657773278368627549 145188203496664979388235331)
            ·
              refine ⟨217782305244997469082352997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145188203496664979388235331 217782305244997469082352997)
              ·
                refine ⟨40834182233437025452941187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217782305244997469082352997 40834182233437025452941187)
                ·
                  refine ⟨61251273350155538179411781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40834182233437025452941187 61251273350155538179411781)
                  ·
                    refine ⟨11484613753154163408639709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61251273350155538179411781 11484613753154163408639709)
                    ·
                      refine ⟨4306730157432811278239891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11484613753154163408639709 4306730157432811278239891)
                      ·
                        rfl

theorem cell23_8387327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_8387327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387327 prefixEnd_8387327 := by exact prefixLift 8387327
  have htrace : WordTrace (prefixWord ++ tailWord_8387327) baseStart_8387327 baseEnd_8387327 := by
    simpa [prefixWord, tailWord_8387327, baseEnd_8387327] using wordTrace_append hprefix tailTrace_8387327
  have hstable : (prefixWord ++ tailWord_8387327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387327).length < 2 ^ (prefixWord ++ tailWord_8387327).sum := by decide
  have hdescent : baseEnd_8387327 < baseStart_8387327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387364 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 8]
def baseStart_8387364 : Nat := 118140960795 + 8387364 * 2 ^ 59
def prefixEnd_8387364 : Nat := 4983230072969 + 3 ^ 40 * 8387364 * 2
def baseEnd_8387364 : Nat := 478527684024114181497469

theorem tailTrace_8387364 : CollatzResearch.WordTrace tailWord_8387364 prefixEnd_8387364 478527684024114181497469 := by
  unfold tailWord_8387364
  simp only [CollatzResearch.WordTrace]
  refine ⟨152956148393010075286660573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203941531190680100382214097 152956148393010075286660573)
  ·
    refine ⟨57358555647378778232497715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152956148393010075286660573 57358555647378778232497715)
    ·
      refine ⟨86037833471068167348746573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57358555647378778232497715 86037833471068167348746573)
      ·
        refine ⟨32264187551650562755779965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86037833471068167348746573 32264187551650562755779965)
        ·
          refine ⟨12099070331868961033417487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32264187551650562755779965 12099070331868961033417487)
          ·
            refine ⟨18148605497803441550126231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099070331868961033417487 18148605497803441550126231)
            ·
              refine ⟨27222908246705162325189347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148605497803441550126231 27222908246705162325189347)
              ·
                refine ⟨40834362370057743487784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27222908246705162325189347 40834362370057743487784021)
                ·
                  refine ⟨478527684024114181497469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40834362370057743487784021 478527684024114181497469)
                  ·
                    rfl

theorem cell23_8387364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_8387364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387364 prefixEnd_8387364 := by exact prefixLift 8387364
  have htrace : WordTrace (prefixWord ++ tailWord_8387364) baseStart_8387364 baseEnd_8387364 := by
    simpa [prefixWord, tailWord_8387364, baseEnd_8387364] using wordTrace_append hprefix tailTrace_8387364
  have hstable : (prefixWord ++ tailWord_8387364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387364).length < 2 ^ (prefixWord ++ tailWord_8387364).sum := by decide
  have hdescent : baseEnd_8387364 < baseStart_8387364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387381 : List Nat := [1, 3, 3, 1, 3, 2, 3, 1, 6]
def baseStart_8387381 : Nat := 118140960795 + 8387381 * 2 ^ 59
def prefixEnd_8387381 : Nat := 4983230072969 + 3 ^ 40 * 8387381 * 2
def baseEnd_8387381 : Nat := 478528653932017118551627

theorem tailTrace_8387381 : CollatzResearch.WordTrace tailWord_8387381 prefixEnd_8387381 478528653932017118551627 := by
  unfold tailWord_8387381
  simp only [CollatzResearch.WordTrace]
  refine ⟨305912916826958562476689997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203941944551305708317793331 305912916826958562476689997)
  ·
    refine ⟨114717343810109460928758749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305912916826958562476689997 114717343810109460928758749)
    ·
      refine ⟨43019003928791047848284531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114717343810109460928758749 43019003928791047848284531)
      ·
        refine ⟨64528505893186571772426797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43019003928791047848284531 64528505893186571772426797)
        ·
          refine ⟨24198189709944964414660049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64528505893186571772426797 24198189709944964414660049)
          ·
            refine ⟨18148642282458723310995037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24198189709944964414660049 18148642282458723310995037)
            ·
              refine ⟨6805740855922021241623139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18148642282458723310995037 6805740855922021241623139)
              ·
                refine ⟨10208611283883031862434709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805740855922021241623139 10208611283883031862434709)
                ·
                  refine ⟨478528653932017118551627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10208611283883031862434709 478528653932017118551627)
                  ·
                    rfl

theorem cell23_8387381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_8387381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387381 prefixEnd_8387381 := by exact prefixLift 8387381
  have htrace : WordTrace (prefixWord ++ tailWord_8387381) baseStart_8387381 baseEnd_8387381 := by
    simpa [prefixWord, tailWord_8387381, baseEnd_8387381] using wordTrace_append hprefix tailTrace_8387381
  have hstable : (prefixWord ++ tailWord_8387381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387381).length < 2 ^ (prefixWord ++ tailWord_8387381).sum := by decide
  have hdescent : baseEnd_8387381 < baseStart_8387381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387384 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2]
def baseStart_8387384 : Nat := 118140960795 + 8387384 * 2 ^ 59
def prefixEnd_8387384 : Nat := 4983230072969 + 3 ^ 40 * 8387384 * 2
def baseEnd_8387384 : Nat := 4306759425830117555227129

theorem tailTrace_8387384 : CollatzResearch.WordTrace tailWord_8387384 prefixEnd_8387384 4306759425830117555227129 := by
  unfold tailWord_8387384
  simp only [CollatzResearch.WordTrace]
  refine ⟨152956513122973846994524603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203942017497298462659366137 152956513122973846994524603)
  ·
    refine ⟨229434769684460770491786905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152956513122973846994524603 229434769684460770491786905)
    ·
      refine ⟨172076077263345577868840179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229434769684460770491786905 172076077263345577868840179)
      ·
        refine ⟨258114115895018366803260269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172076077263345577868840179 258114115895018366803260269)
        ·
          refine ⟨96792793460631887551222601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258114115895018366803260269 96792793460631887551222601)
          ·
            refine ⟨72594595095473915663416951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96792793460631887551222601 72594595095473915663416951)
            ·
              refine ⟨108891892643210873495125427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72594595095473915663416951 108891892643210873495125427)
              ·
                refine ⟨163337838964816310242688141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108891892643210873495125427 163337838964816310242688141)
                ·
                  refine ⟨61251689611806116341008053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163337838964816310242688141 61251689611806116341008053)
                  ·
                    refine ⟨5742345901106823406969505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61251689611806116341008053 5742345901106823406969505)
                    ·
                      refine ⟨4306759425830117555227129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742345901106823406969505 4306759425830117555227129)
                      ·
                        rfl

theorem cell23_8387384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_8387384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387384 prefixEnd_8387384 := by exact prefixLift 8387384
  have htrace : WordTrace (prefixWord ++ tailWord_8387384) baseStart_8387384 baseEnd_8387384 := by
    simpa [prefixWord, tailWord_8387384, baseEnd_8387384] using wordTrace_append hprefix tailTrace_8387384
  have hstable : (prefixWord ++ tailWord_8387384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387384).length < 2 ^ (prefixWord ++ tailWord_8387384).sum := by decide
  have hdescent : baseEnd_8387384 < baseStart_8387384 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387391 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 3]
def baseStart_8387391 : Nat := 118140960795 + 8387391 * 2 ^ 59
def prefixEnd_8387391 : Nat := 4983230072969 + 3 ^ 40 * 8387391 * 2
def baseEnd_8387391 : Nat := 4306763020194699027839597

theorem tailTrace_8387391 : CollatzResearch.WordTrace tailWord_8387391 prefixEnd_8387391 4306763020194699027839597 := by
  unfold tailWord_8387391
  simp only [CollatzResearch.WordTrace]
  refine ⟨305913281556922334184554027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203942187704614889456369351 305913281556922334184554027)
  ·
    refine ⟨458869922335383501276831041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305913281556922334184554027 458869922335383501276831041)
    ·
      refine ⟨344152441751537625957623281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458869922335383501276831041 344152441751537625957623281)
      ·
        refine ⟨258114331313653219468217461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344152441751537625957623281 258114331313653219468217461)
        ·
          refine ⟨24198218560654989325145387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258114331313653219468217461 24198218560654989325145387)
          ·
            refine ⟨36297327840982483987718081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24198218560654989325145387 36297327840982483987718081)
            ·
              refine ⟨27222995880736862990788561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36297327840982483987718081 27222995880736862990788561)
              ·
                refine ⟨20417246910552647243091421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27222995880736862990788561 20417246910552647243091421)
                ·
                  refine ⟨7656467591457242716159283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20417246910552647243091421 7656467591457242716159283)
                  ·
                    refine ⟨11484701387185864074238925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7656467591457242716159283 11484701387185864074238925)
                    ·
                      refine ⟨4306763020194699027839597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11484701387185864074238925 4306763020194699027839597)
                      ·
                        rfl

theorem cell23_8387391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_8387391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387391 prefixEnd_8387391 := by exact prefixLift 8387391
  have htrace : WordTrace (prefixWord ++ tailWord_8387391) baseStart_8387391 baseEnd_8387391 := by
    simpa [prefixWord, tailWord_8387391, baseEnd_8387391] using wordTrace_append hprefix tailTrace_8387391
  have hstable : (prefixWord ++ tailWord_8387391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387391).length < 2 ^ (prefixWord ++ tailWord_8387391).sum := by decide
  have hdescent : baseEnd_8387391 < baseStart_8387391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387408 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 1, 1, 3]
def baseStart_8387408 : Nat := 118140960795 + 8387408 * 2 ^ 59
def prefixEnd_8387408 : Nat := 4983230072969 + 3 ^ 40 * 8387408 * 2
def baseEnd_8387408 : Nat := 4306771749365825461327019

theorem tailTrace_8387408 : CollatzResearch.WordTrace tailWord_8387408 prefixEnd_8387408 4306771749365825461327019 := by
  unfold tailWord_8387408
  simp only [CollatzResearch.WordTrace]
  refine ⟨152956950798930373043961439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203942601065240497391948585 152956950798930373043961439)
  ·
    refine ⟨229435426198395559565942159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152956950798930373043961439 229435426198395559565942159)
    ·
      refine ⟨344153139297593339348913239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229435426198395559565942159 344153139297593339348913239)
      ·
        refine ⟨516229708946390009023369859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344153139297593339348913239 516229708946390009023369859)
        ·
          refine ⟨774344563419585013535054789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516229708946390009023369859 774344563419585013535054789)
          ·
            refine ⟨145189605641172190037822773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774344563419585013535054789 145189605641172190037822773)
            ·
              refine ⟨13611525528859892816045885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145189605641172190037822773 13611525528859892816045885)
              ·
                refine ⟨5104322073322459806017207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13611525528859892816045885 5104322073322459806017207)
                ·
                  refine ⟨7656483109983689709025811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104322073322459806017207 7656483109983689709025811)
                  ·
                    refine ⟨11484724664975534563538717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7656483109983689709025811 11484724664975534563538717)
                    ·
                      refine ⟨4306771749365825461327019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11484724664975534563538717 4306771749365825461327019)
                      ·
                        rfl

theorem cell23_8387408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 1, 3].length) (baseStart_8387408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387408 prefixEnd_8387408 := by exact prefixLift 8387408
  have htrace : WordTrace (prefixWord ++ tailWord_8387408) baseStart_8387408 baseEnd_8387408 := by
    simpa [prefixWord, tailWord_8387408, baseEnd_8387408] using wordTrace_append hprefix tailTrace_8387408
  have hstable : (prefixWord ++ tailWord_8387408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387408).length < 2 ^ (prefixWord ++ tailWord_8387408).sum := by decide
  have hdescent : baseEnd_8387408 < baseStart_8387408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387424 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_8387424 : Nat := 118140960795 + 8387424 * 2 ^ 59
def prefixEnd_8387424 : Nat := 4983230072969 + 3 ^ 40 * 8387424 * 2
def baseEnd_8387424 : Nat := 1435593321685432466242315

theorem tailTrace_8387424 : CollatzResearch.WordTrace tailWord_8387424 prefixEnd_8387424 1435593321685432466242315 := by
  unfold tailWord_8387424
  simp only [CollatzResearch.WordTrace]
  refine ⟨152957242582901390410252663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203942990110535187213670217 152957242582901390410252663)
  ·
    refine ⟨229435863874352085615378995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152957242582901390410252663 229435863874352085615378995)
    ·
      refine ⟨344153795811528128423068493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229435863874352085615378995 344153795811528128423068493)
      ·
        refine ⟨129057673429323048158650685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344153795811528128423068493 129057673429323048158650685)
        ·
          refine ⟨48396627535996143059494007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129057673429323048158650685 48396627535996143059494007)
          ·
            refine ⟨72594941303994214589241011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48396627535996143059494007 72594941303994214589241011)
            ·
              refine ⟨108892411955991321883861517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72594941303994214589241011 108892411955991321883861517)
              ·
                refine ⟨40834654483496745706448069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108892411955991321883861517 40834654483496745706448069)
                ·
                  refine ⟨7656497715655639819959013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40834654483496745706448069 7656497715655639819959013)
                  ·
                    refine ⟨1435593321685432466242315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656497715655639819959013 1435593321685432466242315)
                    ·
                      rfl

theorem cell23_8387424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_8387424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387424 prefixEnd_8387424 := by exact prefixLift 8387424
  have htrace : WordTrace (prefixWord ++ tailWord_8387424) baseStart_8387424 baseEnd_8387424 := by
    simpa [prefixWord, tailWord_8387424, baseEnd_8387424] using wordTrace_append hprefix tailTrace_8387424
  have hstable : (prefixWord ++ tailWord_8387424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387424).length < 2 ^ (prefixWord ++ tailWord_8387424).sum := by decide
  have hdescent : baseEnd_8387424 < baseStart_8387424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387441 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_8387441 : Nat := 118140960795 + 8387441 * 2 ^ 59
def prefixEnd_8387441 : Nat := 4983230072969 + 3 ^ 40 * 8387441 * 2
def baseEnd_8387441 : Nat := 1435596231409141277404789

theorem tailTrace_8387441 : CollatzResearch.WordTrace tailWord_8387441 prefixEnd_8387441 1435596231409141277404789 := by
  unfold tailWord_8387441
  simp only [CollatzResearch.WordTrace]
  refine ⟨305915105206741192723874177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203943403471160795149249451 305915105206741192723874177)
  ·
    refine ⟨229436328905055894542905633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305915105206741192723874177 229436328905055894542905633)
    ·
      refine ⟨172077246678791920907179225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229436328905055894542905633 172077246678791920907179225)
      ·
        refine ⟨129057935009093940680384419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172077246678791920907179225 129057935009093940680384419)
        ·
          refine ⟨193586902513640911020576629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129057935009093940680384419 193586902513640911020576629)
          ·
            refine ⟨18148772110653835408179059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 193586902513640911020576629 18148772110653835408179059)
            ·
              refine ⟨27223158165980753112268589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148772110653835408179059 27223158165980753112268589)
              ·
                refine ⟨10208684312242782417100721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27223158165980753112268589 10208684312242782417100721)
                ·
                  refine ⟨7656513234182086812825541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10208684312242782417100721 7656513234182086812825541)
                  ·
                    refine ⟨1435596231409141277404789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656513234182086812825541 1435596231409141277404789)
                    ·
                      rfl

theorem cell23_8387441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_8387441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387441 prefixEnd_8387441 := by exact prefixLift 8387441
  have htrace : WordTrace (prefixWord ++ tailWord_8387441) baseStart_8387441 baseEnd_8387441 := by
    simpa [prefixWord, tailWord_8387441, baseEnd_8387441] using wordTrace_append hprefix tailTrace_8387441
  have hstable : (prefixWord ++ tailWord_8387441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387441).length < 2 ^ (prefixWord ++ tailWord_8387441).sum := by decide
  have hdescent : baseEnd_8387441 < baseStart_8387441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387451 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 3]
def baseStart_8387451 : Nat := 118140960795 + 8387451 * 2 ^ 59
def prefixEnd_8387451 : Nat := 4983230072969 + 3 ^ 40 * 8387451 * 2
def baseEnd_8387451 : Nat := 4306793829033968793089321

theorem tailTrace_8387451 : CollatzResearch.WordTrace tailWord_8387451 prefixEnd_8387451 4306793829033968793089321 := by
  unfold tailWord_8387451
  simp only [CollatzResearch.WordTrace]
  refine ⟨305915469936704964431738207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203943646624469976287825471 305915469936704964431738207)
  ·
    refine ⟨458873204905057446647607311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305915469936704964431738207 458873204905057446647607311)
    ·
      refine ⟨688309807357586169971410967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458873204905057446647607311 688309807357586169971410967)
      ·
        refine ⟨1032464711036379254957116451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688309807357586169971410967 1032464711036379254957116451)
        ·
          refine ⟨1548697066554568882435674677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032464711036379254957116451 1548697066554568882435674677)
          ·
            refine ⟨145190349989490832728344501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1548697066554568882435674677 145190349989490832728344501)
            ·
              refine ⟨13611595311514765568282297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145190349989490832728344501 13611595311514765568282297)
              ·
                refine ⟨10208696483636074176211723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13611595311514765568282297 10208696483636074176211723)
                ·
                  refine ⟨15313044725454111264317585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208696483636074176211723 15313044725454111264317585)
                  ·
                    refine ⟨11484783544090583448238189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15313044725454111264317585 11484783544090583448238189)
                    ·
                      refine ⟨4306793829033968793089321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11484783544090583448238189 4306793829033968793089321)
                      ·
                        rfl

theorem cell23_8387451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 2, 3].length) (baseStart_8387451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387451 prefixEnd_8387451 := by exact prefixLift 8387451
  have htrace : WordTrace (prefixWord ++ tailWord_8387451) baseStart_8387451 baseEnd_8387451 := by
    simpa [prefixWord, tailWord_8387451, baseEnd_8387451] using wordTrace_append hprefix tailTrace_8387451
  have hstable : (prefixWord ++ tailWord_8387451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387451).length < 2 ^ (prefixWord ++ tailWord_8387451).sum := by decide
  have hdescent : baseEnd_8387451 < baseStart_8387451 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387482 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2]
def baseStart_8387482 : Nat := 118140960795 + 8387482 * 2 ^ 59
def prefixEnd_8387482 : Nat := 4983230072969 + 3 ^ 40 * 8387482 * 2
def baseEnd_8387482 : Nat := 4306809746934258171801679

theorem tailTrace_8387482 : CollatzResearch.WordTrace tailWord_8387482 prefixEnd_8387482 4306809746934258171801679 := by
  unfold tailWord_8387482
  simp only [CollatzResearch.WordTrace]
  refine ⟨76479150149898164181529175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203944400399728437817411133 76479150149898164181529175)
  ·
    refine ⟨114718725224847246272293763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76479150149898164181529175 114718725224847246272293763)
    ·
      refine ⟨172078087837270869408440645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114718725224847246272293763 172078087837270869408440645)
      ·
        refine ⟨32264641469488288014082621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172078087837270869408440645 32264641469488288014082621)
        ·
          refine ⟨12099240551058108005280983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32264641469488288014082621 12099240551058108005280983)
          ·
            refine ⟨18148860826587162007921475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099240551058108005280983 18148860826587162007921475)
            ·
              refine ⟨27223291239880743011882213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18148860826587162007921475 27223291239880743011882213)
              ·
                refine ⟨5104367107477639314727915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27223291239880743011882213 5104367107477639314727915)
                ·
                  refine ⟨7656550661216458972091873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104367107477639314727915 7656550661216458972091873)
                  ·
                    refine ⟨5742412995912344229068905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7656550661216458972091873 5742412995912344229068905)
                    ·
                      refine ⟨4306809746934258171801679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742412995912344229068905 4306809746934258171801679)
                      ·
                        rfl

theorem cell23_8387482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_8387482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387482 prefixEnd_8387482 := by exact prefixLift 8387482
  have htrace : WordTrace (prefixWord ++ tailWord_8387482) baseStart_8387482 baseEnd_8387482 := by
    simpa [prefixWord, tailWord_8387482, baseEnd_8387482] using wordTrace_append hprefix tailTrace_8387482
  have hstable : (prefixWord ++ tailWord_8387482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387482).length < 2 ^ (prefixWord ++ tailWord_8387482).sum := by decide
  have hdescent : baseEnd_8387482 < baseStart_8387482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387491 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 3, 3, 2]
def baseStart_8387491 : Nat := 118140960795 + 8387491 * 2 ^ 59
def prefixEnd_8387491 : Nat := 4983230072969 + 3 ^ 40 * 8387491 * 2
def baseEnd_8387491 : Nat := 4306814368260148636589137

theorem tailTrace_8387491 : CollatzResearch.WordTrace tailWord_8387491 prefixEnd_8387491 4306814368260148636589137 := by
  unfold tailWord_8387491
  simp only [CollatzResearch.WordTrace]
  refine ⟨305916928856560051263194327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203944619237706700842129551 305916928856560051263194327)
  ·
    refine ⟨458875393284840076894791491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305916928856560051263194327 458875393284840076894791491)
    ·
      refine ⟨688313089927260115342187237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458875393284840076894791491 688313089927260115342187237)
      ·
        refine ⟨129058704361361271626660107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 688313089927260115342187237 129058704361361271626660107)
        ·
          refine ⟨193588056542041907439990161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129058704361361271626660107 193588056542041907439990161)
          ·
            refine ⟨145191042406531430579992621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193588056542041907439990161 145191042406531430579992621)
            ·
              refine ⟨54446640902449286467497233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145191042406531430579992621 54446640902449286467497233)
              ·
                refine ⟨40834980676836964850622925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54446640902449286467497233 40834980676836964850622925)
                ·
                  refine ⟨15313117753813861818983597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40834980676836964850622925 15313117753813861818983597)
                  ·
                    refine ⟨5742419157680198182118849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15313117753813861818983597 5742419157680198182118849)
                    ·
                      refine ⟨4306814368260148636589137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742419157680198182118849 4306814368260148636589137)
                      ·
                        rfl

theorem cell23_8387491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 3, 2].length) (baseStart_8387491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387491 prefixEnd_8387491 := by exact prefixLift 8387491
  have htrace : WordTrace (prefixWord ++ tailWord_8387491) baseStart_8387491 baseEnd_8387491 := by
    simpa [prefixWord, tailWord_8387491, baseEnd_8387491] using wordTrace_append hprefix tailTrace_8387491
  have hstable : (prefixWord ++ tailWord_8387491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387491).length < 2 ^ (prefixWord ++ tailWord_8387491).sum := by decide
  have hdescent : baseEnd_8387491 < baseStart_8387491 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387526 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_8387526 : Nat := 118140960795 + 8387526 * 2 ^ 59
def prefixEnd_8387526 : Nat := 4983230072969 + 3 ^ 40 * 8387526 * 2
def baseEnd_8387526 : Nat := 1435610780027685333217159

theorem tailTrace_8387526 : CollatzResearch.WordTrace tailWord_8387526 prefixEnd_8387526 1435610780027685333217159 := by
  unfold tailWord_8387526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559943919107289132522451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 203945470274288834827145621 9559943919107289132522451)
  ·
    refine ⟨14339915878660933698783677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9559943919107289132522451 14339915878660933698783677)
    ·
      refine ⟨5377468454497850137043879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14339915878660933698783677 5377468454497850137043879)
      ·
        refine ⟨8066202681746775205565819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377468454497850137043879 8066202681746775205565819)
        ·
          refine ⟨12099304022620162808348729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066202681746775205565819 12099304022620162808348729)
          ·
            refine ⟨9074478016965122106261547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12099304022620162808348729 9074478016965122106261547)
            ·
              refine ⟨13611717025447683159392321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9074478016965122106261547 13611717025447683159392321)
              ·
                refine ⟨10208787769085762369544241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13611717025447683159392321 10208787769085762369544241)
                ·
                  refine ⟨7656590826814321777158181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10208787769085762369544241 7656590826814321777158181)
                  ·
                    refine ⟨1435610780027685333217159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656590826814321777158181 1435610780027685333217159)
                    ·
                      rfl

theorem cell23_8387526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_8387526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387526 prefixEnd_8387526 := by exact prefixLift 8387526
  have htrace : WordTrace (prefixWord ++ tailWord_8387526) baseStart_8387526 baseEnd_8387526 := by
    simpa [prefixWord, tailWord_8387526, baseEnd_8387526] using wordTrace_append hprefix tailTrace_8387526
  have hstable : (prefixWord ++ tailWord_8387526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387526).length < 2 ^ (prefixWord ++ tailWord_8387526).sum := by decide
  have hdescent : baseEnd_8387526 < baseStart_8387526 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387544 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 7]
def baseStart_8387544 : Nat := 118140960795 + 8387544 * 2 ^ 59
def prefixEnd_8387544 : Nat := 4983230072969 + 3 ^ 40 * 8387544 * 2
def baseEnd_8387544 : Nat := 478537953637204103247377

theorem tailTrace_8387544 : CollatzResearch.WordTrace tailWord_8387544 prefixEnd_8387544 478537953637204103247377 := by
  unfold tailWord_8387544
  simp only [CollatzResearch.WordTrace]
  refine ⟨152959430962684020657436843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 203945907950245360876582457 152959430962684020657436843)
  ·
    refine ⟨229439146444026030986155265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152959430962684020657436843 229439146444026030986155265)
    ·
      refine ⟨172079359833019523239616449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229439146444026030986155265 172079359833019523239616449)
      ·
        refine ⟨129059519874764642429712337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172079359833019523239616449 129059519874764642429712337)
        ·
          refine ⟨96794639906073481822284253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129059519874764642429712337 96794639906073481822284253)
          ·
            refine ⟨36297989964777555683356595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96794639906073481822284253 36297989964777555683356595)
            ·
              refine ⟨54446984947166333525034893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36297989964777555683356595 54446984947166333525034893)
              ·
                refine ⟨20417619355187375071888085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54446984947166333525034893 20417619355187375071888085)
                ·
                  refine ⟨478537953637204103247377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20417619355187375071888085 478537953637204103247377)
                  ·
                    rfl

theorem cell23_8387544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_8387544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387544 prefixEnd_8387544 := by exact prefixLift 8387544
  have htrace : WordTrace (prefixWord ++ tailWord_8387544) baseStart_8387544 baseEnd_8387544 := by
    simpa [prefixWord, tailWord_8387544, baseEnd_8387544] using wordTrace_append hprefix tailTrace_8387544
  have hstable : (prefixWord ++ tailWord_8387544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387544).length < 2 ^ (prefixWord ++ tailWord_8387544).sum := by decide
  have hdescent : baseEnd_8387544 < baseStart_8387544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387581 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 7, 2]
def baseStart_8387581 : Nat := 118140960795 + 8387581 * 2 ^ 59
def prefixEnd_8387581 : Nat := 4983230072969 + 3 ^ 40 * 8387581 * 2
def baseEnd_8387581 : Nat := 4306860581519053284463723

theorem tailTrace_8387581 : CollatzResearch.WordTrace tailWord_8387581 prefixEnd_8387581 4306860581519053284463723 := by
  unfold tailWord_8387581
  simp only [CollatzResearch.WordTrace]
  refine ⟨305920211426233996633970597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203946807617489331089313731 305920211426233996633970597)
  ·
    refine ⟨57360039642418874368869487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305920211426233996633970597 57360039642418874368869487)
    ·
      refine ⟨86040059463628311553304231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57360039642418874368869487 86040059463628311553304231)
      ·
        refine ⟨129060089195442467329956347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86040059463628311553304231 129060089195442467329956347)
        ·
          refine ⟨193590133793163700994934521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129060089195442467329956347 193590133793163700994934521)
          ·
            refine ⟨145192600344872775746200891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193590133793163700994934521 145192600344872775746200891)
            ·
              refine ⟨217788900517309163619301337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145192600344872775746200891 217788900517309163619301337)
              ·
                refine ⟨163341675387981872714476003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217788900517309163619301337 163341675387981872714476003)
                ·
                  refine ⟨245012513081972809071714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163341675387981872714476003 245012513081972809071714005)
                  ·
                    refine ⟨5742480775358737712618297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 245012513081972809071714005 5742480775358737712618297)
                    ·
                      refine ⟨4306860581519053284463723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742480775358737712618297 4306860581519053284463723)
                      ·
                        rfl

theorem cell23_8387581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_8387581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387581 prefixEnd_8387581 := by exact prefixLift 8387581
  have htrace : WordTrace (prefixWord ++ tailWord_8387581) baseStart_8387581 baseEnd_8387581 := by
    simpa [prefixWord, tailWord_8387581, baseEnd_8387581] using wordTrace_append hprefix tailTrace_8387581
  have hstable : (prefixWord ++ tailWord_8387581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387581).length < 2 ^ (prefixWord ++ tailWord_8387581).sum := by decide
  have hdescent : baseEnd_8387581 < baseStart_8387581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387591 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 2, 5]
def baseStart_8387591 : Nat := 118140960795 + 8387591 * 2 ^ 59
def prefixEnd_8387591 : Nat := 4983230072969 + 3 ^ 40 * 8387591 * 2
def baseEnd_8387591 : Nat := 1435621905441866081779559

theorem tailTrace_8387591 : CollatzResearch.WordTrace tailWord_8387591 prefixEnd_8387591 1435621905441866081779559 := by
  unfold tailWord_8387591
  simp only [CollatzResearch.WordTrace]
  refine ⟨305920576156197768341834627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203947050770798512227889751 305920576156197768341834627)
  ·
    refine ⟨458880864234296652512751941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305920576156197768341834627 458880864234296652512751941)
    ·
      refine ⟨86040162043930622346140989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458880864234296652512751941 86040162043930622346140989)
      ·
        refine ⟨32265060766473983379802871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86040162043930622346140989 32265060766473983379802871)
        ·
          refine ⟨48397591149710975069704307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32265060766473983379802871 48397591149710975069704307)
          ·
            refine ⟨72596386724566462604556461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48397591149710975069704307 72596386724566462604556461)
            ·
              refine ⟨27223645021712423476708673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72596386724566462604556461 27223645021712423476708673)
              ·
                refine ⟨20417733766284317607531505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27223645021712423476708673 20417733766284317607531505)
                ·
                  refine ⟨15313300324713238205648629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20417733766284317607531505 15313300324713238205648629)
                  ·
                    refine ⟨1435621905441866081779559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15313300324713238205648629 1435621905441866081779559)
                    ·
                      rfl

theorem cell23_8387591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_8387591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387591 prefixEnd_8387591 := by exact prefixLift 8387591
  have htrace : WordTrace (prefixWord ++ tailWord_8387591) baseStart_8387591 baseEnd_8387591 := by
    simpa [prefixWord, tailWord_8387591, baseEnd_8387591] using wordTrace_append hprefix tailTrace_8387591
  have hstable : (prefixWord ++ tailWord_8387591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387591).length < 2 ^ (prefixWord ++ tailWord_8387591).sum := by decide
  have hdescent : baseEnd_8387591 < baseStart_8387591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387611 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 6, 4, 2]
def baseStart_8387611 : Nat := 118140960795 + 8387611 * 2 ^ 59
def prefixEnd_8387611 : Nat := 4983230072969 + 3 ^ 40 * 8387611 * 2
def baseEnd_8387611 : Nat := 4306875985938688167088585

theorem tailTrace_8387611 : CollatzResearch.WordTrace tailWord_8387611 prefixEnd_8387611 4306875985938688167088585 := by
  unfold tailWord_8387611
  simp only [CollatzResearch.WordTrace]
  refine ⟨305921305616125311757562687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203947537077416874505041791 305921305616125311757562687)
  ·
    refine ⟨458881958424187967636344031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305921305616125311757562687 458881958424187967636344031)
    ·
      refine ⟨688322937636281951454516047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458881958424187967636344031 688322937636281951454516047)
      ·
        refine ⟨1032484406454422927181774071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688322937636281951454516047 1032484406454422927181774071)
        ·
          refine ⟨1548726609681634390772661107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1032484406454422927181774071 1548726609681634390772661107)
          ·
            refine ⟨2323089914522451586158991661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1548726609681634390772661107 2323089914522451586158991661)
            ·
              refine ⟨871158717945919344809621873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2323089914522451586158991661 871158717945919344809621873)
              ·
                refine ⟨653369038459439508607216405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 871158717945919344809621873 653369038459439508607216405)
                ·
                  refine ⟨30626673677786226965963269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 653369038459439508607216405 30626673677786226965963269)
                  ·
                    refine ⟨5742501314584917556118113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30626673677786226965963269 5742501314584917556118113)
                    ·
                      refine ⟨4306875985938688167088585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5742501314584917556118113 4306875985938688167088585)
                      ·
                        rfl

theorem cell23_8387611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 4, 2].length) (baseStart_8387611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387611 prefixEnd_8387611 := by exact prefixLift 8387611
  have htrace : WordTrace (prefixWord ++ tailWord_8387611) baseStart_8387611 baseEnd_8387611 := by
    simpa [prefixWord, tailWord_8387611, baseEnd_8387611] using wordTrace_append hprefix tailTrace_8387611
  have hstable : (prefixWord ++ tailWord_8387611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387611).length < 2 ^ (prefixWord ++ tailWord_8387611).sum := by decide
  have hdescent : baseEnd_8387611 < baseStart_8387611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387621 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_8387621 : Nat := 118140960795 + 8387621 * 2 ^ 59
def prefixEnd_8387621 : Nat := 4983230072969 + 3 ^ 40 * 8387621 * 2
def baseEnd_8387621 : Nat := 1435627040248411042654513

theorem tailTrace_8387621 : CollatzResearch.WordTrace tailWord_8387621 prefixEnd_8387621 1435627040248411042654513 := by
  unfold tailWord_8387621
  simp only [CollatzResearch.WordTrace]
  refine ⟨305921670346089083465426717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203947780230726055643617811 305921670346089083465426717)
  ·
    refine ⟨114720626379783406299535019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 305921670346089083465426717 114720626379783406299535019)
    ·
      refine ⟨172080939569675109449302529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114720626379783406299535019 172080939569675109449302529)
      ·
        refine ⟨129060704677256332086976897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172080939569675109449302529 129060704677256332086976897)
        ·
          refine ⟨96795528507942249065232673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129060704677256332086976897 96795528507942249065232673)
          ·
            refine ⟨72596646380956686798924505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96795528507942249065232673 72596646380956686798924505)
            ·
              refine ⟨54447484785717515099193379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72596646380956686798924505 54447484785717515099193379)
              ·
                refine ⟨81671227178576272648790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54447484785717515099193379 81671227178576272648790069)
                ·
                  refine ⟨7656677547991525560824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81671227178576272648790069 7656677547991525560824069)
                  ·
                    refine ⟨1435627040248411042654513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656677547991525560824069 1435627040248411042654513)
                    ·
                      rfl

theorem cell23_8387621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_8387621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387621 prefixEnd_8387621 := by exact prefixLift 8387621
  have htrace : WordTrace (prefixWord ++ tailWord_8387621) baseStart_8387621 baseEnd_8387621 := by
    simpa [prefixWord, tailWord_8387621, baseEnd_8387621] using wordTrace_append hprefix tailTrace_8387621
  have hstable : (prefixWord ++ tailWord_8387621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387621).length < 2 ^ (prefixWord ++ tailWord_8387621).sum := by decide
  have hdescent : baseEnd_8387621 < baseStart_8387621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387651 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 6]
def baseStart_8387651 : Nat := 118140960795 + 8387651 * 2 ^ 59
def prefixEnd_8387651 : Nat := 4983230072969 + 3 ^ 40 * 8387651 * 2
def baseEnd_8387651 : Nat := 478544058351652001176489

theorem tailTrace_8387651 : CollatzResearch.WordTrace tailWord_8387651 prefixEnd_8387651 478544058351652001176489 := by
  unfold tailWord_8387651
  simp only [CollatzResearch.WordTrace]
  refine ⟨305922764535980398589018807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203948509690653599059345871 305922764535980398589018807)
  ·
    refine ⟨458884146803970597883528211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305922764535980398589018807 458884146803970597883528211)
    ·
      refine ⟨688326220205955896825292317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458884146803970597883528211 688326220205955896825292317)
      ·
        refine ⟨258122332577233461309484619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 688326220205955896825292317 258122332577233461309484619)
        ·
          refine ⟨387183498865850191964226929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258122332577233461309484619 387183498865850191964226929)
          ·
            refine ⟨290387624149387643973170197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387183498865850191964226929 290387624149387643973170197)
            ·
              refine ⟨13611919882002545811242353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290387624149387643973170197 13611919882002545811242353)
              ·
                refine ⟨10208939911501909358431765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13611919882002545811242353 10208939911501909358431765)
                ·
                  refine ⟨478544058351652001176489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10208939911501909358431765 478544058351652001176489)
                  ·
                    rfl

theorem cell23_8387651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 6].length) (baseStart_8387651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387651 prefixEnd_8387651 := by exact prefixLift 8387651
  have htrace : WordTrace (prefixWord ++ tailWord_8387651) baseStart_8387651 baseEnd_8387651 := by
    simpa [prefixWord, tailWord_8387651, baseEnd_8387651] using wordTrace_append hprefix tailTrace_8387651
  have hstable : (prefixWord ++ tailWord_8387651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387651).length < 2 ^ (prefixWord ++ tailWord_8387651).sum := by decide
  have hdescent : baseEnd_8387651 < baseStart_8387651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387655 : List Nat := [1, 1, 4, 1, 3, 3, 1, 4, 1, 4]
def baseStart_8387655 : Nat := 118140960795 + 8387655 * 2 ^ 59
def prefixEnd_8387655 : Nat := 4983230072969 + 3 ^ 40 * 8387655 * 2
def baseEnd_8387655 : Nat := 1435632859695828664979461

theorem tailTrace_8387655 : CollatzResearch.WordTrace tailWord_8387655 prefixEnd_8387655 1435632859695828664979461 := by
  unfold tailWord_8387655
  simp only [CollatzResearch.WordTrace]
  refine ⟨305922910427965907272164419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203948606951977271514776279 305922910427965907272164419)
  ·
    refine ⟨458884365641948860908246629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305922910427965907272164419 458884365641948860908246629)
    ·
      refine ⟨86040818557865411420296243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 458884365641948860908246629 86040818557865411420296243)
      ·
        refine ⟨129061227836798117130444365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86040818557865411420296243 129061227836798117130444365)
        ·
          refine ⟨48397960438799293923916637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129061227836798117130444365 48397960438799293923916637)
          ·
            refine ⟨18149235164549735221468739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48397960438799293923916637 18149235164549735221468739)
            ·
              refine ⟨27223852746824602832203109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149235164549735221468739 27223852746824602832203109)
              ·
                refine ⟨5104472390029613031038083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27223852746824602832203109 5104472390029613031038083)
                ·
                  refine ⟨7656708585044419546557125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104472390029613031038083 7656708585044419546557125)
                  ·
                    refine ⟨1435632859695828664979461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7656708585044419546557125 1435632859695828664979461)
                    ·
                      rfl

theorem cell23_8387655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_8387655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387655 prefixEnd_8387655 := by exact prefixLift 8387655
  have htrace : WordTrace (prefixWord ++ tailWord_8387655) baseStart_8387655 baseEnd_8387655 := by
    simpa [prefixWord, tailWord_8387655, baseEnd_8387655] using wordTrace_append hprefix tailTrace_8387655
  have hstable : (prefixWord ++ tailWord_8387655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387655).length < 2 ^ (prefixWord ++ tailWord_8387655).sum := by decide
  have hdescent : baseEnd_8387655 < baseStart_8387655 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387681 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_8387681 : Nat := 118140960795 + 8387681 * 2 ^ 59
def prefixEnd_8387681 : Nat := 4983230072969 + 3 ^ 40 * 8387681 * 2
def baseEnd_8387681 : Nat := 1435637309861500964404421

theorem tailTrace_8387681 : CollatzResearch.WordTrace tailWord_8387681 prefixEnd_8387681 1435637309861500964404421 := by
  unfold tailWord_8387681
  simp only [CollatzResearch.WordTrace]
  refine ⟨305923858725871713712610897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203949239150581142475073931 305923858725871713712610897)
  ·
    refine ⟨229442894044403785284458173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305923858725871713712610897 229442894044403785284458173)
    ·
      refine ⟨86041085266651419481671815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229442894044403785284458173 86041085266651419481671815)
      ·
        refine ⟨129061627899977129222507723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86041085266651419481671815 129061627899977129222507723)
        ·
          refine ⟨193592441849965693833761585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129061627899977129222507723 193592441849965693833761585)
          ·
            refine ⟨145194331387474270375321189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193592441849965693833761585 145194331387474270375321189)
            ·
              refine ⟨27223937135151425695372723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145194331387474270375321189 27223937135151425695372723)
              ·
                refine ⟨40835905702727138543059085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27223937135151425695372723 40835905702727138543059085)
                ·
                  refine ⟨15313464638522676953647157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40835905702727138543059085 15313464638522676953647157)
                  ·
                    refine ⟨1435637309861500964404421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15313464638522676953647157 1435637309861500964404421)
                    ·
                      rfl

theorem cell23_8387681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_8387681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387681 prefixEnd_8387681 := by exact prefixLift 8387681
  have htrace : WordTrace (prefixWord ++ tailWord_8387681) baseStart_8387681 baseEnd_8387681 := by
    simpa [prefixWord, tailWord_8387681, baseEnd_8387681] using wordTrace_append hprefix tailTrace_8387681
  have hstable : (prefixWord ++ tailWord_8387681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387681).length < 2 ^ (prefixWord ++ tailWord_8387681).sum := by decide
  have hdescent : baseEnd_8387681 < baseStart_8387681 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387682 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_8387682 : Nat := 118140960795 + 8387682 * 2 ^ 59
def prefixEnd_8387682 : Nat := 4983230072969 + 3 ^ 40 * 8387682 * 2
def baseEnd_8387682 : Nat := 4306912443065157389300759

theorem tailTrace_8387682 : CollatzResearch.WordTrace tailWord_8387682 prefixEnd_8387682 4306912443065157389300759 := by
  unfold tailWord_8387682
  simp only [CollatzResearch.WordTrace]
  refine ⟨76480973799717022720849325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203949263465912060588931533 76480973799717022720849325)
  ·
    refine ⟨28680365174893883520318497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76480973799717022720849325 28680365174893883520318497)
    ·
      refine ⟨21510273881170412640238873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28680365174893883520318497 21510273881170412640238873)
      ·
        refine ⟨16132705410877809480179155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21510273881170412640238873 16132705410877809480179155)
        ·
          refine ⟨24199058116316714220268733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16132705410877809480179155 24199058116316714220268733)
          ·
            refine ⟨9074646793618767832600775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24199058116316714220268733 9074646793618767832600775)
            ·
              refine ⟨13611970190428151748901163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9074646793618767832600775 13611970190428151748901163)
              ·
                refine ⟨20417955285642227623351745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13611970190428151748901163 20417955285642227623351745)
                ·
                  refine ⟨15313466464231670717513809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20417955285642227623351745 15313466464231670717513809)
                  ·
                    refine ⟨11485099848173753038135357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15313466464231670717513809 11485099848173753038135357)
                    ·
                      refine ⟨4306912443065157389300759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11485099848173753038135357 4306912443065157389300759)
                      ·
                        rfl

theorem cell23_8387682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_8387682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387682 prefixEnd_8387682 := by exact prefixLift 8387682
  have htrace : WordTrace (prefixWord ++ tailWord_8387682) baseStart_8387682 baseEnd_8387682 := by
    simpa [prefixWord, tailWord_8387682, baseEnd_8387682] using wordTrace_append hprefix tailTrace_8387682
  have hstable : (prefixWord ++ tailWord_8387682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387682).length < 2 ^ (prefixWord ++ tailWord_8387682).sum := by decide
  have hdescent : baseEnd_8387682 < baseStart_8387682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387698 : List Nat := [3, 2, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_8387698 : Nat := 118140960795 + 8387698 * 2 ^ 59
def prefixEnd_8387698 : Nat := 4983230072969 + 3 ^ 40 * 8387698 * 2
def baseEnd_8387698 : Nat := 1435640219585209775566895

theorem tailTrace_8387698 : CollatzResearch.WordTrace tailWord_8387698 prefixEnd_8387698 1435640219585209775566895 := by
  unfold tailWord_8387698
  simp only [CollatzResearch.WordTrace]
  refine ⟨76481119691702531403994937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 203949652511206750410653165 76481119691702531403994937)
  ·
    refine ⟨57360839768776898552996203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76481119691702531403994937 57360839768776898552996203)
    ·
      refine ⟨86041259653165347829494305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57360839768776898552996203 86041259653165347829494305)
      ·
        refine ⟨64530944739874010872120729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86041259653165347829494305 64530944739874010872120729)
        ·
          refine ⟨48398208554905508154090547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64530944739874010872120729 48398208554905508154090547)
          ·
            refine ⟨72597312832358262231135821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48398208554905508154090547 72597312832358262231135821)
            ·
              refine ⟨27223992312134348336675933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72597312832358262231135821 27223992312134348336675933)
              ·
                refine ⟨10208997117050380626253475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27223992312134348336675933 10208997117050380626253475)
                ·
                  refine ⟨15313495675575570939380213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208997117050380626253475 15313495675575570939380213)
                  ·
                    refine ⟨1435640219585209775566895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15313495675575570939380213 1435640219585209775566895)
                    ·
                      rfl

theorem cell23_8387698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_8387698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387698 prefixEnd_8387698 := by exact prefixLift 8387698
  have htrace : WordTrace (prefixWord ++ tailWord_8387698) baseStart_8387698 baseEnd_8387698 := by
    simpa [prefixWord, tailWord_8387698, baseEnd_8387698] using wordTrace_append hprefix tailTrace_8387698
  have hstable : (prefixWord ++ tailWord_8387698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387698).length < 2 ^ (prefixWord ++ tailWord_8387698).sum := by decide
  have hdescent : baseEnd_8387698 < baseStart_8387698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387721 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_8387721 : Nat := 118140960795 + 8387721 * 2 ^ 59
def prefixEnd_8387721 : Nat := 4983230072969 + 3 ^ 40 * 8387721 * 2
def baseEnd_8387721 : Nat := 4306932468810682736713079

theorem tailTrace_8387721 : CollatzResearch.WordTrace tailWord_8387721 prefixEnd_8387721 4306932468810682736713079 := by
  unfold tailWord_8387721
  simp only [CollatzResearch.WordTrace]
  refine ⟨305925317645726800544067017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203950211763817867029378011 305925317645726800544067017)
  ·
    refine ⟨229443988234295100408050263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 305925317645726800544067017 229443988234295100408050263)
    ·
      refine ⟨344165982351442650612075395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229443988234295100408050263 344165982351442650612075395)
      ·
        refine ⟨516248973527163975918113093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344165982351442650612075395 516248973527163975918113093)
        ·
          refine ⟨96796682536343245484646205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 516248973527163975918113093 96796682536343245484646205)
          ·
            refine ⟨36298755951128717056742327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96796682536343245484646205 36298755951128717056742327)
            ·
              refine ⟨54448133926693075585113491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36298755951128717056742327 54448133926693075585113491)
              ·
                refine ⟨81672200890039613377670237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54448133926693075585113491 81672200890039613377670237)
                ·
                  refine ⟨30627075333764855016626339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81672200890039613377670237 30627075333764855016626339)
                  ·
                    refine ⟨45940613000647282524939509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30627075333764855016626339 45940613000647282524939509)
                    ·
                      refine ⟨4306932468810682736713079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45940613000647282524939509 4306932468810682736713079)
                      ·
                        rfl

theorem cell23_8387721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_8387721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387721 prefixEnd_8387721 := by exact prefixLift 8387721
  have htrace : WordTrace (prefixWord ++ tailWord_8387721) baseStart_8387721 baseEnd_8387721 := by
    simpa [prefixWord, tailWord_8387721, baseEnd_8387721] using wordTrace_append hprefix tailTrace_8387721
  have hstable : (prefixWord ++ tailWord_8387721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387721).length < 2 ^ (prefixWord ++ tailWord_8387721).sum := by decide
  have hdescent : baseEnd_8387721 < baseStart_8387721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387735 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_8387735 : Nat := 118140960795 + 8387735 * 2 ^ 59
def prefixEnd_8387735 : Nat := 4983230072969 + 3 ^ 40 * 8387735 * 2
def baseEnd_8387735 : Nat := 4306939657539845681938015

theorem tailTrace_8387735 : CollatzResearch.WordTrace tailWord_8387735 prefixEnd_8387735 4306939657539845681938015 := by
  unfold tailWord_8387735
  simp only [CollatzResearch.WordTrace]
  refine ⟨305925828267676080935076659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203950552178450720623384439 305925828267676080935076659)
  ·
    refine ⟨458888742401514121402614989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305925828267676080935076659 458888742401514121402614989)
    ·
      refine ⟨172083278400567795525980621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458888742401514121402614989 172083278400567795525980621)
      ·
        refine ⟨64531229400212923322242733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172083278400567795525980621 64531229400212923322242733)
        ·
          refine ⟨24199211025079846245841025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64531229400212923322242733 24199211025079846245841025)
          ·
            refine ⟨18149408268809884684380769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24199211025079846245841025 18149408268809884684380769)
            ·
              refine ⟨13612056201607413513285577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18149408268809884684380769 13612056201607413513285577)
              ·
                refine ⟨10209042151205560134964183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13612056201607413513285577 10209042151205560134964183)
                ·
                  refine ⟨15313563226808340202446275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209042151205560134964183 15313563226808340202446275)
                  ·
                    refine ⟨22970344840212510303669413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15313563226808340202446275 22970344840212510303669413)
                    ·
                      refine ⟨4306939657539845681938015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22970344840212510303669413 4306939657539845681938015)
                      ·
                        rfl

theorem cell23_8387735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_8387735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387735 prefixEnd_8387735 := by exact prefixLift 8387735
  have htrace : WordTrace (prefixWord ++ tailWord_8387735) baseStart_8387735 baseEnd_8387735 := by
    simpa [prefixWord, tailWord_8387735, baseEnd_8387735] using wordTrace_append hprefix tailTrace_8387735
  have hstable : (prefixWord ++ tailWord_8387735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387735).length < 2 ^ (prefixWord ++ tailWord_8387735).sum := by decide
  have hdescent : baseEnd_8387735 < baseStart_8387735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8387741 : List Nat := [1, 4, 2, 1, 1, 2, 3, 9]
def baseStart_8387741 : Nat := 118140960795 + 8387741 * 2 ^ 59
def prefixEnd_8387741 : Nat := 4983230072969 + 3 ^ 40 * 8387741 * 2
def baseEnd_8387741 : Nat := 159516397719398987350481

theorem tailTrace_8387741 : CollatzResearch.WordTrace tailWord_8387741 prefixEnd_8387741 159516397719398987350481 := by
  unfold tailWord_8387741
  simp only [CollatzResearch.WordTrace]
  refine ⟨305926047105654343959795077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 203950698070436229306530051 305926047105654343959795077)
  ·
    refine ⟨57361133832310189492461577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 305926047105654343959795077 57361133832310189492461577)
    ·
      refine ⟨43020850374232642119346183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57361133832310189492461577 43020850374232642119346183)
      ·
        refine ⟨64531275561348963179019275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43020850374232642119346183 64531275561348963179019275)
        ·
          refine ⟨96796913342023444768528913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64531275561348963179019275 96796913342023444768528913)
          ·
            refine ⟨72597685006517583576396685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96796913342023444768528913 72597685006517583576396685)
            ·
              refine ⟨27224131877444093841148757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72597685006517583576396685 27224131877444093841148757)
              ·
                refine ⟨159516397719398987350481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 27224131877444093841148757 159516397719398987350481)
                ·
                  rfl

theorem cell23_8387741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 9].length) (baseStart_8387741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8387741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8387741 prefixEnd_8387741 := by exact prefixLift 8387741
  have htrace : WordTrace (prefixWord ++ tailWord_8387741) baseStart_8387741 baseEnd_8387741 := by
    simpa [prefixWord, tailWord_8387741, baseEnd_8387741] using wordTrace_append hprefix tailTrace_8387741
  have hstable : (prefixWord ++ tailWord_8387741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8387741).length < 2 ^ (prefixWord ++ tailWord_8387741).sum := by decide
  have hdescent : baseEnd_8387741 < baseStart_8387741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8387741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
