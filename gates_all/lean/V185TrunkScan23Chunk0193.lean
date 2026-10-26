import V185TrunkScan23Chunk0192

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1142790 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1142790 : Nat := 118140960795 + 1142790 * 2 ^ 59
def prefixEnd_1142790 : Nat := 4983230072969 + 3 ^ 40 * 1142790 * 2
def baseEnd_1142790 : Nat := 65200061905743229174379

theorem tailTrace_1142790 : CollatzResearch.WordTrace tailWord_1142790 prefixEnd_1142790 65200061905743229174379 := by
  unfold tailWord_1142790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1302530485308577432456057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27787317019916318559062549 1302530485308577432456057)
  ·
    refine ⟨976897863981433074342043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1302530485308577432456057 976897863981433074342043)
    ·
      refine ⟨1465346795972149611513065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 976897863981433074342043 1465346795972149611513065)
      ·
        refine ⟨1099010096979112208634799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1465346795972149611513065 1099010096979112208634799)
        ·
          refine ⟨1648515145468668312952199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099010096979112208634799 1648515145468668312952199)
          ·
            refine ⟨2472772718203002469428299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648515145468668312952199 2472772718203002469428299)
            ·
              refine ⟨3709159077304503704142449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472772718203002469428299 3709159077304503704142449)
              ·
                refine ⟨2781869307978377778106837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3709159077304503704142449 2781869307978377778106837)
                ·
                  refine ⟨65200061905743229174379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2781869307978377778106837 65200061905743229174379)
                  ·
                    rfl

theorem cell23_1142790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1142790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142790 prefixEnd_1142790 := by exact prefixLift 1142790
  have htrace : WordTrace (prefixWord ++ tailWord_1142790) baseStart_1142790 baseEnd_1142790 := by
    simpa [prefixWord, tailWord_1142790, baseEnd_1142790] using wordTrace_append hprefix tailTrace_1142790
  have hstable : (prefixWord ++ tailWord_1142790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142790).length < 2 ^ (prefixWord ++ tailWord_1142790).sum := by decide
  have hdescent : baseEnd_1142790 < baseStart_1142790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142832 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6]
def baseStart_1142832 : Nat := 118140960795 + 1142832 * 2 ^ 59
def prefixEnd_1142832 : Nat := 4983230072969 + 3 ^ 40 * 1142832 * 2
def baseEnd_1142832 : Nat := 586822123339177898244217

theorem tailTrace_1142832 : CollatzResearch.WordTrace tailWord_1142832 prefixEnd_1142832 586822123339177898244217 := by
  unfold tailWord_1142832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841253697861159505811375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27788338263814879341081833 20841253697861159505811375)
  ·
    refine ⟨31261880546791739258717063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20841253697861159505811375 31261880546791739258717063)
    ·
      refine ⟨46892820820187608888075595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31261880546791739258717063 46892820820187608888075595)
      ·
        refine ⟨70339231230281413332113393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46892820820187608888075595 70339231230281413332113393)
        ·
          refine ⟨52754423422711059999085045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70339231230281413332113393 52754423422711059999085045)
          ·
            refine ⟨4945727195879161874914223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52754423422711059999085045 4945727195879161874914223)
            ·
              refine ⟨7418590793818742812371335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4945727195879161874914223 7418590793818742812371335)
              ·
                refine ⟨11127886190728114218557003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7418590793818742812371335 11127886190728114218557003)
                ·
                  refine ⟨16691829286092171327835505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11127886190728114218557003 16691829286092171327835505)
                  ·
                    refine ⟨12518871964569128495876629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16691829286092171327835505 12518871964569128495876629)
                    ·
                      refine ⟨586822123339177898244217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12518871964569128495876629 586822123339177898244217)
                      ·
                        rfl

theorem cell23_1142832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6].length) (baseStart_1142832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142832 prefixEnd_1142832 := by exact prefixLift 1142832
  have htrace : WordTrace (prefixWord ++ tailWord_1142832) baseStart_1142832 baseEnd_1142832 := by
    simpa [prefixWord, tailWord_1142832, baseEnd_1142832] using wordTrace_append hprefix tailTrace_1142832
  have hstable : (prefixWord ++ tailWord_1142832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142832).length < 2 ^ (prefixWord ++ tailWord_1142832).sum := by decide
  have hdescent : baseEnd_1142832 < baseStart_1142832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142876 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_1142876 : Nat := 118140960795 + 1142876 * 2 ^ 59
def prefixEnd_1142876 : Nat := 4983230072969 + 3 ^ 40 * 1142876 * 2
def baseEnd_1142876 : Nat := 195614905495991908698005

theorem tailTrace_1142876 : CollatzResearch.WordTrace tailWord_1142876 prefixEnd_1142876 195614905495991908698005 := by
  unfold tailWord_1142876
  simp only [CollatzResearch.WordTrace]
  refine ⟨20842056103781457263112241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27789408138375276350816321 20842056103781457263112241)
  ·
    refine ⟨15631542077836092947334181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20842056103781457263112241 15631542077836092947334181)
    ·
      refine ⟨2930914139594267427625159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15631542077836092947334181 2930914139594267427625159)
      ·
        refine ⟨4396371209391401141437739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930914139594267427625159 4396371209391401141437739)
        ·
          refine ⟨6594556814087101712156609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396371209391401141437739 6594556814087101712156609)
          ·
            refine ⟨4945917610565326284117457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6594556814087101712156609 4945917610565326284117457)
            ·
              refine ⟨3709438207923994713088093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4945917610565326284117457 3709438207923994713088093)
              ·
                refine ⟨1391039327971498017408035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3709438207923994713088093 1391039327971498017408035)
                ·
                  refine ⟨2086558991957247026112053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391039327971498017408035 2086558991957247026112053)
                  ·
                    refine ⟨195614905495991908698005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2086558991957247026112053 195614905495991908698005)
                    ·
                      rfl

theorem cell23_1142876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_1142876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142876 prefixEnd_1142876 := by exact prefixLift 1142876
  have htrace : WordTrace (prefixWord ++ tailWord_1142876) baseStart_1142876 baseEnd_1142876 := by
    simpa [prefixWord, tailWord_1142876, baseEnd_1142876] using wordTrace_append hprefix tailTrace_1142876
  have hstable : (prefixWord ++ tailWord_1142876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142876).length < 2 ^ (prefixWord ++ tailWord_1142876).sum := by decide
  have hdescent : baseEnd_1142876 < baseStart_1142876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142889 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_1142889 : Nat := 118140960795 + 1142889 * 2 ^ 59
def prefixEnd_1142889 : Nat := 4983230072969 + 3 ^ 40 * 1142889 * 2
def baseEnd_1142889 : Nat := 195617130578828058410485

theorem tailTrace_1142889 : CollatzResearch.WordTrace tailWord_1142889 prefixEnd_1142889 195617130578828058410485 := by
  unfold tailWord_1142889
  simp only [CollatzResearch.WordTrace]
  refine ⟨41684586356515817746447721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27789724237677211830965147 41684586356515817746447721)
  ·
    refine ⟨31263439767386863309835791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41684586356515817746447721 31263439767386863309835791)
    ·
      refine ⟨46895159651080294964753687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31263439767386863309835791 46895159651080294964753687)
      ·
        refine ⟨70342739476620442447130531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46895159651080294964753687 70342739476620442447130531)
        ·
          refine ⟨105514109214930663670695797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70342739476620442447130531 105514109214930663670695797)
          ·
            refine ⟨9891947738899749719127731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105514109214930663670695797 9891947738899749719127731)
            ·
              refine ⟨14837921608349624578691597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9891947738899749719127731 14837921608349624578691597)
              ·
                refine ⟨5564220603131109217009349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14837921608349624578691597 5564220603131109217009349)
                ·
                  refine ⟨1043291363087082978189253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5564220603131109217009349 1043291363087082978189253)
                  ·
                    refine ⟨195617130578828058410485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043291363087082978189253 195617130578828058410485)
                    ·
                      rfl

theorem cell23_1142889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_1142889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142889 prefixEnd_1142889 := by exact prefixLift 1142889
  have htrace : WordTrace (prefixWord ++ tailWord_1142889) baseStart_1142889 baseEnd_1142889 := by
    simpa [prefixWord, tailWord_1142889, baseEnd_1142889] using wordTrace_append hprefix tailTrace_1142889
  have hstable : (prefixWord ++ tailWord_1142889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142889).length < 2 ^ (prefixWord ++ tailWord_1142889).sum := by decide
  have hdescent : baseEnd_1142889 < baseStart_1142889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142890 : List Nat := [3, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1142890 : Nat := 118140960795 + 1142890 * 2 ^ 59
def prefixEnd_1142890 : Nat := 4983230072969 + 3 ^ 40 * 1142890 * 2
def baseEnd_1142890 : Nat := 586851905217138671318951

theorem tailTrace_1142890 : CollatzResearch.WordTrace tailWord_1142890 prefixEnd_1142890 586851905217138671318951 := by
  unfold tailWord_1142890
  simp only [CollatzResearch.WordTrace]
  refine ⟨10421155707378048729308531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27789748553008129944822749 10421155707378048729308531)
  ·
    refine ⟨15631733561067073093962797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10421155707378048729308531 15631733561067073093962797)
    ·
      refine ⟨5861900085400152410236049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15631733561067073093962797 5861900085400152410236049)
      ·
        refine ⟨4396425064050114307677037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5861900085400152410236049 4396425064050114307677037)
        ·
          refine ⟨1648659399018792865378889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4396425064050114307677037 1648659399018792865378889)
          ·
            refine ⟨1236494549264094649034167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648659399018792865378889 1236494549264094649034167)
            ·
              refine ⟨1854741823896141973551251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236494549264094649034167 1854741823896141973551251)
              ·
                refine ⟨2782112735844212960326877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854741823896141973551251 2782112735844212960326877)
                ·
                  refine ⟨1043292275941579860122579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2782112735844212960326877 1043292275941579860122579)
                  ·
                    refine ⟨1564938413912369790183869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1043292275941579860122579 1564938413912369790183869)
                    ·
                      refine ⟨586851905217138671318951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564938413912369790183869 586851905217138671318951)
                      ·
                        rfl

theorem cell23_1142890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1142890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142890 prefixEnd_1142890 := by exact prefixLift 1142890
  have htrace : WordTrace (prefixWord ++ tailWord_1142890) baseStart_1142890 baseEnd_1142890 := by
    simpa [prefixWord, tailWord_1142890, baseEnd_1142890] using wordTrace_append hprefix tailTrace_1142890
  have hstable : (prefixWord ++ tailWord_1142890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142890).length < 2 ^ (prefixWord ++ tailWord_1142890).sum := by decide
  have hdescent : baseEnd_1142890 < baseStart_1142890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142909 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1142909 : Nat := 118140960795 + 1142909 * 2 ^ 59
def prefixEnd_1142909 : Nat := 4983230072969 + 3 ^ 40 * 1142909 * 2
def baseEnd_1142909 : Nat := 586861661349574096981363

theorem tailTrace_1142909 : CollatzResearch.WordTrace tailWord_1142909 prefixEnd_1142909 586861661349574096981363 := by
  unfold tailWord_1142909
  simp only [CollatzResearch.WordTrace]
  refine ⟨41685315816443361162175781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27790210544295574108117187 41685315816443361162175781)
  ·
    refine ⟨7815996715583130217907959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41685315816443361162175781 7815996715583130217907959)
    ·
      refine ⟨11723995073374695326861939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7815996715583130217907959 11723995073374695326861939)
      ·
        refine ⟨17585992610062042990292909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11723995073374695326861939 17585992610062042990292909)
        ·
          refine ⟨6594747228773266121359841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17585992610062042990292909 6594747228773266121359841)
          ·
            refine ⟨4946060421579949591019881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6594747228773266121359841 4946060421579949591019881)
            ·
              refine ⟨3709545316184962193264911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4946060421579949591019881 3709545316184962193264911)
              ·
                refine ⟨5564317974277443289897367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709545316184962193264911 5564317974277443289897367)
                ·
                  refine ⟨8346476961416164934846051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564317974277443289897367 8346476961416164934846051)
                  ·
                    refine ⟨12519715442124247402269077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8346476961416164934846051 12519715442124247402269077)
                    ·
                      refine ⟨586861661349574096981363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12519715442124247402269077 586861661349574096981363)
                      ·
                        rfl

theorem cell23_1142909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1142909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142909 prefixEnd_1142909 := by exact prefixLift 1142909
  have htrace : WordTrace (prefixWord ++ tailWord_1142909) baseStart_1142909 baseEnd_1142909 := by
    simpa [prefixWord, tailWord_1142909, baseEnd_1142909] using wordTrace_append hprefix tailTrace_1142909
  have hstable : (prefixWord ++ tailWord_1142909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142909).length < 2 ^ (prefixWord ++ tailWord_1142909).sum := by decide
  have hdescent : baseEnd_1142909 < baseStart_1142909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142916 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1142916 : Nat := 118140960795 + 1142916 * 2 ^ 59
def prefixEnd_1142916 : Nat := 4983230072969 + 3 ^ 40 * 1142916 * 2
def baseEnd_1142916 : Nat := 586865255714155569593831

theorem tailTrace_1142916 : CollatzResearch.WordTrace tailWord_1142916 prefixEnd_1142916 586865255714155569593831 := by
  unfold tailWord_1142916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20842785563709000678840301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27790380751612000905120401 20842785563709000678840301)
  ·
    refine ⟨7816044586390875254565113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20842785563709000678840301 7816044586390875254565113)
    ·
      refine ⟨5862033439793156440923835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7816044586390875254565113 5862033439793156440923835)
      ·
        refine ⟨8793050159689734661385753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862033439793156440923835 8793050159689734661385753)
        ·
          refine ⟨6594787619767300996039315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8793050159689734661385753 6594787619767300996039315)
          ·
            refine ⟨9892181429650951494058973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594787619767300996039315 9892181429650951494058973)
            ·
              refine ⟨3709568036119106810272115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9892181429650951494058973 3709568036119106810272115)
              ·
                refine ⟨5564352054178660215408173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709568036119106810272115 5564352054178660215408173)
                ·
                  refine ⟨2086632020316997580778065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5564352054178660215408173 2086632020316997580778065)
                  ·
                    refine ⟨1564974015237748185583549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2086632020316997580778065 1564974015237748185583549)
                    ·
                      refine ⟨586865255714155569593831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564974015237748185583549 586865255714155569593831)
                      ·
                        rfl

theorem cell23_1142916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1142916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142916 prefixEnd_1142916 := by exact prefixLift 1142916
  have htrace : WordTrace (prefixWord ++ tailWord_1142916) baseStart_1142916 baseEnd_1142916 := by
    simpa [prefixWord, tailWord_1142916, baseEnd_1142916] using wordTrace_append hprefix tailTrace_1142916
  have hstable : (prefixWord ++ tailWord_1142916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142916).length < 2 ^ (prefixWord ++ tailWord_1142916).sum := by decide
  have hdescent : baseEnd_1142916 < baseStart_1142916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142933 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_1142933 : Nat := 118140960795 + 1142933 * 2 ^ 59
def prefixEnd_1142933 : Nat := 4983230072969 + 3 ^ 40 * 1142933 * 2
def baseEnd_1142933 : Nat := 586873984885282003081253

theorem tailTrace_1142933 : CollatzResearch.WordTrace tailWord_1142933 prefixEnd_1142933 586873984885282003081253 := by
  unfold tailWord_1142933
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686191168356413261049453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27790794112237608840699635 41686191168356413261049453)
  ·
    refine ⟨15632321688133654972893545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41686191168356413261049453 15632321688133654972893545)
    ·
      refine ⟨11724241266100241229670159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15632321688133654972893545 11724241266100241229670159)
      ·
        refine ⟨17586361899150361844505239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11724241266100241229670159 17586361899150361844505239)
        ·
          refine ⟨26379542848725542766757859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17586361899150361844505239 26379542848725542766757859)
          ·
            refine ⟨39569314273088314150136789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26379542848725542766757859 39569314273088314150136789)
            ·
              refine ⟨927405803275507362893831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39569314273088314150136789 927405803275507362893831)
              ·
                refine ⟨1391108704913261044340747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927405803275507362893831 1391108704913261044340747)
                ·
                  refine ⟨2086663057369891566511121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391108704913261044340747 2086663057369891566511121)
                  ·
                    refine ⟨1564997293027418674883341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2086663057369891566511121 1564997293027418674883341)
                    ·
                      refine ⟨586873984885282003081253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1564997293027418674883341 586873984885282003081253)
                      ·
                        rfl

theorem cell23_1142933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_1142933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142933 prefixEnd_1142933 := by exact prefixLift 1142933
  have htrace : WordTrace (prefixWord ++ tailWord_1142933) baseStart_1142933 baseEnd_1142933 := by
    simpa [prefixWord, tailWord_1142933, baseEnd_1142933] using wordTrace_append hprefix tailTrace_1142933
  have hstable : (prefixWord ++ tailWord_1142933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142933).length < 2 ^ (prefixWord ++ tailWord_1142933).sum := by decide
  have hdescent : baseEnd_1142933 < baseStart_1142933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142969 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1142969 : Nat := 118140960795 + 1142969 * 2 ^ 59
def prefixEnd_1142969 : Nat := 4983230072969 + 3 ^ 40 * 1142969 * 2
def baseEnd_1142969 : Nat := 586892470188843862231087

theorem tailTrace_1142969 : CollatzResearch.WordTrace tailWord_1142969 prefixEnd_1142969 586892470188843862231087 := by
  unfold tailWord_1142969
  simp only [CollatzResearch.WordTrace]
  refine ⟨41687504196225991409359961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27791669464150660939573307 41687504196225991409359961)
  ·
    refine ⟨31265628147169493557019971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41687504196225991409359961 31265628147169493557019971)
    ·
      refine ⟨46898442220754240335529957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31265628147169493557019971 46898442220754240335529957)
      ·
        refine ⟨8793457916391420062911867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46898442220754240335529957 8793457916391420062911867)
        ·
          refine ⟨13190186874587130094367801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8793457916391420062911867 13190186874587130094367801)
          ·
            refine ⟨9892640155940347570775851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13190186874587130094367801 9892640155940347570775851)
            ·
              refine ⟨14838960233910521356163777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892640155940347570775851 14838960233910521356163777)
              ·
                refine ⟨11129220175432891017122833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14838960233910521356163777 11129220175432891017122833)
                ·
                  refine ⟨8346915131574668262842125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11129220175432891017122833 8346915131574668262842125)
                  ·
                    refine ⟨3130093174340500598565797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8346915131574668262842125 3130093174340500598565797)
                    ·
                      refine ⟨586892470188843862231087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3130093174340500598565797 586892470188843862231087)
                      ·
                        rfl

theorem cell23_1142969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1142969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142969 prefixEnd_1142969 := by exact prefixLift 1142969
  have htrace : WordTrace (prefixWord ++ tailWord_1142969) baseStart_1142969 baseEnd_1142969 := by
    simpa [prefixWord, tailWord_1142969, baseEnd_1142969] using wordTrace_append hprefix tailTrace_1142969
  have hstable : (prefixWord ++ tailWord_1142969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142969).length < 2 ^ (prefixWord ++ tailWord_1142969).sum := by decide
  have hdescent : baseEnd_1142969 < baseStart_1142969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142973 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 1, 3, 2]
def baseStart_1142973 : Nat := 118140960795 + 1142973 * 2 ^ 59
def prefixEnd_1142973 : Nat := 4983230072969 + 3 ^ 40 * 1142973 * 2
def baseEnd_1142973 : Nat := 586894524111461846581069

theorem tailTrace_1142973 : CollatzResearch.WordTrace tailWord_1142973 prefixEnd_1142973 586894524111461846581069 := by
  unfold tailWord_1142973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41687650088211500092505573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27791766725474333395003715 41687650088211500092505573)
  ·
    refine ⟨7816434391539656267344795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41687650088211500092505573 7816434391539656267344795)
    ·
      refine ⟨11724651587309484401017193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816434391539656267344795 11724651587309484401017193)
      ·
        refine ⟨8793488690482113300762895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11724651587309484401017193 8793488690482113300762895)
        ·
          refine ⟨13190233035723169951144343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8793488690482113300762895 13190233035723169951144343)
          ·
            refine ⟨19785349553584754926716515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13190233035723169951144343 19785349553584754926716515)
            ·
              refine ⟨29678024330377132390074773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19785349553584754926716515 29678024330377132390074773)
              ·
                refine ⟨1391157390486428080784755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29678024330377132390074773 1391157390486428080784755)
                ·
                  refine ⟨2086736085729642121177133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391157390486428080784755 2086736085729642121177133)
                  ·
                    refine ⟨782526032148615795441425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086736085729642121177133 782526032148615795441425)
                    ·
                      refine ⟨586894524111461846581069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782526032148615795441425 586894524111461846581069)
                      ·
                        rfl

theorem cell23_1142973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_1142973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142973 prefixEnd_1142973 := by exact prefixLift 1142973
  have htrace : WordTrace (prefixWord ++ tailWord_1142973) baseStart_1142973 baseEnd_1142973 := by
    simpa [prefixWord, tailWord_1142973, baseEnd_1142973] using wordTrace_append hprefix tailTrace_1142973
  have hstable : (prefixWord ++ tailWord_1142973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142973).length < 2 ^ (prefixWord ++ tailWord_1142973).sum := by decide
  have hdescent : baseEnd_1142973 < baseStart_1142973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142990 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2]
def baseStart_1142990 : Nat := 118140960795 + 1142990 * 2 ^ 59
def prefixEnd_1142990 : Nat := 4983230072969 + 3 ^ 40 * 1142990 * 2
def baseEnd_1142990 : Nat := 586903253282588280068491

theorem tailTrace_1142990 : CollatzResearch.WordTrace tailWord_1142990 prefixEnd_1142990 586903253282588280068491 := by
  unfold tailWord_1142990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211033766143738999484303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27792180086099941330582949 5211033766143738999484303)
  ·
    refine ⟨7816550649215608499226455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211033766143738999484303 7816550649215608499226455)
    ·
      refine ⟨11724825973823412748839683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816550649215608499226455 11724825973823412748839683)
      ·
        refine ⟨17587238960735119123259525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11724825973823412748839683 17587238960735119123259525)
        ·
          refine ⟨3297607305137834835611161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17587238960735119123259525 3297607305137834835611161)
          ·
            refine ⟨2473205478853376126708371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297607305137834835611161 2473205478853376126708371)
            ·
              refine ⟨3709808218280064190062557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473205478853376126708371 3709808218280064190062557)
              ·
                refine ⟨1391178081855024071273459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3709808218280064190062557 1391178081855024071273459)
                ·
                  refine ⟨2086767122782536106910189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391178081855024071273459 2086767122782536106910189)
                  ·
                    refine ⟨782537671043451040091321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086767122782536106910189 782537671043451040091321)
                    ·
                      refine ⟨586903253282588280068491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782537671043451040091321 586903253282588280068491)
                      ·
                        rfl

theorem cell23_1142990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2].length) (baseStart_1142990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142990 prefixEnd_1142990 := by exact prefixLift 1142990
  have htrace : WordTrace (prefixWord ++ tailWord_1142990) baseStart_1142990 baseEnd_1142990 := by
    simpa [prefixWord, tailWord_1142990, baseEnd_1142990] using wordTrace_append hprefix tailTrace_1142990
  have hstable : (prefixWord ++ tailWord_1142990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142990).length < 2 ^ (prefixWord ++ tailWord_1142990).sum := by decide
  have hdescent : baseEnd_1142990 < baseStart_1142990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1142997 : List Nat := [1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1142997 : Nat := 118140960795 + 1142997 * 2 ^ 59
def prefixEnd_1142997 : Nat := 4983230072969 + 3 ^ 40 * 1142997 * 2
def baseEnd_1142997 : Nat := 586906847647169752680959

theorem tailTrace_1142997 : CollatzResearch.WordTrace tailWord_1142997 prefixEnd_1142997 586906847647169752680959 := by
  unfold tailWord_1142997
  simp only [CollatzResearch.WordTrace]
  refine ⟨41688525440124552191379245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27792350293416368127586163 41688525440124552191379245)
  ·
    refine ⟨15633197040046707071767217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41688525440124552191379245 15633197040046707071767217)
    ·
      refine ⟨11724897780035030303825413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15633197040046707071767217 11724897780035030303825413)
      ·
        refine ⟨2198418333756568181967265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11724897780035030303825413 2198418333756568181967265)
        ·
          refine ⟨1648813750317426136475449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198418333756568181967265 1648813750317426136475449)
          ·
            refine ⟨1236610312738069602356587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1648813750317426136475449 1236610312738069602356587)
            ·
              refine ⟨1854915469107104403534881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1236610312738069602356587 1854915469107104403534881)
              ·
                refine ⟨1391186601830328302651161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854915469107104403534881 1391186601830328302651161)
                ·
                  refine ⟨1043389951372746226988371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1391186601830328302651161 1043389951372746226988371)
                  ·
                    refine ⟨1565084927059119340482557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1043389951372746226988371 1565084927059119340482557)
                    ·
                      refine ⟨586906847647169752680959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1565084927059119340482557 586906847647169752680959)
                      ·
                        rfl

theorem cell23_1142997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1142997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1142997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1142997 prefixEnd_1142997 := by exact prefixLift 1142997
  have htrace : WordTrace (prefixWord ++ tailWord_1142997) baseStart_1142997 baseEnd_1142997 := by
    simpa [prefixWord, tailWord_1142997, baseEnd_1142997] using wordTrace_append hprefix tailTrace_1142997
  have hstable : (prefixWord ++ tailWord_1142997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1142997).length < 2 ^ (prefixWord ++ tailWord_1142997).sum := by decide
  have hdescent : baseEnd_1142997 < baseStart_1142997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1142997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143016 : List Nat := [2, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1143016 : Nat := 118140960795 + 1143016 * 2 ^ 59
def prefixEnd_1143016 : Nat := 4983230072969 + 3 ^ 40 * 1143016 * 2
def baseEnd_1143016 : Nat := 586916603779605178343371

theorem tailTrace_1143016 : CollatzResearch.WordTrace tailWord_1143016 prefixEnd_1143016 586916603779605178343371 := by
  unfold tailWord_1143016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20844609213527859218160451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27792812284703812290880601 20844609213527859218160451)
  ·
    refine ⟨31266913820291788827240677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20844609213527859218160451 31266913820291788827240677)
    ·
      refine ⟨5862546341304710405107627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31266913820291788827240677 5862546341304710405107627)
      ·
        refine ⟨8793819511957065607661441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862546341304710405107627 8793819511957065607661441)
        ·
          refine ⟨6595364633967799205746081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8793819511957065607661441 6595364633967799205746081)
          ·
            refine ⟨4946523475475849404309561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6595364633967799205746081 4946523475475849404309561)
            ·
              refine ⟨3709892606606887053232171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4946523475475849404309561 3709892606606887053232171)
              ·
                refine ⟨5564838909910330579848257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709892606606887053232171 5564838909910330579848257)
                ·
                  refine ⟨4173629182432747934886193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5564838909910330579848257 4173629182432747934886193)
                  ·
                    refine ⟨3130221886824560951164645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4173629182432747934886193 3130221886824560951164645)
                    ·
                      refine ⟨586916603779605178343371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3130221886824560951164645 586916603779605178343371)
                      ·
                        rfl

theorem cell23_1143016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1143016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143016 prefixEnd_1143016 := by exact prefixLift 1143016
  have htrace : WordTrace (prefixWord ++ tailWord_1143016) baseStart_1143016 baseEnd_1143016 := by
    simpa [prefixWord, tailWord_1143016, baseEnd_1143016] using wordTrace_append hprefix tailTrace_1143016
  have hstable : (prefixWord ++ tailWord_1143016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143016).length < 2 ^ (prefixWord ++ tailWord_1143016).sum := by decide
  have hdescent : baseEnd_1143016 < baseStart_1143016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143026 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_1143026 : Nat := 118140960795 + 1143026 * 2 ^ 59
def prefixEnd_1143026 : Nat := 4983230072969 + 3 ^ 40 * 1143026 * 2
def baseEnd_1143026 : Nat := 65213526509572237690925

theorem tailTrace_1143026 : CollatzResearch.WordTrace tailWord_1143026 prefixEnd_1143026 65213526509572237690925 := by
  unfold tailWord_1143026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10422395789254872536046233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27793055438012993429456621 10422395789254872536046233)
  ·
    refine ⟨7816796841941154402034675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10422395789254872536046233 7816796841941154402034675)
    ·
      refine ⟨11725195262911731603052013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816796841941154402034675 11725195262911731603052013)
      ·
        refine ⟨4396948223591899351144505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11725195262911731603052013 4396948223591899351144505)
        ·
          refine ⟨3297711167693924513358379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4396948223591899351144505 3297711167693924513358379)
          ·
            refine ⟨4946566751540886770037569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297711167693924513358379 4946566751540886770037569)
            ·
              refine ⟨3709925063655665077528177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4946566751540886770037569 3709925063655665077528177)
              ·
                refine ⟨2782443797741748808146133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3709925063655665077528177 2782443797741748808146133)
                ·
                  refine ⟨65213526509572237690925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2782443797741748808146133 65213526509572237690925)
                  ·
                    rfl

theorem cell23_1143026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_1143026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143026 prefixEnd_1143026 := by exact prefixLift 1143026
  have htrace : WordTrace (prefixWord ++ tailWord_1143026) baseStart_1143026 baseEnd_1143026 := by
    simpa [prefixWord, tailWord_1143026, baseEnd_1143026] using wordTrace_append hprefix tailTrace_1143026
  have hstable : (prefixWord ++ tailWord_1143026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143026).length < 2 ^ (prefixWord ++ tailWord_1143026).sum := by decide
  have hdescent : baseEnd_1143026 < baseStart_1143026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143039 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 7]
def baseStart_1143039 : Nat := 118140960795 + 1143039 * 2 ^ 59
def prefixEnd_1143039 : Nat := 4983230072969 + 3 ^ 40 * 1143039 * 2
def baseEnd_1143039 : Nat := 195642804611552862785255

theorem tailTrace_1143039 : CollatzResearch.WordTrace tailWord_1143039 prefixEnd_1143039 195642804611552862785255 := by
  unfold tailWord_1143039
  simp only [CollatzResearch.WordTrace]
  refine ⟨41690057305972393364408171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27793371537314928909605447 41690057305972393364408171)
  ·
    refine ⟨62535085958958590046612257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41690057305972393364408171 62535085958958590046612257)
    ·
      refine ⟨46901314469218942534959193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62535085958958590046612257 46901314469218942534959193)
      ·
        refine ⟨35175985851914206901219395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46901314469218942534959193 35175985851914206901219395)
        ·
          refine ⟨52763978777871310351829093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35175985851914206901219395 52763978777871310351829093)
          ·
            refine ⟨9893246020850870690967955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52763978777871310351829093 9893246020850870690967955)
            ·
              refine ⟨14839869031276306036451933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9893246020850870690967955 14839869031276306036451933)
              ·
                refine ⟨5564950886728614763669475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14839869031276306036451933 5564950886728614763669475)
                ·
                  refine ⟨8347426330092922145504213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564950886728614763669475 8347426330092922145504213)
                  ·
                    refine ⟨195642804611552862785255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8347426330092922145504213 195642804611552862785255)
                    ·
                      rfl

theorem cell23_1143039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_1143039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143039 prefixEnd_1143039 := by exact prefixLift 1143039
  have htrace : WordTrace (prefixWord ++ tailWord_1143039) baseStart_1143039 baseEnd_1143039 := by
    simpa [prefixWord, tailWord_1143039, baseEnd_1143039] using wordTrace_append hprefix tailTrace_1143039
  have hstable : (prefixWord ++ tailWord_1143039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143039).length < 2 ^ (prefixWord ++ tailWord_1143039).sum := by decide
  have hdescent : baseEnd_1143039 < baseStart_1143039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143093 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_1143093 : Nat := 118140960795 + 1143093 * 2 ^ 59
def prefixEnd_1143093 : Nat := 4983230072969 + 3 ^ 40 * 1143093 * 2
def baseEnd_1143093 : Nat := 586956141790001377080517

theorem tailTrace_1143093 : CollatzResearch.WordTrace tailWord_1143093 prefixEnd_1143093 586956141790001377080517 := by
  unfold tailWord_1143093
  simp only [CollatzResearch.WordTrace]
  refine ⟨41692026847776760586873933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27794684565184507057915955 41692026847776760586873933)
  ·
    refine ⟨15634510067916285220077725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41692026847776760586873933 15634510067916285220077725)
    ·
      refine ⟨5862941275468606957529147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15634510067916285220077725 5862941275468606957529147)
      ·
        refine ⟨8794411913202910436293721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862941275468606957529147 8794411913202910436293721)
        ·
          refine ⟨6595808934902182827220291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8794411913202910436293721 6595808934902182827220291)
          ·
            refine ⟨9893713402353274240830437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595808934902182827220291 9893713402353274240830437)
            ·
              refine ⟨1855071262941238920155707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9893713402353274240830437 1855071262941238920155707)
              ·
                refine ⟨2782606894411858380233561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855071262941238920155707 2782606894411858380233561)
                ·
                  refine ⟨2086955170808893785175171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2782606894411858380233561 2086955170808893785175171)
                  ·
                    refine ⟨3130432756213340677762757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2086955170808893785175171 3130432756213340677762757)
                    ·
                      refine ⟨586956141790001377080517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3130432756213340677762757 586956141790001377080517)
                      ·
                        rfl

theorem cell23_1143093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_1143093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143093 prefixEnd_1143093 := by exact prefixLift 1143093
  have htrace : WordTrace (prefixWord ++ tailWord_1143093) baseStart_1143093 baseEnd_1143093 := by
    simpa [prefixWord, tailWord_1143093, baseEnd_1143093] using wordTrace_append hprefix tailTrace_1143093
  have hstable : (prefixWord ++ tailWord_1143093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143093).length < 2 ^ (prefixWord ++ tailWord_1143093).sum := by decide
  have hdescent : baseEnd_1143093 < baseStart_1143093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143096 : List Nat := [2, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3]
def baseStart_1143096 : Nat := 118140960795 + 1143096 * 2 ^ 59
def prefixEnd_1143096 : Nat := 4983230072969 + 3 ^ 40 * 1143096 * 2
def baseEnd_1143096 : Nat := 586957682231964865343003

theorem tailTrace_1143096 : CollatzResearch.WordTrace tailWord_1143096 prefixEnd_1143096 586957682231964865343003 := by
  unfold tailWord_1143096
  simp only [CollatzResearch.WordTrace]
  refine ⟨20846068133382946049616571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27794757511177261399488761 20846068133382946049616571)
  ·
    refine ⟨31269102200074419074424857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20846068133382946049616571 31269102200074419074424857)
    ·
      refine ⟨23451826650055814305818643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31269102200074419074424857 23451826650055814305818643)
      ·
        refine ⟨35177739975083721458727965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23451826650055814305818643 35177739975083721458727965)
        ·
          refine ⟨13191652490656395547022987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35177739975083721458727965 13191652490656395547022987)
          ·
            refine ⟨19787478735984593320534481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13191652490656395547022987 19787478735984593320534481)
            ·
              refine ⟨14840609051988444990400861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19787478735984593320534481 14840609051988444990400861)
              ·
                refine ⟨5565228394495666871400323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14840609051988444990400861 5565228394495666871400323)
                ·
                  refine ⟨8347842591743500307100485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565228394495666871400323 8347842591743500307100485)
                  ·
                    refine ⟨1565220485951906307581341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8347842591743500307100485 1565220485951906307581341)
                    ·
                      refine ⟨586957682231964865343003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1565220485951906307581341 586957682231964865343003)
                      ·
                        rfl

theorem cell23_1143096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_1143096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143096 prefixEnd_1143096 := by exact prefixLift 1143096
  have htrace : WordTrace (prefixWord ++ tailWord_1143096) baseStart_1143096 baseEnd_1143096 := by
    simpa [prefixWord, tailWord_1143096, baseEnd_1143096] using wordTrace_append hprefix tailTrace_1143096
  have hstable : (prefixWord ++ tailWord_1143096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143096).length < 2 ^ (prefixWord ++ tailWord_1143096).sum := by decide
  have hdescent : baseEnd_1143096 < baseStart_1143096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143120 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 1, 4]
def baseStart_1143120 : Nat := 118140960795 + 1143120 * 2 ^ 59
def prefixEnd_1143120 : Nat := 4983230072969 + 3 ^ 40 * 1143120 * 2
def baseEnd_1143120 : Nat := 195656668589224257147631

theorem tailTrace_1143120 : CollatzResearch.WordTrace tailWord_1143120 prefixEnd_1143120 195656668589224257147631 := by
  unfold tailWord_1143120
  simp only [CollatzResearch.WordTrace]
  refine ⟨20846505809339472099053407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27795341079119296132071209 20846505809339472099053407)
  ·
    refine ⟨31269758714009208148580111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20846505809339472099053407 31269758714009208148580111)
    ·
      refine ⟨46904638071013812222870167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31269758714009208148580111 46904638071013812222870167)
      ·
        refine ⟨70356957106520718334305251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46904638071013812222870167 70356957106520718334305251)
        ·
          refine ⟨105535435659781077501457877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70356957106520718334305251 105535435659781077501457877)
          ·
            refine ⟨2473486773276119003940419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 105535435659781077501457877 2473486773276119003940419)
            ·
              refine ⟨3710230159914178505910629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473486773276119003940419 3710230159914178505910629)
              ·
                refine ⟨695668154983908469858243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3710230159914178505910629 695668154983908469858243)
                ·
                  refine ⟨1043502232475862704787365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695668154983908469858243 1043502232475862704787365)
                  ·
                    refine ⟨195656668589224257147631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043502232475862704787365 195656668589224257147631)
                    ·
                      rfl

theorem cell23_1143120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 4].length) (baseStart_1143120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143120 prefixEnd_1143120 := by exact prefixLift 1143120
  have htrace : WordTrace (prefixWord ++ tailWord_1143120) baseStart_1143120 baseEnd_1143120 := by
    simpa [prefixWord, tailWord_1143120, baseEnd_1143120] using wordTrace_append hprefix tailTrace_1143120
  have hstable : (prefixWord ++ tailWord_1143120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143120).length < 2 ^ (prefixWord ++ tailWord_1143120).sum := by decide
  have hdescent : baseEnd_1143120 < baseStart_1143120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143163 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 1, 5]
def baseStart_1143163 : Nat := 118140960795 + 1143163 * 2 ^ 59
def prefixEnd_1143163 : Nat := 4983230072969 + 3 ^ 40 * 1143163 * 2
def baseEnd_1143163 : Nat := 195664028478605367735065

theorem tailTrace_1143163 : CollatzResearch.WordTrace tailWord_1143163 prefixEnd_1143163 195664028478605367735065 := by
  unfold tailWord_1143163
  simp only [CollatzResearch.WordTrace]
  refine ⟨41694579957523162541922143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27796386638348775027948095 41694579957523162541922143)
  ·
    refine ⟨62541869936284743812883215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41694579957523162541922143 62541869936284743812883215)
    ·
      refine ⟨93812804904427115719324823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62541869936284743812883215 93812804904427115719324823)
      ·
        refine ⟨140719207356640673578987235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93812804904427115719324823 140719207356640673578987235)
        ·
          refine ⟨211078811034961010368480853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140719207356640673578987235 211078811034961010368480853)
          ·
            refine ⟨2473579816815949340255635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 211078811034961010368480853 2473579816815949340255635)
            ·
              refine ⟨3710369725223924010383453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473579816815949340255635 3710369725223924010383453)
              ·
                refine ⟨1391388646958971503893795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3710369725223924010383453 1391388646958971503893795)
                ·
                  refine ⟨2087082970438457255840693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391388646958971503893795 2087082970438457255840693)
                  ·
                    refine ⟨195664028478605367735065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2087082970438457255840693 195664028478605367735065)
                    ·
                      rfl

theorem cell23_1143163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 5].length) (baseStart_1143163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143163 prefixEnd_1143163 := by exact prefixLift 1143163
  have htrace : WordTrace (prefixWord ++ tailWord_1143163) baseStart_1143163 baseEnd_1143163 := by
    simpa [prefixWord, tailWord_1143163, baseEnd_1143163] using wordTrace_append hprefix tailTrace_1143163
  have hstable : (prefixWord ++ tailWord_1143163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143163).length < 2 ^ (prefixWord ++ tailWord_1143163).sum := by decide
  have hdescent : baseEnd_1143163 < baseStart_1143163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143177 : List Nat := [1, 2, 1, 1, 6, 1, 2, 4, 1, 1, 3]
def baseStart_1143177 : Nat := 118140960795 + 1143177 * 2 ^ 59
def prefixEnd_1143177 : Nat := 4983230072969 + 3 ^ 40 * 1143177 * 2
def baseEnd_1143177 : Nat := 586999274164979048430131

theorem tailTrace_1143177 : CollatzResearch.WordTrace tailWord_1143177 prefixEnd_1143177 586999274164979048430131 := by
  unfold tailWord_1143177
  simp only [CollatzResearch.WordTrace]
  refine ⟨41695090579472442932931785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27796727052981628621954523 41695090579472442932931785)
  ·
    refine ⟨31271317934604332199698839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41695090579472442932931785 31271317934604332199698839)
    ·
      refine ⟨46906976901906498299548259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31271317934604332199698839 46906976901906498299548259)
      ·
        refine ⟨70360465352859747449322389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46906976901906498299548259 70360465352859747449322389)
        ·
          refine ⟨3298146813415300661686987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70360465352859747449322389 3298146813415300661686987)
          ·
            refine ⟨4947220220122950992530481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298146813415300661686987 4947220220122950992530481)
            ·
              refine ⟨3710415165092213244397861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4947220220122950992530481 3710415165092213244397861)
              ·
                refine ⟨695702843454789983324599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3710415165092213244397861 695702843454789983324599)
                ·
                  refine ⟨1043554265182184974986899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695702843454789983324599 1043554265182184974986899)
                  ·
                    refine ⟨1565331397773277462480349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1043554265182184974986899 1565331397773277462480349)
                    ·
                      refine ⟨586999274164979048430131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1565331397773277462480349 586999274164979048430131)
                      ·
                        rfl

theorem cell23_1143177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 4, 1, 1, 3].length) (baseStart_1143177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143177 prefixEnd_1143177 := by exact prefixLift 1143177
  have htrace : WordTrace (prefixWord ++ tailWord_1143177) baseStart_1143177 baseEnd_1143177 := by
    simpa [prefixWord, tailWord_1143177, baseEnd_1143177] using wordTrace_append hprefix tailTrace_1143177
  have hstable : (prefixWord ++ tailWord_1143177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143177).length < 2 ^ (prefixWord ++ tailWord_1143177).sum := by decide
  have hdescent : baseEnd_1143177 < baseStart_1143177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143200 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4]
def baseStart_1143200 : Nat := 118140960795 + 1143200 * 2 ^ 59
def prefixEnd_1143200 : Nat := 4983230072969 + 3 ^ 40 * 1143200 * 2
def baseEnd_1143200 : Nat := 587011084220032458442525

theorem tailTrace_1143200 : CollatzResearch.WordTrace tailWord_1143200 prefixEnd_1143200 587011084220032458442525 := by
  unfold tailWord_1143200
  simp only [CollatzResearch.WordTrace]
  refine ⟨20847964729194558930509527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27797286305592745240679369 20847964729194558930509527)
  ·
    refine ⟨31271947093791838395764291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20847964729194558930509527 31271947093791838395764291)
    ·
      refine ⟨46907920640687757593646437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31271947093791838395764291 46907920640687757593646437)
      ·
        refine ⟨8795235120128954548808707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46907920640687757593646437 8795235120128954548808707)
        ·
          refine ⟨13192852680193431823213061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8795235120128954548808707 13192852680193431823213061)
          ·
            refine ⟨2473659877536268466852449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13192852680193431823213061 2473659877536268466852449)
            ·
              refine ⟨1855244908152201350139337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473659877536268466852449 1855244908152201350139337)
              ·
                refine ⟨1391433681114151012604503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855244908152201350139337 1391433681114151012604503)
                ·
                  refine ⟨2087150521671226518906755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391433681114151012604503 2087150521671226518906755)
                  ·
                    refine ⟨3130725782506839778360133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2087150521671226518906755 3130725782506839778360133)
                    ·
                      refine ⟨587011084220032458442525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3130725782506839778360133 587011084220032458442525)
                      ·
                        rfl

theorem cell23_1143200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_1143200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143200 prefixEnd_1143200 := by exact prefixLift 1143200
  have htrace : WordTrace (prefixWord ++ tailWord_1143200) baseStart_1143200 baseEnd_1143200 := by
    simpa [prefixWord, tailWord_1143200, baseEnd_1143200] using wordTrace_append hprefix tailTrace_1143200
  have hstable : (prefixWord ++ tailWord_1143200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143200).length < 2 ^ (prefixWord ++ tailWord_1143200).sum := by decide
  have hdescent : baseEnd_1143200 < baseStart_1143200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143243 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 7, 2]
def baseStart_1143243 : Nat := 118140960795 + 1143243 * 2 ^ 59
def prefixEnd_1143243 : Nat := 4983230072969 + 3 ^ 40 * 1143243 * 2
def baseEnd_1143243 : Nat := 587033163888175790204827

theorem tailTrace_1143243 : CollatzResearch.WordTrace tailWord_1143243 prefixEnd_1143243 587033163888175790204827 := by
  unfold tailWord_1143243
  simp only [CollatzResearch.WordTrace]
  refine ⟨41697497797233336204834383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27798331864822224136556255 41697497797233336204834383)
  ·
    refine ⟨62546246695850004307251575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41697497797233336204834383 62546246695850004307251575)
    ·
      refine ⟨93819370043775006460877363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62546246695850004307251575 93819370043775006460877363)
      ·
        refine ⟨140729055065662509691316045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93819370043775006460877363 140729055065662509691316045)
        ·
          refine ⟨52773395649623441134243517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140729055065662509691316045 52773395649623441134243517)
          ·
            refine ⟨19790023368608790425341319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52773395649623441134243517 19790023368608790425341319)
            ·
              refine ⟨29685035052913185638011979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19790023368608790425341319 29685035052913185638011979)
              ·
                refine ⟨44527552579369778457017969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29685035052913185638011979 44527552579369778457017969)
                ·
                  refine ⟨33395664434527333842763477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44527552579369778457017969 33395664434527333842763477)
                  ·
                    refine ⟨782710885184234386939769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33395664434527333842763477 782710885184234386939769)
                    ·
                      refine ⟨587033163888175790204827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782710885184234386939769 587033163888175790204827)
                      ·
                        rfl

theorem cell23_1143243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7, 2].length) (baseStart_1143243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143243 prefixEnd_1143243 := by exact prefixLift 1143243
  have htrace : WordTrace (prefixWord ++ tailWord_1143243) baseStart_1143243 baseEnd_1143243 := by
    simpa [prefixWord, tailWord_1143243, baseEnd_1143243] using wordTrace_append hprefix tailTrace_1143243
  have hstable : (prefixWord ++ tailWord_1143243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143243).length < 2 ^ (prefixWord ++ tailWord_1143243).sum := by decide
  have hdescent : baseEnd_1143243 < baseStart_1143243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143244 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_1143244 : Nat := 118140960795 + 1143244 * 2 ^ 59
def prefixEnd_1143244 : Nat := 4983230072969 + 3 ^ 40 * 1143244 * 2
def baseEnd_1143244 : Nat := 195677892456276762097441

theorem tailTrace_1143244 : CollatzResearch.WordTrace tailWord_1143244 prefixEnd_1143244 195677892456276762097441 := by
  unfold tailWord_1143244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20848767135114856687810393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27798356180153142250413857 20848767135114856687810393)
  ·
    refine ⟨15636575351336142515857795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20848767135114856687810393 15636575351336142515857795)
    ·
      refine ⟨23454863027004213773786693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15636575351336142515857795 23454863027004213773786693)
      ·
        refine ⟨4397786817563290082585005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23454863027004213773786693 4397786817563290082585005)
        ·
          refine ⟨1649170056586233780969377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4397786817563290082585005 1649170056586233780969377)
          ·
            refine ⟨1236877542439675335727033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649170056586233780969377 1236877542439675335727033)
            ·
              refine ⟨927658156829756501795275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236877542439675335727033 927658156829756501795275)
              ·
                refine ⟨1391487235244634752692913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927658156829756501795275 1391487235244634752692913)
                ·
                  refine ⟨1043615426433476064519685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1391487235244634752692913 1043615426433476064519685)
                  ·
                    refine ⟨195677892456276762097441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043615426433476064519685 195677892456276762097441)
                    ·
                      rfl

theorem cell23_1143244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_1143244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143244 prefixEnd_1143244 := by exact prefixLift 1143244
  have htrace : WordTrace (prefixWord ++ tailWord_1143244) baseStart_1143244 baseEnd_1143244 := by
    simpa [prefixWord, tailWord_1143244, baseEnd_1143244] using wordTrace_append hprefix tailTrace_1143244
  have hstable : (prefixWord ++ tailWord_1143244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143244).length < 2 ^ (prefixWord ++ tailWord_1143244).sum := by decide
  have hdescent : baseEnd_1143244 < baseStart_1143244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143256 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8]
def baseStart_1143256 : Nat := 118140960795 + 1143256 * 2 ^ 59
def prefixEnd_1143256 : Nat := 4983230072969 + 3 ^ 40 * 1143256 * 2
def baseEnd_1143256 : Nat := 587039839136684239342267

theorem tailTrace_1143256 : CollatzResearch.WordTrace tailWord_1143256 prefixEnd_1143256 587039839136684239342267 := by
  unfold tailWord_1143256
  simp only [CollatzResearch.WordTrace]
  refine ⟨20848985973093119712528811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27798647964124159616705081 20848985973093119712528811)
  ·
    refine ⟨31273478959639679568793217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20848985973093119712528811 31273478959639679568793217)
    ·
      refine ⟨23455109219729759676594913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31273478959639679568793217 23455109219729759676594913)
      ·
        refine ⟨17591331914797319757446185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23455109219729759676594913 17591331914797319757446185)
        ·
          refine ⟨13193498936097989818084639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17591331914797319757446185 13193498936097989818084639)
          ·
            refine ⟨19790248404146984727126959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13193498936097989818084639 19790248404146984727126959)
            ·
              refine ⟨29685372606220477090690439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19790248404146984727126959 29685372606220477090690439)
              ·
                refine ⟨44528058909330715636035659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29685372606220477090690439 44528058909330715636035659)
                ·
                  refine ⟨66792088363996073454053489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44528058909330715636035659 66792088363996073454053489)
                  ·
                    refine ⟨50094066272997055090540117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66792088363996073454053489 50094066272997055090540117)
                    ·
                      refine ⟨587039839136684239342267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 50094066272997055090540117 587039839136684239342267)
                      ·
                        rfl

theorem cell23_1143256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_1143256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143256 prefixEnd_1143256 := by exact prefixLift 1143256
  have htrace : WordTrace (prefixWord ++ tailWord_1143256) baseStart_1143256 baseEnd_1143256 := by
    simpa [prefixWord, tailWord_1143256, baseEnd_1143256] using wordTrace_append hprefix tailTrace_1143256
  have hstable : (prefixWord ++ tailWord_1143256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143256).length < 2 ^ (prefixWord ++ tailWord_1143256).sum := by decide
  have hdescent : baseEnd_1143256 < baseStart_1143256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143285 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1143285 : Nat := 118140960795 + 1143285 * 2 ^ 59
def prefixEnd_1143285 : Nat := 4983230072969 + 3 ^ 40 * 1143285 * 2
def baseEnd_1143285 : Nat := 587054730075664625879635

theorem tailTrace_1143285 : CollatzResearch.WordTrace tailWord_1143285 prefixEnd_1143285 587054730075664625879635 := by
  unfold tailWord_1143285
  simp only [CollatzResearch.WordTrace]
  refine ⟨41699029663081177377863309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27799353108720784918575539 41699029663081177377863309)
  ·
    refine ⟨15637136123655441516698741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41699029663081177377863309 15637136123655441516698741)
    ·
      refine ⟨1465981511592697642190507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15637136123655441516698741 1465981511592697642190507)
      ·
        refine ⟨2198972267389046463285761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465981511592697642190507 2198972267389046463285761)
        ·
          refine ⟨1649229200541784847464321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198972267389046463285761 1649229200541784847464321)
          ·
            refine ⟨1236921900406338635598241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1649229200541784847464321 1236921900406338635598241)
            ·
              refine ⟨927691425304753976698681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236921900406338635598241 927691425304753976698681)
              ·
                refine ⟨695768568978565482524011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927691425304753976698681 695768568978565482524011)
                ·
                  refine ⟨1043652853467848223786017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695768568978565482524011 1043652853467848223786017)
                  ·
                    refine ⟨782739640100886167839513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1043652853467848223786017 782739640100886167839513)
                    ·
                      refine ⟨587054730075664625879635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782739640100886167839513 587054730075664625879635)
                      ·
                        rfl

theorem cell23_1143285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1143285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143285 prefixEnd_1143285 := by exact prefixLift 1143285
  have htrace : WordTrace (prefixWord ++ tailWord_1143285) baseStart_1143285 baseEnd_1143285 := by
    simpa [prefixWord, tailWord_1143285, baseEnd_1143285] using wordTrace_append hprefix tailTrace_1143285
  have hstable : (prefixWord ++ tailWord_1143285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143285).length < 2 ^ (prefixWord ++ tailWord_1143285).sum := by decide
  have hdescent : baseEnd_1143285 < baseStart_1143285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143293 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1143293 : Nat := 118140960795 + 1143293 * 2 ^ 59
def prefixEnd_1143293 : Nat := 4983230072969 + 3 ^ 40 * 1143293 * 2
def baseEnd_1143293 : Nat := 587058837920900594579597

theorem tailTrace_1143293 : CollatzResearch.WordTrace tailWord_1143293 prefixEnd_1143293 587058837920900594579597 := by
  unfold tailWord_1143293
  simp only [CollatzResearch.WordTrace]
  refine ⟨41699321447052194744154533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27799547631368129829436355 41699321447052194744154533)
  ·
    refine ⟨7818622771322286514528975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41699321447052194744154533 7818622771322286514528975)
    ·
      refine ⟨11727934156983429771793463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7818622771322286514528975 11727934156983429771793463)
      ·
        refine ⟨17591901235475144657690195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11727934156983429771793463 17591901235475144657690195)
        ·
          refine ⟨26387851853212716986535293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17591901235475144657690195 26387851853212716986535293)
          ·
            refine ⟨9895444444954768869950735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26387851853212716986535293 9895444444954768869950735)
            ·
              refine ⟨14843166667432153304926103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9895444444954768869950735 14843166667432153304926103)
              ·
                refine ⟨22264750001148229957389155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14843166667432153304926103 22264750001148229957389155)
                ·
                  refine ⟨33397125001722344936083733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22264750001148229957389155 33397125001722344936083733)
                  ·
                    refine ⟨1565490234455734918878925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33397125001722344936083733 1565490234455734918878925)
                    ·
                      refine ⟨587058837920900594579597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1565490234455734918878925 587058837920900594579597)
                      ·
                        rfl

theorem cell23_1143293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1143293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143293 prefixEnd_1143293 := by exact prefixLift 1143293
  have htrace : WordTrace (prefixWord ++ tailWord_1143293) baseStart_1143293 baseEnd_1143293 := by
    simpa [prefixWord, tailWord_1143293, baseEnd_1143293] using wordTrace_append hprefix tailTrace_1143293
  have hstable : (prefixWord ++ tailWord_1143293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143293).length < 2 ^ (prefixWord ++ tailWord_1143293).sum := by decide
  have hdescent : baseEnd_1143293 < baseStart_1143293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143296 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 13]
def baseStart_1143296 : Nat := 118140960795 + 1143296 * 2 ^ 59
def prefixEnd_1143296 : Nat := 4983230072969 + 3 ^ 40 * 1143296 * 2
def baseEnd_1143296 : Nat := 65228930929207120315787

theorem tailTrace_1143296 : CollatzResearch.WordTrace tailWord_1143296 prefixEnd_1143296 65228930929207120315787 := by
  unfold tailWord_1143296
  simp only [CollatzResearch.WordTrace]
  refine ⟨20849715433020663128256871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27799620577360884171009161 20849715433020663128256871)
  ·
    refine ⟨31274573149530994692385307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20849715433020663128256871 31274573149530994692385307)
    ·
      refine ⟨46911859724296492038577961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31274573149530994692385307 46911859724296492038577961)
      ·
        refine ⟨35183894793222369028933471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46911859724296492038577961 35183894793222369028933471)
        ·
          refine ⟨52775842189833553543400207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35183894793222369028933471 52775842189833553543400207)
          ·
            refine ⟨79163763284750330315100311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52775842189833553543400207 79163763284750330315100311)
            ·
              refine ⟨118745644927125495472650467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79163763284750330315100311 118745644927125495472650467)
              ·
                refine ⟨178118467390688243208975701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118745644927125495472650467 178118467390688243208975701)
                ·
                  refine ⟨65228930929207120315787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 178118467390688243208975701 65228930929207120315787)
                  ·
                    rfl

theorem cell23_1143296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_1143296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143296 prefixEnd_1143296 := by exact prefixLift 1143296
  have htrace : WordTrace (prefixWord ++ tailWord_1143296) baseStart_1143296 baseEnd_1143296 := by
    simpa [prefixWord, tailWord_1143296, baseEnd_1143296] using wordTrace_append hprefix tailTrace_1143296
  have hstable : (prefixWord ++ tailWord_1143296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143296).length < 2 ^ (prefixWord ++ tailWord_1143296).sum := by decide
  have hdescent : baseEnd_1143296 < baseStart_1143296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143300 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_1143300 : Nat := 118140960795 + 1143300 * 2 ^ 59
def prefixEnd_1143300 : Nat := 4983230072969 + 3 ^ 40 * 1143300 * 2
def baseEnd_1143300 : Nat := 195687477428494022397355

theorem tailTrace_1143300 : CollatzResearch.WordTrace tailWord_1143300 prefixEnd_1143300 195687477428494022397355 := by
  unfold tailWord_1143300
  simp only [CollatzResearch.WordTrace]
  refine ⟨20849788379013417469829677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27799717838684556626439569 20849788379013417469829677)
  ·
    refine ⟨7818670642130031551186129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20849788379013417469829677 7818670642130031551186129)
    ·
      refine ⟨5864002981597523663389597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7818670642130031551186129 5864002981597523663389597)
      ·
        refine ⟨2199001118099071373771099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5864002981597523663389597 2199001118099071373771099)
        ·
          refine ⟨3298501677148607060656649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199001118099071373771099 3298501677148607060656649)
          ·
            refine ⟨2473876257861455295492487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3298501677148607060656649 2473876257861455295492487)
            ·
              refine ⟨3710814386792182943238731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473876257861455295492487 3710814386792182943238731)
              ·
                refine ⟨5566221580188274414858097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710814386792182943238731 5566221580188274414858097)
                ·
                  refine ⟨4174666185141205811143573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5566221580188274414858097 4174666185141205811143573)
                  ·
                    refine ⟨195687477428494022397355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4174666185141205811143573 195687477428494022397355)
                    ·
                      rfl

theorem cell23_1143300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_1143300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143300 prefixEnd_1143300 := by exact prefixLift 1143300
  have htrace : WordTrace (prefixWord ++ tailWord_1143300) baseStart_1143300 baseEnd_1143300 := by
    simpa [prefixWord, tailWord_1143300, baseEnd_1143300] using wordTrace_append hprefix tailTrace_1143300
  have hstable : (prefixWord ++ tailWord_1143300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143300).length < 2 ^ (prefixWord ++ tailWord_1143300).sum := by decide
  have hdescent : baseEnd_1143300 < baseStart_1143300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143307 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 1, 4, 2]
def baseStart_1143307 : Nat := 118140960795 + 1143307 * 2 ^ 59
def prefixEnd_1143307 : Nat := 4983230072969 + 3 ^ 40 * 1143307 * 2
def baseEnd_1143307 : Nat := 587066026650063539804533

theorem tailTrace_1143307 : CollatzResearch.WordTrace tailWord_1143307 prefixEnd_1143307 587066026650063539804533 := by
  unfold tailWord_1143307
  simp only [CollatzResearch.WordTrace]
  refine ⟨41699832069001475135164175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27799888046000983423442783 41699832069001475135164175)
  ·
    refine ⟨62549748103502212702746263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41699832069001475135164175 62549748103502212702746263)
    ·
      refine ⟨93824622155253319054119395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62549748103502212702746263 93824622155253319054119395)
      ·
        refine ⟨140736933232879978581179093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93824622155253319054119395 140736933232879978581179093)
        ·
          refine ⟨3298521872645624497996385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 140736933232879978581179093 3298521872645624497996385)
          ·
            refine ⟨2473891404484218373497289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3298521872645624497996385 2473891404484218373497289)
            ·
              refine ⟨1855418553363163780122967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473891404484218373497289 1855418553363163780122967)
              ·
                refine ⟨2783127830044745670184451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855418553363163780122967 2783127830044745670184451)
                ·
                  refine ⟨4174691745067118505276677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783127830044745670184451 4174691745067118505276677)
                  ·
                    refine ⟨782754702200084719739377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4174691745067118505276677 782754702200084719739377)
                    ·
                      refine ⟨587066026650063539804533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782754702200084719739377 587066026650063539804533)
                      ·
                        rfl

theorem cell23_1143307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4, 2].length) (baseStart_1143307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143307 prefixEnd_1143307 := by exact prefixLift 1143307
  have htrace : WordTrace (prefixWord ++ tailWord_1143307) baseStart_1143307 baseEnd_1143307 := by
    simpa [prefixWord, tailWord_1143307, baseEnd_1143307] using wordTrace_append hprefix tailTrace_1143307
  have hstable : (prefixWord ++ tailWord_1143307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143307).length < 2 ^ (prefixWord ++ tailWord_1143307).sum := by decide
  have hdescent : baseEnd_1143307 < baseStart_1143307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143328 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1143328 : Nat := 118140960795 + 1143328 * 2 ^ 59
def prefixEnd_1143328 : Nat := 4983230072969 + 3 ^ 40 * 1143328 * 2
def baseEnd_1143328 : Nat := 587076809743807957641937

theorem tailTrace_1143328 : CollatzResearch.WordTrace tailWord_1143328 prefixEnd_1143328 587076809743807957641937 := by
  unfold tailWord_1143328
  simp only [CollatzResearch.WordTrace]
  refine ⟨20850299000962697860839319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27800398667950263814452425 20850299000962697860839319)
  ·
    refine ⟨31275448501444046791258979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20850299000962697860839319 31275448501444046791258979)
    ·
      refine ⟨46913172752166070186888469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31275448501444046791258979 46913172752166070186888469)
      ·
        refine ⟨2199054972757784540010397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46913172752166070186888469 2199054972757784540010397)
        ·
          refine ⟨824645614784169202503899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2199054972757784540010397 824645614784169202503899)
          ·
            refine ⟨1236968422176253803755849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824645614784169202503899 1236968422176253803755849)
            ·
              refine ⟨927726316632190352816887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1236968422176253803755849 927726316632190352816887)
              ·
                refine ⟨1391589474948285529225331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 927726316632190352816887 1391589474948285529225331)
                ·
                  refine ⟨2087384212422428293837997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391589474948285529225331 2087384212422428293837997)
                  ·
                    refine ⟨782769079658410610189249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087384212422428293837997 782769079658410610189249)
                    ·
                      refine ⟨587076809743807957641937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782769079658410610189249 587076809743807957641937)
                      ·
                        rfl

theorem cell23_1143328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1143328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143328 prefixEnd_1143328 := by exact prefixLift 1143328
  have htrace : WordTrace (prefixWord ++ tailWord_1143328) baseStart_1143328 baseEnd_1143328 := by
    simpa [prefixWord, tailWord_1143328, baseEnd_1143328] using wordTrace_append hprefix tailTrace_1143328
  have hstable : (prefixWord ++ tailWord_1143328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143328).length < 2 ^ (prefixWord ++ tailWord_1143328).sum := by decide
  have hdescent : baseEnd_1143328 < baseStart_1143328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143353 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1143353 : Nat := 118140960795 + 1143353 * 2 ^ 59
def prefixEnd_1143353 : Nat := 4983230072969 + 3 ^ 40 * 1143353 * 2
def baseEnd_1143353 : Nat := 587089646760170359829321

theorem tailTrace_1143353 : CollatzResearch.WordTrace tailWord_1143353 prefixEnd_1143353 587089646760170359829321 := by
  unfold tailWord_1143353
  simp only [CollatzResearch.WordTrace]
  refine ⟨41701509826834824991338713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27801006551223216660892475 41701509826834824991338713)
  ·
    refine ⟨31276132370126118743504035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41701509826834824991338713 31276132370126118743504035)
    ·
      refine ⟨46914198555189178115256053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31276132370126118743504035 46914198555189178115256053)
      ·
        refine ⟨4398206114548985448305255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46914198555189178115256053 4398206114548985448305255)
        ·
          refine ⟨6597309171823478172457883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398206114548985448305255 6597309171823478172457883)
          ·
            refine ⟨9895963757735217258686825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597309171823478172457883 9895963757735217258686825)
            ·
              refine ⟨7421972818301412944015119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9895963757735217258686825 7421972818301412944015119)
              ·
                refine ⟨11132959227452119416022679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7421972818301412944015119 11132959227452119416022679)
                ·
                  refine ⟨16699438841178179124034019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11132959227452119416022679 16699438841178179124034019)
                  ·
                    refine ⟨25049158261767268686051029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16699438841178179124034019 25049158261767268686051029)
                    ·
                      refine ⟨587089646760170359829321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25049158261767268686051029 587089646760170359829321)
                      ·
                        rfl

theorem cell23_1143353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1143353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143353 prefixEnd_1143353 := by exact prefixLift 1143353
  have htrace : WordTrace (prefixWord ++ tailWord_1143353) baseStart_1143353 baseEnd_1143353 := by
    simpa [prefixWord, tailWord_1143353, baseEnd_1143353] using wordTrace_append hprefix tailTrace_1143353
  have hstable : (prefixWord ++ tailWord_1143353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143353).length < 2 ^ (prefixWord ++ tailWord_1143353).sum := by decide
  have hdescent : baseEnd_1143353 < baseStart_1143353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143358 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1143358 : Nat := 118140960795 + 1143358 * 2 ^ 59
def prefixEnd_1143358 : Nat := 4983230072969 + 3 ^ 40 * 1143358 * 2
def baseEnd_1143358 : Nat := 587092214163442840266799

theorem tailTrace_1143358 : CollatzResearch.WordTrace tailWord_1143358 prefixEnd_1143358 587092214163442840266799 := by
  unfold tailWord_1143358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5212711523977088855658841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27801128127877807230180485 5212711523977088855658841)
  ·
    refine ⟨3909533642982816641744131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5212711523977088855658841 3909533642982816641744131)
    ·
      refine ⟨5864300464474224962616197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909533642982816641744131 5864300464474224962616197)
      ·
        refine ⟨1099556337088917180490537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5864300464474224962616197 1099556337088917180490537)
        ·
          refine ⟨824667252816687885367903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1099556337088917180490537 824667252816687885367903)
          ·
            refine ⟨1237000879225031828051855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 824667252816687885367903 1237000879225031828051855)
            ·
              refine ⟨1855501318837547742077783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237000879225031828051855 1855501318837547742077783)
              ·
                refine ⟨2783251978256321613116675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855501318837547742077783 2783251978256321613116675)
                ·
                  refine ⟨4174877967384482419675013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783251978256321613116675 4174877967384482419675013)
                  ·
                    refine ⟨782789618884590453689065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4174877967384482419675013 782789618884590453689065)
                    ·
                      refine ⟨587092214163442840266799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782789618884590453689065 587092214163442840266799)
                      ·
                        rfl

theorem cell23_1143358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1143358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143358 prefixEnd_1143358 := by exact prefixLift 1143358
  have htrace : WordTrace (prefixWord ++ tailWord_1143358) baseStart_1143358 baseEnd_1143358 := by
    simpa [prefixWord, tailWord_1143358, baseEnd_1143358] using wordTrace_append hprefix tailTrace_1143358
  have hstable : (prefixWord ++ tailWord_1143358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143358).length < 2 ^ (prefixWord ++ tailWord_1143358).sum := by decide
  have hdescent : baseEnd_1143358 < baseStart_1143358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143380 : List Nat := [2, 4, 1, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1143380 : Nat := 118140960795 + 1143380 * 2 ^ 59
def prefixEnd_1143380 : Nat := 4983230072969 + 3 ^ 40 * 1143380 * 2
def baseEnd_1143380 : Nat := 587103510737841754191697

theorem tailTrace_1143380 : CollatzResearch.WordTrace tailWord_1143380 prefixEnd_1143380 587103510737841754191697 := by
  unfold tailWord_1143380
  simp only [CollatzResearch.WordTrace]
  refine ⟨20851247298868504301285797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27801663065158005735047729 20851247298868504301285797)
  ·
    refine ⟨3909608868537844556491087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20851247298868504301285797 3909608868537844556491087)
    ·
      refine ⟨5864413302806766834736631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909608868537844556491087 5864413302806766834736631)
      ·
        refine ⟨8796619954210150252104947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5864413302806766834736631 8796619954210150252104947)
        ·
          refine ⟨13194929931315225378157421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796619954210150252104947 13194929931315225378157421)
          ·
            refine ⟨4948098724243209516809033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13194929931315225378157421 4948098724243209516809033)
            ·
              refine ⟨3711074043182407137606775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4948098724243209516809033 3711074043182407137606775)
              ·
                refine ⟨5566611064773610706410163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3711074043182407137606775 5566611064773610706410163)
                ·
                  refine ⟨8349916597160416059615245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5566611064773610706410163 8349916597160416059615245)
                  ·
                    refine ⟨3131218723935156022355717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8349916597160416059615245 3131218723935156022355717)
                    ·
                      refine ⟨587103510737841754191697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3131218723935156022355717 587103510737841754191697)
                      ·
                        rfl

theorem cell23_1143380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1143380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143380 prefixEnd_1143380 := by exact prefixLift 1143380
  have htrace : WordTrace (prefixWord ++ tailWord_1143380) baseStart_1143380 baseEnd_1143380 := by
    simpa [prefixWord, tailWord_1143380, baseEnd_1143380] using wordTrace_append hprefix tailTrace_1143380
  have hstable : (prefixWord ++ tailWord_1143380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143380).length < 2 ^ (prefixWord ++ tailWord_1143380).sum := by decide
  have hdescent : baseEnd_1143380 < baseStart_1143380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143394 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 2, 5]
def baseStart_1143394 : Nat := 118140960795 + 1143394 * 2 ^ 59
def prefixEnd_1143394 : Nat := 4983230072969 + 3 ^ 40 * 1143394 * 2
def baseEnd_1143394 : Nat := 195703566489001566472211

theorem tailTrace_1143394 : CollatzResearch.WordTrace tailWord_1143394 prefixEnd_1143394 195703566489001566472211 := by
  unfold tailWord_1143394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10425751304921572248395309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27802003479790859329054157 10425751304921572248395309)
  ·
    refine ⟨3909656739345589593148241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10425751304921572248395309 3909656739345589593148241)
    ·
      refine ⟨2932242554509192194861181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3909656739345589593148241 2932242554509192194861181)
      ·
        refine ⟨1099590957940947073072943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2932242554509192194861181 1099590957940947073072943)
        ·
          refine ⟨1649386436911420609609415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1099590957940947073072943 1649386436911420609609415)
          ·
            refine ⟨2474079655367130914414123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649386436911420609609415 2474079655367130914414123)
            ·
              refine ⟨3711119483050696371621185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474079655367130914414123 3711119483050696371621185)
              ·
                refine ⟨2783339612288022278715889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711119483050696371621185 2783339612288022278715889)
                ·
                  refine ⟨2087504709216016709036917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783339612288022278715889 2087504709216016709036917)
                  ·
                    refine ⟨195703566489001566472211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2087504709216016709036917 195703566489001566472211)
                    ·
                      rfl

theorem cell23_1143394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_1143394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143394 prefixEnd_1143394 := by exact prefixLift 1143394
  have htrace : WordTrace (prefixWord ++ tailWord_1143394) baseStart_1143394 baseEnd_1143394 := by
    simpa [prefixWord, tailWord_1143394, baseEnd_1143394] using wordTrace_append hprefix tailTrace_1143394
  have hstable : (prefixWord ++ tailWord_1143394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143394).length < 2 ^ (prefixWord ++ tailWord_1143394).sum := by decide
  have hdescent : baseEnd_1143394 < baseStart_1143394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143397 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1143397 : Nat := 118140960795 + 1143397 * 2 ^ 59
def prefixEnd_1143397 : Nat := 4983230072969 + 3 ^ 40 * 1143397 * 2
def baseEnd_1143397 : Nat := 587112239908968187679119

theorem tailTrace_1143397 : CollatzResearch.WordTrace tailWord_1143397 prefixEnd_1143397 587112239908968187679119 := by
  unfold tailWord_1143397
  simp only [CollatzResearch.WordTrace]
  refine ⟨41703114638675420505940445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27802076425783613670626963 41703114638675420505940445)
  ·
    refine ⟨15638667989503282689727667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41703114638675420505940445 15638667989503282689727667)
    ·
      refine ⟨23458001984254924034591501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15638667989503282689727667 23458001984254924034591501)
      ·
        refine ⟨8796750744095596512971813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23458001984254924034591501 8796750744095596512971813)
        ·
          refine ⟨1649390764517924346182215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8796750744095596512971813 1649390764517924346182215)
          ·
            refine ⟨2474086146776886519273323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649390764517924346182215 2474086146776886519273323)
            ·
              refine ⟨3711129220165329778909985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474086146776886519273323 3711129220165329778909985)
              ·
                refine ⟨2783346915123997334182489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3711129220165329778909985 2783346915123997334182489)
                ·
                  refine ⟨2087510186342998000636867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783346915123997334182489 2087510186342998000636867)
                  ·
                    refine ⟨3131265279514497000955301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2087510186342998000636867 3131265279514497000955301)
                    ·
                      refine ⟨587112239908968187679119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3131265279514497000955301 587112239908968187679119)
                      ·
                        rfl

theorem cell23_1143397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1143397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143397 prefixEnd_1143397 := by exact prefixLift 1143397
  have htrace : WordTrace (prefixWord ++ tailWord_1143397) baseStart_1143397 baseEnd_1143397 := by
    simpa [prefixWord, tailWord_1143397, baseEnd_1143397] using wordTrace_append hprefix tailTrace_1143397
  have hstable : (prefixWord ++ tailWord_1143397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143397).length < 2 ^ (prefixWord ++ tailWord_1143397).sum := by decide
  have hdescent : baseEnd_1143397 < baseStart_1143397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143407 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 1, 4]
def baseStart_1143407 : Nat := 118140960795 + 1143407 * 2 ^ 59
def prefixEnd_1143407 : Nat := 4983230072969 + 3 ^ 40 * 1143407 * 2
def baseEnd_1143407 : Nat := 195705791571837716184691

theorem tailTrace_1143407 : CollatzResearch.WordTrace tailWord_1143407 prefixEnd_1143407 195705791571837716184691 := by
  unfold tailWord_1143407
  simp only [CollatzResearch.WordTrace]
  refine ⟨41703479368639192213804475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27802319579092794809202983 41703479368639192213804475)
  ·
    refine ⟨62555219052958788320706713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41703479368639192213804475 62555219052958788320706713)
    ·
      refine ⟨46916414289719091240530035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62555219052958788320706713 46916414289719091240530035)
      ·
        refine ⟨70374621434578636860795053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46916414289719091240530035 70374621434578636860795053)
        ·
          refine ⟨26390483037966988822798145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70374621434578636860795053 26390483037966988822798145)
          ·
            refine ⟨19792862278475241617098609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26390483037966988822798145 19792862278475241617098609)
            ·
              refine ⟨14844646708856431212823957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19792862278475241617098609 14844646708856431212823957)
              ·
                refine ⟨695842814477645213101123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14844646708856431212823957 695842814477645213101123)
                ·
                  refine ⟨1043764221716467819651685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 695842814477645213101123 1043764221716467819651685)
                  ·
                    refine ⟨195705791571837716184691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043764221716467819651685 195705791571837716184691)
                    ·
                      rfl

theorem cell23_1143407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 4].length) (baseStart_1143407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143407 prefixEnd_1143407 := by exact prefixLift 1143407
  have htrace : WordTrace (prefixWord ++ tailWord_1143407) baseStart_1143407 baseEnd_1143407 := by
    simpa [prefixWord, tailWord_1143407, baseEnd_1143407] using wordTrace_append hprefix tailTrace_1143407
  have hstable : (prefixWord ++ tailWord_1143407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143407).length < 2 ^ (prefixWord ++ tailWord_1143407).sum := by decide
  have hdescent : baseEnd_1143407 < baseStart_1143407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143434 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1143434 : Nat := 118140960795 + 1143434 * 2 ^ 59
def prefixEnd_1143434 : Nat := 4983230072969 + 3 ^ 40 * 1143434 * 2
def baseEnd_1143434 : Nat := 587131238693184542916449

theorem tailTrace_1143434 : CollatzResearch.WordTrace tailWord_1143434 prefixEnd_1143434 587131238693184542916449 := by
  unfold tailWord_1143434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10426116034885343956259339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27802976093027583883358237 10426116034885343956259339)
  ·
    refine ⟨15639174052328015934389009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10426116034885343956259339 15639174052328015934389009)
    ·
      refine ⟨11729380539246011950791757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15639174052328015934389009 11729380539246011950791757)
      ·
        refine ⟨4398517702217254481546909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11729380539246011950791757 4398517702217254481546909)
        ·
          refine ⟨1649444138331470430580091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4398517702217254481546909 1649444138331470430580091)
          ·
            refine ⟨2474166207497205645870137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649444138331470430580091 2474166207497205645870137)
            ·
              refine ⟨1855624655622904234402603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474166207497205645870137 1855624655622904234402603)
              ·
                refine ⟨2783436983434356351603905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855624655622904234402603 2783436983434356351603905)
                ·
                  refine ⟨2087577737575767263702929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783436983434356351603905 2087577737575767263702929)
                  ·
                    refine ⟨1565683303181825447777197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2087577737575767263702929 1565683303181825447777197)
                    ·
                      refine ⟨587131238693184542916449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1565683303181825447777197 587131238693184542916449)
                      ·
                        rfl

theorem cell23_1143434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1143434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143434 prefixEnd_1143434 := by exact prefixLift 1143434
  have htrace : WordTrace (prefixWord ++ tailWord_1143434) baseStart_1143434 baseEnd_1143434 := by
    simpa [prefixWord, tailWord_1143434, baseEnd_1143434] using wordTrace_append hprefix tailTrace_1143434
  have hstable : (prefixWord ++ tailWord_1143434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143434).length < 2 ^ (prefixWord ++ tailWord_1143434).sum := by decide
  have hdescent : baseEnd_1143434 < baseStart_1143434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143480 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 8, 4]
def baseStart_1143480 : Nat := 118140960795 + 1143480 * 2 ^ 59
def prefixEnd_1143480 : Nat := 4983230072969 + 3 ^ 40 * 1143480 * 2
def baseEnd_1143480 : Nat := 195718286267763787647079

theorem tailTrace_1143480 : CollatzResearch.WordTrace tailWord_1143480 prefixEnd_1143480 195718286267763787647079 := by
  unfold tailWord_1143480
  simp only [CollatzResearch.WordTrace]
  refine ⟨20853070948687362840605947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27804094598249817120807929 20853070948687362840605947)
  ·
    refine ⟨31279606423031044260908921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20853070948687362840605947 31279606423031044260908921)
    ·
      refine ⟨23459704817273283195681691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31279606423031044260908921 23459704817273283195681691)
      ·
        refine ⟨35189557225909924793522537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23459704817273283195681691 35189557225909924793522537)
        ·
          refine ⟨26392167919432443595141903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35189557225909924793522537 26392167919432443595141903)
          ·
            refine ⟨39588251879148665392712855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26392167919432443595141903 39588251879148665392712855)
            ·
              refine ⟨59382377818722998089069283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39588251879148665392712855 59382377818722998089069283)
              ·
                refine ⟨89073566728084497133603925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59382377818722998089069283 89073566728084497133603925)
                ·
                  refine ⟨1043830860094740200784421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 89073566728084497133603925 1043830860094740200784421)
                  ·
                    refine ⟨195718286267763787647079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1043830860094740200784421 195718286267763787647079)
                    ·
                      rfl

theorem cell23_1143480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_1143480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143480 prefixEnd_1143480 := by exact prefixLift 1143480
  have htrace : WordTrace (prefixWord ++ tailWord_1143480) baseStart_1143480 baseEnd_1143480 := by
    simpa [prefixWord, tailWord_1143480, baseEnd_1143480] using wordTrace_append hprefix tailTrace_1143480
  have hstable : (prefixWord ++ tailWord_1143480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143480).length < 2 ^ (prefixWord ++ tailWord_1143480).sum := by decide
  have hdescent : baseEnd_1143480 < baseStart_1143480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143501 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1143501 : Nat := 118140960795 + 1143501 * 2 ^ 59
def prefixEnd_1143501 : Nat := 4983230072969 + 3 ^ 40 * 1143501 * 2
def baseEnd_1143501 : Nat := 195721880632345260259547

theorem tailTrace_1143501 : CollatzResearch.WordTrace tailWord_1143501 prefixEnd_1143501 195721880632345260259547 := by
  unfold tailWord_1143501
  simp only [CollatzResearch.WordTrace]
  refine ⟨41706907830298646267726357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27804605220199097511817571 41706907830298646267726357)
  ·
    refine ⟨1955011304545249043799673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41706907830298646267726357 1955011304545249043799673)
    ·
      refine ⟨1466258478408936782849755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1955011304545249043799673 1466258478408936782849755)
      ·
        refine ⟨2199387717613405174274633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466258478408936782849755 2199387717613405174274633)
        ·
          refine ⟨1649540788210053880705975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2199387717613405174274633 1649540788210053880705975)
          ·
            refine ⟨2474311182315080821058963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649540788210053880705975 2474311182315080821058963)
            ·
              refine ⟨3711466773472621231588445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474311182315080821058963 3711466773472621231588445)
              ·
                refine ⟨1391800040052232961845667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3711466773472621231588445 1391800040052232961845667)
                ·
                  refine ⟨2087700060078349442768501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391800040052232961845667 2087700060078349442768501)
                  ·
                    refine ⟨195721880632345260259547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2087700060078349442768501 195721880632345260259547)
                    ·
                      rfl

theorem cell23_1143501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1143501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143501 prefixEnd_1143501 := by exact prefixLift 1143501
  have htrace : WordTrace (prefixWord ++ tailWord_1143501) baseStart_1143501 baseEnd_1143501 := by
    simpa [prefixWord, tailWord_1143501, baseEnd_1143501] using wordTrace_append hprefix tailTrace_1143501
  have hstable : (prefixWord ++ tailWord_1143501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143501).length < 2 ^ (prefixWord ++ tailWord_1143501).sum := by decide
  have hdescent : baseEnd_1143501 < baseStart_1143501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143521 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 3, 2, 2]
def baseStart_1143521 : Nat := 118140960795 + 1143521 * 2 ^ 59
def prefixEnd_1143521 : Nat := 4983230072969 + 3 ^ 40 * 1143521 * 2
def baseEnd_1143521 : Nat := 587175911510125702528549

theorem tailTrace_1143521 : CollatzResearch.WordTrace tailWord_1143521 prefixEnd_1143521 587175911510125702528549 := by
  unfold tailWord_1143521
  simp only [CollatzResearch.WordTrace]
  refine ⟨41707637290226189683454417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27805091526817459788969611 41707637290226189683454417)
  ·
    refine ⟨31280727967669642262590813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41707637290226189683454417 31280727967669642262590813)
    ·
      refine ⟨11730272987876115848471555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31280727967669642262590813 11730272987876115848471555)
      ·
        refine ⟨17595409481814173772707333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11730272987876115848471555 17595409481814173772707333)
        ·
          refine ⟨3299139277840157582382625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17595409481814173772707333 3299139277840157582382625)
          ·
            refine ⟨2474354458380118186786969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299139277840157582382625 2474354458380118186786969)
            ·
              refine ⟨1855765843785088640090227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474354458380118186786969 1855765843785088640090227)
              ·
                refine ⟨2783648765677632960135341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855765843785088640090227 2783648765677632960135341)
                ·
                  refine ⟨1043868287129112360050753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2783648765677632960135341 1043868287129112360050753)
                  ·
                    refine ⟨782901215346834270038065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1043868287129112360050753 782901215346834270038065)
                    ·
                      refine ⟨587175911510125702528549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782901215346834270038065 587175911510125702528549)
                      ·
                        rfl

theorem cell23_1143521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_1143521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143521 prefixEnd_1143521 := by exact prefixLift 1143521
  have htrace : WordTrace (prefixWord ++ tailWord_1143521) baseStart_1143521 baseEnd_1143521 := by
    simpa [prefixWord, tailWord_1143521, baseEnd_1143521] using wordTrace_append hprefix tailTrace_1143521
  have hstable : (prefixWord ++ tailWord_1143521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143521).length < 2 ^ (prefixWord ++ tailWord_1143521).sum := by decide
  have hdescent : baseEnd_1143521 < baseStart_1143521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143534 : List Nat := [4, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_1143534 : Nat := 118140960795 + 1143534 * 2 ^ 59
def prefixEnd_1143534 : Nat := 4983230072969 + 3 ^ 40 * 1143534 * 2
def baseEnd_1143534 : Nat := 587182586758634151665989

theorem tailTrace_1143534 : CollatzResearch.WordTrace tailWord_1143534 prefixEnd_1143534 587182586758634151665989 := by
  unfold tailWord_1143534
  simp only [CollatzResearch.WordTrace]
  refine ⟨5213513929897386612959707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27805407626119395269118437 5213513929897386612959707)
  ·
    refine ⟨7820270894846079919439561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5213513929897386612959707 7820270894846079919439561)
    ·
      refine ⟨5865203171134559939579671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7820270894846079919439561 5865203171134559939579671)
      ·
        refine ⟨8797804756701839909369507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865203171134559939579671 8797804756701839909369507)
        ·
          refine ⟨13196707135052759864054261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8797804756701839909369507 13196707135052759864054261)
          ·
            refine ⟨1237191293911196237255087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13196707135052759864054261 1237191293911196237255087)
            ·
              refine ⟨1855786940866794355882631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237191293911196237255087 1855786940866794355882631)
              ·
                refine ⟨2783680411300191533823947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855786940866794355882631 2783680411300191533823947)
                ·
                  refine ⟨4175520616950287300735921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783680411300191533823947 4175520616950287300735921)
                  ·
                    refine ⟨3131640462712715475551941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4175520616950287300735921 3131640462712715475551941)
                    ·
                      refine ⟨587182586758634151665989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3131640462712715475551941 587182586758634151665989)
                      ·
                        rfl

theorem cell23_1143534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_1143534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143534 prefixEnd_1143534 := by exact prefixLift 1143534
  have htrace : WordTrace (prefixWord ++ tailWord_1143534) baseStart_1143534 baseEnd_1143534 := by
    simpa [prefixWord, tailWord_1143534, baseEnd_1143534] using wordTrace_append hprefix tailTrace_1143534
  have hstable : (prefixWord ++ tailWord_1143534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143534).length < 2 ^ (prefixWord ++ tailWord_1143534).sum := by decide
  have hdescent : baseEnd_1143534 < baseStart_1143534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143547 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 7, 3, 2]
def baseStart_1143547 : Nat := 118140960795 + 1143547 * 2 ^ 59
def prefixEnd_1143547 : Nat := 4983230072969 + 3 ^ 40 * 1143547 * 2
def baseEnd_1143547 : Nat := 587189262007142600803429

theorem tailTrace_1143547 : CollatzResearch.WordTrace tailWord_1143547 prefixEnd_1143547 587189262007142600803429 := by
  unfold tailWord_1143547
  simp only [CollatzResearch.WordTrace]
  refine ⟨41708585588131996123900895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27805723725421330749267263 41708585588131996123900895)
  ·
    refine ⟨62562878382197994185851343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41708585588131996123900895 62562878382197994185851343)
    ·
      refine ⟨93844317573296991278777015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62562878382197994185851343 93844317573296991278777015)
      ·
        refine ⟨140766476359945486918165523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93844317573296991278777015 140766476359945486918165523)
        ·
          refine ⟨211149714539918230377248285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140766476359945486918165523 211149714539918230377248285)
          ·
            refine ⟨79181142952469336391468107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211149714539918230377248285 79181142952469336391468107)
            ·
              refine ⟨118771714428704004587202161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79181142952469336391468107 118771714428704004587202161)
              ·
                refine ⟨89078785821528003440401621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118771714428704004587202161 89078785821528003440401621)
                ·
                  refine ⟨2087784042692062580634413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89078785821528003440401621 2087784042692062580634413)
                  ·
                    refine ⟨782919016009523467737905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087784042692062580634413 782919016009523467737905)
                    ·
                      refine ⟨587189262007142600803429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782919016009523467737905 587189262007142600803429)
                      ·
                        rfl

theorem cell23_1143547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 3, 2].length) (baseStart_1143547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143547 prefixEnd_1143547 := by exact prefixLift 1143547
  have htrace : WordTrace (prefixWord ++ tailWord_1143547) baseStart_1143547 baseEnd_1143547 := by
    simpa [prefixWord, tailWord_1143547, baseEnd_1143547] using wordTrace_append hprefix tailTrace_1143547
  have hstable : (prefixWord ++ tailWord_1143547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143547).length < 2 ^ (prefixWord ++ tailWord_1143547).sum := by decide
  have hdescent : baseEnd_1143547 < baseStart_1143547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143577 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 5, 4, 2]
def baseStart_1143577 : Nat := 118140960795 + 1143577 * 2 ^ 59
def prefixEnd_1143577 : Nat := 4983230072969 + 3 ^ 40 * 1143577 * 2
def baseEnd_1143577 : Nat := 587204666426777483428291

theorem tailTrace_1143577 : CollatzResearch.WordTrace tailWord_1143577 prefixEnd_1143577 587204666426777483428291 := by
  unfold tailWord_1143577
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709679778023311247492985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27806453185348874164995323 41709679778023311247492985)
  ·
    refine ⟨31282259833517483435619739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41709679778023311247492985 31282259833517483435619739)
    ·
      refine ⟨46923389750276225153429609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31282259833517483435619739 46923389750276225153429609)
      ·
        refine ⟨35192542312707168865072207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46923389750276225153429609 35192542312707168865072207)
        ·
          refine ⟨52788813469060753297608311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35192542312707168865072207 52788813469060753297608311)
          ·
            refine ⟨79183220203591129946412467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52788813469060753297608311 79183220203591129946412467)
            ·
              refine ⟨118774830305386694919618701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79183220203591129946412467 118774830305386694919618701)
              ·
                refine ⟨44540561364520010594857013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118774830305386694919618701 44540561364520010594857013)
                ·
                  refine ⟨4175677627923750993267845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44540561364520010594857013 4175677627923750993267845)
                  ·
                    refine ⟨782939555235703311237721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175677627923750993267845 782939555235703311237721)
                    ·
                      refine ⟨587204666426777483428291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782939555235703311237721 587204666426777483428291)
                      ·
                        rfl

theorem cell23_1143577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_1143577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143577 prefixEnd_1143577 := by exact prefixLift 1143577
  have htrace : WordTrace (prefixWord ++ tailWord_1143577) baseStart_1143577 baseEnd_1143577 := by
    simpa [prefixWord, tailWord_1143577, baseEnd_1143577] using wordTrace_append hprefix tailTrace_1143577
  have hstable : (prefixWord ++ tailWord_1143577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143577).length < 2 ^ (prefixWord ++ tailWord_1143577).sum := by decide
  have hdescent : baseEnd_1143577 < baseStart_1143577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143598 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1143598 : Nat := 118140960795 + 1143598 * 2 ^ 59
def prefixEnd_1143598 : Nat := 4983230072969 + 3 ^ 40 * 1143598 * 2
def baseEnd_1143598 : Nat := 587215449520521901265695

theorem tailTrace_1143598 : CollatzResearch.WordTrace tailWord_1143598 prefixEnd_1143598 587215449520521901265695 := by
  unfold tailWord_1143598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5213805713868403979250931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27806963807298154556004965 5213805713868403979250931)
  ·
    refine ⟨7820708570802605968876397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5213805713868403979250931 7820708570802605968876397)
    ·
      refine ⟨2932765714050977238328649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7820708570802605968876397 2932765714050977238328649)
      ·
        refine ⟨2199574285538232928746487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2932765714050977238328649 2199574285538232928746487)
        ·
          refine ⟨3299361428307349393119731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199574285538232928746487 3299361428307349393119731)
          ·
            refine ⟨4949042142461024089679597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299361428307349393119731 4949042142461024089679597)
            ·
              refine ⟨1855890803422884033629849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4949042142461024089679597 1855890803422884033629849)
              ·
                refine ⟨1391918102567163025222387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855890803422884033629849 1391918102567163025222387)
                ·
                  refine ⟨2087877153850744537833581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391918102567163025222387 2087877153850744537833581)
                  ·
                    refine ⟨782953932694029201687593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087877153850744537833581 782953932694029201687593)
                    ·
                      refine ⟨587215449520521901265695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782953932694029201687593 587215449520521901265695)
                      ·
                        rfl

theorem cell23_1143598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1143598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143598 prefixEnd_1143598 := by exact prefixLift 1143598
  have htrace : WordTrace (prefixWord ++ tailWord_1143598) baseStart_1143598 baseEnd_1143598 := by
    simpa [prefixWord, tailWord_1143598, baseEnd_1143598] using wordTrace_append hprefix tailTrace_1143598
  have hstable : (prefixWord ++ tailWord_1143598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143598).length < 2 ^ (prefixWord ++ tailWord_1143598).sum := by decide
  have hdescent : baseEnd_1143598 < baseStart_1143598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143600 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 7]
def baseStart_1143600 : Nat := 118140960795 + 1143600 * 2 ^ 59
def prefixEnd_1143600 : Nat := 4983230072969 + 3 ^ 40 * 1143600 * 2
def baseEnd_1143600 : Nat := 65246275164647877048965

theorem tailTrace_1143600 : CollatzResearch.WordTrace tailWord_1143600 prefixEnd_1143600 65246275164647877048965 := by
  unfold tailWord_1143600
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855259328469993087790127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27807012437959990783720169 20855259328469993087790127)
  ·
    refine ⟨31282888992704989631685191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20855259328469993087790127 31282888992704989631685191)
    ·
      refine ⟨46924333489057484447527787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31282888992704989631685191 46924333489057484447527787)
      ·
        refine ⟨70386500233586226671291681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46924333489057484447527787 70386500233586226671291681)
        ·
          refine ⟨52789875175189670003468761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70386500233586226671291681 52789875175189670003468761)
          ·
            refine ⟨39592406381392252502601571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52789875175189670003468761 39592406381392252502601571)
            ·
              refine ⟨59388609572088378753902357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39592406381392252502601571 59388609572088378753902357)
              ·
                refine ⟨2783841073691642754089173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59388609572088378753902357 2783841073691642754089173)
                ·
                  refine ⟨65246275164647877048965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2783841073691642754089173 65246275164647877048965)
                  ·
                    rfl

theorem cell23_1143600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 7].length) (baseStart_1143600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143600 prefixEnd_1143600 := by exact prefixLift 1143600
  have htrace : WordTrace (prefixWord ++ tailWord_1143600) baseStart_1143600 baseEnd_1143600 := by
    simpa [prefixWord, tailWord_1143600, baseEnd_1143600] using wordTrace_append hprefix tailTrace_1143600
  have hstable : (prefixWord ++ tailWord_1143600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143600).length < 2 ^ (prefixWord ++ tailWord_1143600).sum := by decide
  have hdescent : baseEnd_1143600 < baseStart_1143600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143628 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1143628 : Nat := 118140960795 + 1143628 * 2 ^ 59
def prefixEnd_1143628 : Nat := 4983230072969 + 3 ^ 40 * 1143628 * 2
def baseEnd_1143628 : Nat := 587230853940156783890557

theorem tailTrace_1143628 : CollatzResearch.WordTrace tailWord_1143628 prefixEnd_1143628 587230853940156783890557 := by
  unfold tailWord_1143628
  simp only [CollatzResearch.WordTrace]
  refine ⟨20855769950419273478799769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27807693267225697971733025 20855769950419273478799769)
  ·
    refine ⟨15641827462814455109099827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20855769950419273478799769 15641827462814455109099827)
    ·
      refine ⟨23462741194221682663649741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15641827462814455109099827 23462741194221682663649741)
      ·
        refine ⟨8798527947833130998868653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23462741194221682663649741 8798527947833130998868653)
        ·
          refine ⟨3299447980437424124575745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8798527947833130998868653 3299447980437424124575745)
          ·
            refine ⟨2474585985328068093431809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299447980437424124575745 2474585985328068093431809)
            ·
              refine ⟨1855939488996051070073857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474585985328068093431809 1855939488996051070073857)
              ·
                refine ⟨1391954616747038302555393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855939488996051070073857 1391954616747038302555393)
                ·
                  refine ⟨1043965962560278726916545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1391954616747038302555393 1043965962560278726916545)
                  ·
                    refine ⟨782974471920209045187409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1043965962560278726916545 782974471920209045187409)
                    ·
                      refine ⟨587230853940156783890557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 782974471920209045187409 587230853940156783890557)
                      ·
                        rfl

theorem cell23_1143628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1143628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143628 prefixEnd_1143628 := by exact prefixLift 1143628
  have htrace : WordTrace (prefixWord ++ tailWord_1143628) baseStart_1143628 baseEnd_1143628 := by
    simpa [prefixWord, tailWord_1143628, baseEnd_1143628] using wordTrace_append hprefix tailTrace_1143628
  have hstable : (prefixWord ++ tailWord_1143628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143628).length < 2 ^ (prefixWord ++ tailWord_1143628).sum := by decide
  have hdescent : baseEnd_1143628 < baseStart_1143628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143634 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 5]
def baseStart_1143634 : Nat := 118140960795 + 1143634 * 2 ^ 59
def prefixEnd_1143634 : Nat := 4983230072969 + 3 ^ 40 * 1143634 * 2
def baseEnd_1143634 : Nat := 65248214980453751157281

theorem tailTrace_1143634 : CollatzResearch.WordTrace tailWord_1143634 prefixEnd_1143634 65248214980453751157281 := by
  unfold tailWord_1143634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427939684704202495579489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27807839159211206654878637 10427939684704202495579489)
  ·
    refine ⟨7820954763528151871684617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10427939684704202495579489 7820954763528151871684617)
    ·
      refine ⟨5865716072646113903763463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7820954763528151871684617 5865716072646113903763463)
      ·
        refine ⟨8798574108969170855645195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5865716072646113903763463 8798574108969170855645195)
        ·
          refine ⟨13197861163453756283467793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8798574108969170855645195 13197861163453756283467793)
          ·
            refine ⟨9898395872590317212600845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13197861163453756283467793 9898395872590317212600845)
            ·
              refine ⟨3711898452221368954725317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9898395872590317212600845 3711898452221368954725317)
              ·
                refine ⟨695980959791506679010997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3711898452221368954725317 695980959791506679010997)
                ·
                  refine ⟨65248214980453751157281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 695980959791506679010997 65248214980453751157281)
                  ·
                    rfl

theorem cell23_1143634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_1143634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143634 prefixEnd_1143634 := by exact prefixLift 1143634
  have htrace : WordTrace (prefixWord ++ tailWord_1143634) baseStart_1143634 baseEnd_1143634 := by
    simpa [prefixWord, tailWord_1143634, baseEnd_1143634] using wordTrace_append hprefix tailTrace_1143634
  have hstable : (prefixWord ++ tailWord_1143634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143634).length < 2 ^ (prefixWord ++ tailWord_1143634).sum := by decide
  have hdescent : baseEnd_1143634 < baseStart_1143634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143644 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1143644 : Nat := 118140960795 + 1143644 * 2 ^ 59
def prefixEnd_1143644 : Nat := 4983230072969 + 3 ^ 40 * 1143644 * 2
def baseEnd_1143644 : Nat := 587239069630628721290483

theorem tailTrace_1143644 : CollatzResearch.WordTrace tailWord_1143644 prefixEnd_1143644 587239069630628721290483 := by
  unfold tailWord_1143644
  simp only [CollatzResearch.WordTrace]
  refine ⟨20856061734390290845090993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27808082312520387793454657 20856061734390290845090993)
  ·
    refine ⟨15642046300792718133818245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20856061734390290845090993 15642046300792718133818245)
    ·
      refine ⟨2932883681398634650090921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15642046300792718133818245 2932883681398634650090921)
      ·
        refine ⟨2199662761048975987568191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2932883681398634650090921 2199662761048975987568191)
        ·
          refine ⟨3299494141573463981352287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199662761048975987568191 3299494141573463981352287)
          ·
            refine ⟨4949241212360195972028431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299494141573463981352287 4949241212360195972028431)
            ·
              refine ⟨7423861818540293958042647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949241212360195972028431 7423861818540293958042647)
              ·
                refine ⟨11135792727810440937063971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423861818540293958042647 11135792727810440937063971)
                ·
                  refine ⟨16703689091715661405595957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11135792727810440937063971 16703689091715661405595957)
                  ·
                    refine ⟨1565970852348343256774621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16703689091715661405595957 1565970852348343256774621)
                    ·
                      refine ⟨587239069630628721290483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1565970852348343256774621 587239069630628721290483)
                      ·
                        rfl

theorem cell23_1143644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1143644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143644 prefixEnd_1143644 := by exact prefixLift 1143644
  have htrace : WordTrace (prefixWord ++ tailWord_1143644) baseStart_1143644 baseEnd_1143644 := by
    simpa [prefixWord, tailWord_1143644, baseEnd_1143644] using wordTrace_append hprefix tailTrace_1143644
  have hstable : (prefixWord ++ tailWord_1143644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143644).length < 2 ^ (prefixWord ++ tailWord_1143644).sum := by decide
  have hdescent : baseEnd_1143644 < baseStart_1143644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143751 : List Nat := [1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 3]
def baseStart_1143751 : Nat := 118140960795 + 1143751 * 2 ^ 59
def prefixEnd_1143751 : Nat := 4983230072969 + 3 ^ 40 * 1143751 * 2
def baseEnd_1143751 : Nat := 587294012060659802652491

theorem tailTrace_1143751 : CollatzResearch.WordTrace tailWord_1143751 prefixEnd_1143751 587294012060659802652491 := by
  unfold tailWord_1143751
  simp only [CollatzResearch.WordTrace]
  refine ⟨41716026079392938964327107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27810684052928625976218071 41716026079392938964327107)
  ·
    refine ⟨62574039119089408446490661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41716026079392938964327107 62574039119089408446490661)
    ·
      refine ⟨11732632334829264083716999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62574039119089408446490661 11732632334829264083716999)
      ·
        refine ⟨17598948502243896125575499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11732632334829264083716999 17598948502243896125575499)
        ·
          refine ⟨26398422753365844188363249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17598948502243896125575499 26398422753365844188363249)
          ·
            refine ⟨19798817065024383141272437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26398422753365844188363249 19798817065024383141272437)
            ·
              refine ⟨1856139099846035919494291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19798817065024383141272437 1856139099846035919494291)
              ·
                refine ⟨2784208649769053879241437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856139099846035919494291 2784208649769053879241437)
                ·
                  refine ⟨1044078243663395204715539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2784208649769053879241437 1044078243663395204715539)
                  ·
                    refine ⟨1566117365495092807073309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1044078243663395204715539 1566117365495092807073309)
                    ·
                      refine ⟨587294012060659802652491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566117365495092807073309 587294012060659802652491)
                      ·
                        rfl

theorem cell23_1143751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_1143751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143751 prefixEnd_1143751 := by exact prefixLift 1143751
  have htrace : WordTrace (prefixWord ++ tailWord_1143751) baseStart_1143751 baseEnd_1143751 := by
    simpa [prefixWord, tailWord_1143751, baseEnd_1143751] using wordTrace_append hprefix tailTrace_1143751
  have hstable : (prefixWord ++ tailWord_1143751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143751).length < 2 ^ (prefixWord ++ tailWord_1143751).sum := by decide
  have hdescent : baseEnd_1143751 < baseStart_1143751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143784 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 6, 4]
def baseStart_1143784 : Nat := 118140960795 + 1143784 * 2 ^ 59
def prefixEnd_1143784 : Nat := 4983230072969 + 3 ^ 40 * 1143784 * 2
def baseEnd_1143784 : Nat := 195770318974086057846613

theorem tailTrace_1143784 : CollatzResearch.WordTrace tailWord_1143784 prefixEnd_1143784 195770318974086057846613 := by
  unfold tailWord_1143784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20858614844136692800139203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27811486458848923733518937 20858614844136692800139203)
  ·
    refine ⟨31287922266205039200208805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20858614844136692800139203 31287922266205039200208805)
    ·
      refine ⟨5866485424913444850039151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31287922266205039200208805 5866485424913444850039151)
      ·
        refine ⟨8799728137370167275058727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866485424913444850039151 8799728137370167275058727)
        ·
          refine ⟨13199592206055250912588091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799728137370167275058727 13199592206055250912588091)
          ·
            refine ⟨19799388309082876368882137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13199592206055250912588091 19799388309082876368882137)
            ·
              refine ⟨14849541231812157276661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19799388309082876368882137 14849541231812157276661603)
              ·
                refine ⟨22274311847718235914992405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14849541231812157276661603 22274311847718235914992405)
                ·
                  refine ⟨1044108367861792308515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22274311847718235914992405 1044108367861792308515269)
                  ·
                    refine ⟨195770318974086057846613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044108367861792308515269 195770318974086057846613)
                    ·
                      rfl

theorem cell23_1143784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_1143784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143784 prefixEnd_1143784 := by exact prefixLift 1143784
  have htrace : WordTrace (prefixWord ++ tailWord_1143784) baseStart_1143784 baseEnd_1143784 := by
    simpa [prefixWord, tailWord_1143784, baseEnd_1143784] using wordTrace_append hprefix tailTrace_1143784
  have hstable : (prefixWord ++ tailWord_1143784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143784).length < 2 ^ (prefixWord ++ tailWord_1143784).sum := by decide
  have hdescent : baseEnd_1143784 < baseStart_1143784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143801 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_1143801 : Nat := 118140960795 + 1143801 * 2 ^ 59
def prefixEnd_1143801 : Nat := 4983230072969 + 3 ^ 40 * 1143801 * 2
def baseEnd_1143801 : Nat := 195773228697794869009087

theorem tailTrace_1143801 : CollatzResearch.WordTrace tailWord_1143801 prefixEnd_1143801 195773228697794869009087 := by
  unfold tailWord_1143801
  simp only [CollatzResearch.WordTrace]
  refine ⟨41717849729211797503647257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27811899819474531669098171 41717849729211797503647257)
  ·
    refine ⟨31288387296908848127735443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41717849729211797503647257 31288387296908848127735443)
    ·
      refine ⟨46932580945363272191603165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31288387296908848127735443 46932580945363272191603165)
      ·
        refine ⟨17599717854511227071851187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46932580945363272191603165 17599717854511227071851187)
        ·
          refine ⟨26399576781766840607776781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17599717854511227071851187 26399576781766840607776781)
          ·
            refine ⟨9899841293162565227916293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26399576781766840607776781 9899841293162565227916293)
            ·
              refine ⟨1856220242467980980234305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9899841293162565227916293 1856220242467980980234305)
              ·
                refine ⟨1392165181850985735175729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856220242467980980234305 1392165181850985735175729)
                ·
                  refine ⟨1044123886388239301381797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1392165181850985735175729 1044123886388239301381797)
                  ·
                    refine ⟨195773228697794869009087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044123886388239301381797 195773228697794869009087)
                    ·
                      rfl

theorem cell23_1143801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_1143801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143801 prefixEnd_1143801 := by exact prefixLift 1143801
  have htrace : WordTrace (prefixWord ++ tailWord_1143801) baseStart_1143801 baseEnd_1143801 := by
    simpa [prefixWord, tailWord_1143801, baseEnd_1143801] using wordTrace_append hprefix tailTrace_1143801
  have hstable : (prefixWord ++ tailWord_1143801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143801).length < 2 ^ (prefixWord ++ tailWord_1143801).sum := by decide
  have hdescent : baseEnd_1143801 < baseStart_1143801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143817 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 6]
def baseStart_1143817 : Nat := 118140960795 + 1143817 * 2 ^ 59
def prefixEnd_1143817 : Nat := 4983230072969 + 3 ^ 40 * 1143817 * 2
def baseEnd_1143817 : Nat := 587327901783856544427187

theorem tailTrace_1143817 : CollatzResearch.WordTrace tailWord_1143817 prefixEnd_1143817 587327901783856544427187 := by
  unfold tailWord_1143817
  simp only [CollatzResearch.WordTrace]
  refine ⟨41718433297153832236229705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27812288864769221490819803 41718433297153832236229705)
  ·
    refine ⟨31288824972865374177172279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41718433297153832236229705 31288824972865374177172279)
    ·
      refine ⟨46933237459298061265758419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31288824972865374177172279 46933237459298061265758419)
      ·
        refine ⟨70399856188947091898637629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46933237459298061265758419 70399856188947091898637629)
        ·
          refine ⟨26399946070855159461989111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70399856188947091898637629 26399946070855159461989111)
          ·
            refine ⟨39599919106282739192983667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26399946070855159461989111 39599919106282739192983667)
            ·
              refine ⟨59399878659424108789475501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39599919106282739192983667 59399878659424108789475501)
              ·
                refine ⟨22274954497284040796053313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59399878659424108789475501 22274954497284040796053313)
                ·
                  refine ⟨16706215872963030597039985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22274954497284040796053313 16706215872963030597039985)
                  ·
                    refine ⟨12529661904722272947779989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16706215872963030597039985 12529661904722272947779989)
                    ·
                      refine ⟨587327901783856544427187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12529661904722272947779989 587327901783856544427187)
                      ·
                        rfl

theorem cell23_1143817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_1143817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143817 prefixEnd_1143817 := by exact prefixLift 1143817
  have htrace : WordTrace (prefixWord ++ tailWord_1143817) baseStart_1143817 baseEnd_1143817 := by
    simpa [prefixWord, tailWord_1143817, baseEnd_1143817] using wordTrace_append hprefix tailTrace_1143817
  have hstable : (prefixWord ++ tailWord_1143817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143817).length < 2 ^ (prefixWord ++ tailWord_1143817).sum := by decide
  have hdescent : baseEnd_1143817 < baseStart_1143817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143827 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 7]
def baseStart_1143827 : Nat := 118140960795 + 1143827 * 2 ^ 59
def prefixEnd_1143827 : Nat := 4983230072969 + 3 ^ 40 * 1143827 * 2
def baseEnd_1143827 : Nat := 195777678863467168434047

theorem tailTrace_1143827 : CollatzResearch.WordTrace tailWord_1143827 prefixEnd_1143827 195777678863467168434047 := by
  unfold tailWord_1143827
  simp only [CollatzResearch.WordTrace]
  refine ⟨41718798027117603944093735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27812532018078402629395823 41718798027117603944093735)
  ·
    refine ⟨62578197040676405916140603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41718798027117603944093735 62578197040676405916140603)
    ·
      refine ⟨93867295561014608874210905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62578197040676405916140603 93867295561014608874210905)
      ·
        refine ⟨70400471670760956655658179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93867295561014608874210905 70400471670760956655658179)
        ·
          refine ⟨105600707506141434983487269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70400471670760956655658179 105600707506141434983487269)
          ·
            refine ⟨19800132657401519059403863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105600707506141434983487269 19800132657401519059403863)
            ·
              refine ⟨29700198986102278589105795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19800132657401519059403863 29700198986102278589105795)
              ·
                refine ⟨44550298479153417883658693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29700198986102278589105795 44550298479153417883658693)
                ·
                  refine ⟨8353180964841265853186005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44550298479153417883658693 8353180964841265853186005)
                  ·
                    refine ⟨195777678863467168434047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8353180964841265853186005 195777678863467168434047)
                    ·
                      rfl

theorem cell23_1143827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_1143827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143827 prefixEnd_1143827 := by exact prefixLift 1143827
  have htrace : WordTrace (prefixWord ++ tailWord_1143827) baseStart_1143827 baseEnd_1143827 := by
    simpa [prefixWord, tailWord_1143827, baseEnd_1143827] using wordTrace_append hprefix tailTrace_1143827
  have hstable : (prefixWord ++ tailWord_1143827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143827).length < 2 ^ (prefixWord ++ tailWord_1143827).sum := by decide
  have hdescent : baseEnd_1143827 < baseStart_1143827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143831 : List Nat := [1, 1, 3, 5, 1, 2, 3, 7]
def baseStart_1143831 : Nat := 118140960795 + 1143831 * 2 ^ 59
def prefixEnd_1143831 : Nat := 4983230072969 + 3 ^ 40 * 1143831 * 2
def baseEnd_1143831 : Nat := 21753151500482203320449

theorem tailTrace_1143831 : CollatzResearch.WordTrace tailWord_1143831 prefixEnd_1143831 21753151500482203320449 := by
  unfold tailWord_1143831
  simp only [CollatzResearch.WordTrace]
  refine ⟨41718943919103112627239347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27812629279402075084826231 41718943919103112627239347)
  ·
    refine ⟨62578415878654668940859021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41718943919103112627239347 62578415878654668940859021)
    ·
      refine ⟨23466905954495500852822133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62578415878654668940859021 23466905954495500852822133)
      ·
        refine ⟨2200022433233953204952075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23466905954495500852822133 2200022433233953204952075)
        ·
          refine ⟨3300033649850929807428113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200022433233953204952075 3300033649850929807428113)
          ·
            refine ⟨2475025237388197355571085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3300033649850929807428113 2475025237388197355571085)
            ·
              refine ⟨928134464020574008339157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2475025237388197355571085 928134464020574008339157)
              ·
                refine ⟨21753151500482203320449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 928134464020574008339157 21753151500482203320449)
                ·
                  rfl

theorem cell23_1143831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 7].length) (baseStart_1143831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143831 prefixEnd_1143831 := by exact prefixLift 1143831
  have htrace : WordTrace (prefixWord ++ tailWord_1143831) baseStart_1143831 baseEnd_1143831 := by
    simpa [prefixWord, tailWord_1143831, baseEnd_1143831] using wordTrace_append hprefix tailTrace_1143831
  have hstable : (prefixWord ++ tailWord_1143831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143831).length < 2 ^ (prefixWord ++ tailWord_1143831).sum := by decide
  have hdescent : baseEnd_1143831 < baseStart_1143831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143841 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1143841 : Nat := 118140960795 + 1143841 * 2 ^ 59
def prefixEnd_1143841 : Nat := 4983230072969 + 3 ^ 40 * 1143841 * 2
def baseEnd_1143841 : Nat := 587340225319564450527077

theorem tailTrace_1143841 : CollatzResearch.WordTrace tailWord_1143841 prefixEnd_1143841 587340225319564450527077 := by
  unfold tailWord_1143841
  simp only [CollatzResearch.WordTrace]
  refine ⟨41719308649066884335103377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27812872432711256223402251 41719308649066884335103377)
  ·
    refine ⟨31289481486800163251327533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41719308649066884335103377 31289481486800163251327533)
    ·
      refine ⟨11733555557550061219247825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31289481486800163251327533 11733555557550061219247825)
      ·
        refine ⟨8800166668162545914435869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11733555557550061219247825 8800166668162545914435869)
        ·
          refine ⟨3300062500560954717913451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8800166668162545914435869 3300062500560954717913451)
          ·
            refine ⟨4950093750841432076870177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300062500560954717913451 4950093750841432076870177)
            ·
              refine ⟨3712570313131074057652633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950093750841432076870177 3712570313131074057652633)
              ·
                refine ⟨2784427734848305543239475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712570313131074057652633 2784427734848305543239475)
                ·
                  refine ⟨4176641602272458314859213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784427734848305543239475 4176641602272458314859213)
                  ·
                    refine ⟨1566240600852171868072205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4176641602272458314859213 1566240600852171868072205)
                    ·
                      refine ⟨587340225319564450527077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566240600852171868072205 587340225319564450527077)
                      ·
                        rfl

theorem cell23_1143841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1143841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143841 prefixEnd_1143841 := by exact prefixLift 1143841
  have htrace : WordTrace (prefixWord ++ tailWord_1143841) baseStart_1143841 baseEnd_1143841 := by
    simpa [prefixWord, tailWord_1143841, baseEnd_1143841] using wordTrace_append hprefix tailTrace_1143841
  have hstable : (prefixWord ++ tailWord_1143841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143841).length < 2 ^ (prefixWord ++ tailWord_1143841).sum := by decide
  have hdescent : baseEnd_1143841 < baseStart_1143841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143842 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 1, 2, 2]
def baseStart_1143842 : Nat := 118140960795 + 1143842 * 2 ^ 59
def prefixEnd_1143842 : Nat := 4983230072969 + 3 ^ 40 * 1143842 * 2
def baseEnd_1143842 : Nat := 587340738800218946614573

theorem tailTrace_1143842 : CollatzResearch.WordTrace tailWord_1143842 prefixEnd_1143842 587340738800218946614573 := by
  unfold tailWord_1143842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10429836280515815376472445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27812896748042174337259853 10429836280515815376472445)
  ·
    refine ⟨3911188605193430766177167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10429836280515815376472445 3911188605193430766177167)
    ·
      refine ⟨5866782907790146149265751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911188605193430766177167 5866782907790146149265751)
      ·
        refine ⟨8800174361685219223898627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5866782907790146149265751 8800174361685219223898627)
        ·
          refine ⟨13200261542527828835847941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800174361685219223898627 13200261542527828835847941)
          ·
            refine ⟨2475049039223967906721489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13200261542527828835847941 2475049039223967906721489)
            ·
              refine ⟨1856286779417975930041117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475049039223967906721489 1856286779417975930041117)
              ·
                refine ⟨696107542281740973765419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1856286779417975930041117 696107542281740973765419)
                ·
                  refine ⟨1044161313422611460648129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696107542281740973765419 1044161313422611460648129)
                  ·
                    refine ⟨783120985066958595486097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1044161313422611460648129 783120985066958595486097)
                    ·
                      refine ⟨587340738800218946614573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783120985066958595486097 587340738800218946614573)
                      ·
                        rfl

theorem cell23_1143842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 1, 2, 2].length) (baseStart_1143842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143842 prefixEnd_1143842 := by exact prefixLift 1143842
  have htrace : WordTrace (prefixWord ++ tailWord_1143842) baseStart_1143842 baseEnd_1143842 := by
    simpa [prefixWord, tailWord_1143842, baseEnd_1143842] using wordTrace_append hprefix tailTrace_1143842
  have hstable : (prefixWord ++ tailWord_1143842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143842).length < 2 ^ (prefixWord ++ tailWord_1143842).sum := by decide
  have hdescent : baseEnd_1143842 < baseStart_1143842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143881 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 1, 4, 2]
def baseStart_1143881 : Nat := 118140960795 + 1143881 * 2 ^ 59
def prefixEnd_1143881 : Nat := 4983230072969 + 3 ^ 40 * 1143881 * 2
def baseEnd_1143881 : Nat := 587360764545744294026893

theorem tailTrace_1143881 : CollatzResearch.WordTrace tailWord_1143881 prefixEnd_1143881 587360764545744294026893 := by
  unfold tailWord_1143881
  simp only [CollatzResearch.WordTrace]
  refine ⟨41720767568921971166559497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27813845045947980777706331 41720767568921971166559497)
  ·
    refine ⟨31290575676691478374919623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41720767568921971166559497 31290575676691478374919623)
    ·
      refine ⟨46935863515037217562379435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31290575676691478374919623 46935863515037217562379435)
      ·
        refine ⟨70403795272555826343569153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46935863515037217562379435 70403795272555826343569153)
        ·
          refine ⟨52802846454416869757676865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70403795272555826343569153 52802846454416869757676865)
          ·
            refine ⟨39602134840812652318257649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52802846454416869757676865 39602134840812652318257649)
            ·
              refine ⟨29701601130609489238693237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39602134840812652318257649 29701601130609489238693237)
              ·
                refine ⟨2784525105994639616127491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29701601130609489238693237 2784525105994639616127491)
                ·
                  refine ⟨4176787658991959424191237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784525105994639616127491 4176787658991959424191237)
                  ·
                    refine ⟨783147686060992392035857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176787658991959424191237 783147686060992392035857)
                    ·
                      refine ⟨587360764545744294026893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783147686060992392035857 587360764545744294026893)
                      ·
                        rfl

theorem cell23_1143881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 4, 2].length) (baseStart_1143881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143881 prefixEnd_1143881 := by exact prefixLift 1143881
  have htrace : WordTrace (prefixWord ++ tailWord_1143881) baseStart_1143881 baseEnd_1143881 := by
    simpa [prefixWord, tailWord_1143881, baseEnd_1143881] using wordTrace_append hprefix tailTrace_1143881
  have hstable : (prefixWord ++ tailWord_1143881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143881).length < 2 ^ (prefixWord ++ tailWord_1143881).sum := by decide
  have hdescent : baseEnd_1143881 < baseStart_1143881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143884 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1143884 : Nat := 118140960795 + 1143884 * 2 ^ 59
def prefixEnd_1143884 : Nat := 4983230072969 + 3 ^ 40 * 1143884 * 2
def baseEnd_1143884 : Nat := 587362304987707782289379

theorem tailTrace_1143884 : CollatzResearch.WordTrace tailWord_1143884 prefixEnd_1143884 587362304987707782289379 := by
  unfold tailWord_1143884
  simp only [CollatzResearch.WordTrace]
  refine ⟨20860438493955551339459353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27813917991940735119279137 20860438493955551339459353)
  ·
    refine ⟨15645328870466663504594515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20860438493955551339459353 15645328870466663504594515)
    ·
      refine ⟨23467993305699995256891773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15645328870466663504594515 23467993305699995256891773)
      ·
        refine ⟨8800497489637498221334415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23467993305699995256891773 8800497489637498221334415)
        ·
          refine ⟨13200746234456247332001623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8800497489637498221334415 13200746234456247332001623)
          ·
            refine ⟨19801119351684370998002435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13200746234456247332001623 19801119351684370998002435)
            ·
              refine ⟨29701679027526556497003653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19801119351684370998002435 29701679027526556497003653)
              ·
                refine ⟨5569064817661229343188185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29701679027526556497003653 5569064817661229343188185)
                ·
                  refine ⟨4176798613245922007391139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5569064817661229343188185 4176798613245922007391139)
                  ·
                    refine ⟨6265197919868883011086709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4176798613245922007391139 6265197919868883011086709)
                    ·
                      refine ⟨587362304987707782289379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6265197919868883011086709 587362304987707782289379)
                      ·
                        rfl

theorem cell23_1143884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1143884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143884 prefixEnd_1143884 := by exact prefixLift 1143884
  have htrace : WordTrace (prefixWord ++ tailWord_1143884) baseStart_1143884 baseEnd_1143884 := by
    simpa [prefixWord, tailWord_1143884, baseEnd_1143884] using wordTrace_append hprefix tailTrace_1143884
  have hstable : (prefixWord ++ tailWord_1143884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143884).length < 2 ^ (prefixWord ++ tailWord_1143884).sum := by decide
  have hdescent : baseEnd_1143884 < baseStart_1143884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143885 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_1143885 : Nat := 118140960795 + 1143885 * 2 ^ 59
def prefixEnd_1143885 : Nat := 4983230072969 + 3 ^ 40 * 1143885 * 2
def baseEnd_1143885 : Nat := 587362818468362278376875

theorem tailTrace_1143885 : CollatzResearch.WordTrace tailWord_1143885 prefixEnd_1143885 587362818468362278376875 := by
  unfold tailWord_1143885
  simp only [CollatzResearch.WordTrace]
  refine ⟨41720913460907479849705109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27813942307271653233136739 41720913460907479849705109)
  ·
    refine ⟨1955667818480038117954927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41720913460907479849705109 1955667818480038117954927)
    ·
      refine ⟨2933501727720057176932391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955667818480038117954927 2933501727720057176932391)
      ·
        refine ⟨4400252591580085765398587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933501727720057176932391 4400252591580085765398587)
        ·
          refine ⟨6600378887370128648097881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4400252591580085765398587 6600378887370128648097881)
          ·
            refine ⟨4950284165527596486073411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6600378887370128648097881 4950284165527596486073411)
            ·
              refine ⟨7425426248291394729110117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950284165527596486073411 7425426248291394729110117)
              ·
                refine ⟨1392267421554636511708147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7425426248291394729110117 1392267421554636511708147)
                ·
                  refine ⟨2088401132331954767562221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392267421554636511708147 2088401132331954767562221)
                  ·
                    refine ⟨783150424624483037835833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088401132331954767562221 783150424624483037835833)
                    ·
                      refine ⟨587362818468362278376875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783150424624483037835833 587362818468362278376875)
                      ·
                        rfl

theorem cell23_1143885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_1143885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143885 prefixEnd_1143885 := by exact prefixLift 1143885
  have htrace : WordTrace (prefixWord ++ tailWord_1143885) baseStart_1143885 baseEnd_1143885 := by
    simpa [prefixWord, tailWord_1143885, baseEnd_1143885] using wordTrace_append hprefix tailTrace_1143885
  have hstable : (prefixWord ++ tailWord_1143885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143885).length < 2 ^ (prefixWord ++ tailWord_1143885).sum := by decide
  have hdescent : baseEnd_1143885 < baseStart_1143885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143971 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 6, 2]
def baseStart_1143971 : Nat := 118140960795 + 1143971 * 2 ^ 59
def prefixEnd_1143971 : Nat := 4983230072969 + 3 ^ 40 * 1143971 * 2
def baseEnd_1143971 : Nat := 587406977804648941901479

theorem tailTrace_1143971 : CollatzResearch.WordTrace tailWord_1143971 prefixEnd_1143971 587406977804648941901479 := by
  unfold tailWord_1143971
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724050138595916537335767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27816033425730611024890511 41724050138595916537335767)
  ·
    refine ⟨62586075207893874806003651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41724050138595916537335767 62586075207893874806003651)
    ·
      refine ⟨93879112811840812209005477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62586075207893874806003651 93879112811840812209005477)
      ·
        refine ⟨17602333652220152289188527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93879112811840812209005477 17602333652220152289188527)
        ·
          refine ⟨26403500478330228433782791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17602333652220152289188527 26403500478330228433782791)
          ·
            refine ⟨39605250717495342650674187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26403500478330228433782791 39605250717495342650674187)
            ·
              refine ⟨59407876076243013976011281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39605250717495342650674187 59407876076243013976011281)
              ·
                refine ⟨44555907057182260482008461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59407876076243013976011281 44555907057182260482008461)
                ·
                  refine ⟨16708465146443347680753173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44555907057182260482008461 16708465146443347680753173)
                  ·
                    refine ⟨783209303739531922535305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16708465146443347680753173 783209303739531922535305)
                    ·
                      refine ⟨587406977804648941901479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783209303739531922535305 587406977804648941901479)
                      ·
                        rfl

theorem cell23_1143971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_1143971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143971 prefixEnd_1143971 := by exact prefixLift 1143971
  have htrace : WordTrace (prefixWord ++ tailWord_1143971) baseStart_1143971 baseEnd_1143971 := by
    simpa [prefixWord, tailWord_1143971, baseEnd_1143971] using wordTrace_append hprefix tailTrace_1143971
  have hstable : (prefixWord ++ tailWord_1143971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143971).length < 2 ^ (prefixWord ++ tailWord_1143971).sum := by decide
  have hdescent : baseEnd_1143971 < baseStart_1143971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143978 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1143978 : Nat := 118140960795 + 1143978 * 2 ^ 59
def prefixEnd_1143978 : Nat := 4983230072969 + 3 ^ 40 * 1143978 * 2
def baseEnd_1143978 : Nat := 587410572169230414513947

theorem tailTrace_1143978 : CollatzResearch.WordTrace tailWord_1143978 prefixEnd_1143978 587410572169230414513947 := by
  unfold tailWord_1143978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431076362392639183210147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27816203633047037821893725 10431076362392639183210147)
  ·
    refine ⟨15646614543588958774815221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431076362392639183210147 15646614543588958774815221)
    ·
      refine ⟨1466870113461464885138927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15646614543588958774815221 1466870113461464885138927)
      ·
        refine ⟨2200305170192197327708391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1466870113461464885138927 2200305170192197327708391)
        ·
          refine ⟨3300457755288295991562587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200305170192197327708391 3300457755288295991562587)
          ·
            refine ⟨4950686632932443987343881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300457755288295991562587 4950686632932443987343881)
            ·
              refine ⟨3713014974699332990507911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4950686632932443987343881 3713014974699332990507911)
              ·
                refine ⟨5569522462048999485761867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713014974699332990507911 5569522462048999485761867)
                ·
                  refine ⟨8354283693073499228642801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569522462048999485761867 8354283693073499228642801)
                  ·
                    refine ⟨6265712769805124421482101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8354283693073499228642801 6265712769805124421482101)
                    ·
                      refine ⟨587410572169230414513947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6265712769805124421482101 587410572169230414513947)
                      ·
                        rfl

theorem cell23_1143978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1143978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143978 prefixEnd_1143978 := by exact prefixLift 1143978
  have htrace : WordTrace (prefixWord ++ tailWord_1143978) baseStart_1143978 baseEnd_1143978 := by
    simpa [prefixWord, tailWord_1143978, baseEnd_1143978] using wordTrace_append hprefix tailTrace_1143978
  have hstable : (prefixWord ++ tailWord_1143978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143978).length < 2 ^ (prefixWord ++ tailWord_1143978).sum := by decide
  have hdescent : baseEnd_1143978 < baseStart_1143978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143984 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_1143984 : Nat := 118140960795 + 1143984 * 2 ^ 59
def prefixEnd_1143984 : Nat := 4983230072969 + 3 ^ 40 * 1143984 * 2
def baseEnd_1143984 : Nat := 587413653053157391038919

theorem tailTrace_1143984 : CollatzResearch.WordTrace tailWord_1143984 prefixEnd_1143984 587413653053157391038919 := by
  unfold tailWord_1143984
  simp only [CollatzResearch.WordTrace]
  refine ⟨20862262143774409878779503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27816349525032546505039337 20862262143774409878779503)
  ·
    refine ⟨31293393215661614818169255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20862262143774409878779503 31293393215661614818169255)
    ·
      refine ⟨46940089823492422227253883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31293393215661614818169255 46940089823492422227253883)
      ·
        refine ⟨70410134735238633340880825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46940089823492422227253883 70410134735238633340880825)
        ·
          refine ⟨52807601051428975005660619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70410134735238633340880825 52807601051428975005660619)
          ·
            refine ⟨79211401577143462508490929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52807601051428975005660619 79211401577143462508490929)
            ·
              refine ⟨59408551182857596881368197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79211401577143462508490929 59408551182857596881368197)
              ·
                refine ⟨11139103346785799415256537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59408551182857596881368197 11139103346785799415256537)
                ·
                  refine ⟨8354327510089349561442403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11139103346785799415256537 8354327510089349561442403)
                  ·
                    refine ⟨12531491265134024342163605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8354327510089349561442403 12531491265134024342163605)
                    ·
                      refine ⟨587413653053157391038919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12531491265134024342163605 587413653053157391038919)
                      ·
                        rfl

theorem cell23_1143984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_1143984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143984 prefixEnd_1143984 := by exact prefixLift 1143984
  have htrace : WordTrace (prefixWord ++ tailWord_1143984) baseStart_1143984 baseEnd_1143984 := by
    simpa [prefixWord, tailWord_1143984, baseEnd_1143984] using wordTrace_append hprefix tailTrace_1143984
  have hstable : (prefixWord ++ tailWord_1143984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143984).length < 2 ^ (prefixWord ++ tailWord_1143984).sum := by decide
  have hdescent : baseEnd_1143984 < baseStart_1143984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143991 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3]
def baseStart_1143991 : Nat := 118140960795 + 1143991 * 2 ^ 59
def prefixEnd_1143991 : Nat := 4983230072969 + 3 ^ 40 * 1143991 * 2
def baseEnd_1143991 : Nat := 587417247417738863651387

theorem tailTrace_1143991 : CollatzResearch.WordTrace tailWord_1143991 prefixEnd_1143991 587417247417738863651387 := by
  unfold tailWord_1143991
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724779598523459953063827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27816519732348973302042551 41724779598523459953063827)
  ·
    refine ⟨62587169397785189929595741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41724779598523459953063827 62587169397785189929595741)
    ·
      refine ⟨23470188524169446223598403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62587169397785189929595741 23470188524169446223598403)
      ·
        refine ⟨35205282786254169335397605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23470188524169446223598403 35205282786254169335397605)
        ·
          refine ⟨6600990522422656750387051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35205282786254169335397605 6600990522422656750387051)
          ·
            refine ⟨9901485783633985125580577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6600990522422656750387051 9901485783633985125580577)
            ·
              refine ⟨7426114337725488844185433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9901485783633985125580577 7426114337725488844185433)
              ·
                refine ⟨5569585753294116633139075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7426114337725488844185433 5569585753294116633139075)
                ·
                  refine ⟨8354378629941174949708613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569585753294116633139075 8354378629941174949708613)
                  ·
                    refine ⟨1566445993113970303070365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8354378629941174949708613 1566445993113970303070365)
                    ·
                      refine ⟨587417247417738863651387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566445993113970303070365 587417247417738863651387)
                      ·
                        rfl

theorem cell23_1143991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_1143991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143991 prefixEnd_1143991 := by exact prefixLift 1143991
  have htrace : WordTrace (prefixWord ++ tailWord_1143991) baseStart_1143991 baseEnd_1143991 := by
    simpa [prefixWord, tailWord_1143991, baseEnd_1143991] using wordTrace_append hprefix tailTrace_1143991
  have hstable : (prefixWord ++ tailWord_1143991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143991).length < 2 ^ (prefixWord ++ tailWord_1143991).sum := by decide
  have hdescent : baseEnd_1143991 < baseStart_1143991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143994 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 10]
def baseStart_1143994 : Nat := 118140960795 + 1143994 * 2 ^ 59
def prefixEnd_1143994 : Nat := 4983230072969 + 3 ^ 40 * 1143994 * 2
def baseEnd_1143994 : Nat := 65268754206633594657097

theorem tailTrace_1143994 : CollatzResearch.WordTrace tailWord_1143994 prefixEnd_1143994 65268754206633594657097 := by
  unfold tailWord_1143994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431222254378147866355759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27816592678341727643615357 10431222254378147866355759)
  ·
    refine ⟨15646833381567221799533639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431222254378147866355759 15646833381567221799533639)
    ·
      refine ⟨23470250072350832699300459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15646833381567221799533639 23470250072350832699300459)
      ·
        refine ⟨35205375108526249048950689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23470250072350832699300459 35205375108526249048950689)
        ·
          refine ⟨26404031331394686786713017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35205375108526249048950689 26404031331394686786713017)
          ·
            refine ⟨19803023498546015090034763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26404031331394686786713017 19803023498546015090034763)
            ·
              refine ⟨29704535247819022635052145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19803023498546015090034763 29704535247819022635052145)
              ·
                refine ⟨22278401435864266976289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29704535247819022635052145 22278401435864266976289109)
                ·
                  refine ⟨65268754206633594657097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 22278401435864266976289109 65268754206633594657097)
                  ·
                    rfl

theorem cell23_1143994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 10].length) (baseStart_1143994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143994 prefixEnd_1143994 := by exact prefixLift 1143994
  have htrace : WordTrace (prefixWord ++ tailWord_1143994) baseStart_1143994 baseEnd_1143994 := by
    simpa [prefixWord, tailWord_1143994, baseEnd_1143994] using wordTrace_append hprefix tailTrace_1143994
  have hstable : (prefixWord ++ tailWord_1143994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143994).length < 2 ^ (prefixWord ++ tailWord_1143994).sum := by decide
  have hdescent : baseEnd_1143994 < baseStart_1143994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1143998 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1143998 : Nat := 118140960795 + 1143998 * 2 ^ 59
def prefixEnd_1143998 : Nat := 4983230072969 + 3 ^ 40 * 1143998 * 2
def baseEnd_1143998 : Nat := 195806947260773445421285

theorem tailTrace_1143998 : CollatzResearch.WordTrace tailWord_1143998 prefixEnd_1143998 195806947260773445421285 := by
  unfold tailWord_1143998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5215629363687262518571081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27816689939665400099045765 5215629363687262518571081)
  ·
    refine ⟨3911722022765446888928311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5215629363687262518571081 3911722022765446888928311)
    ·
      refine ⟨5867583034148170333392467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911722022765446888928311 5867583034148170333392467)
      ·
        refine ⟨8801374551222255500088701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5867583034148170333392467 8801374551222255500088701)
        ·
          refine ⟨3300515456708345812533263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8801374551222255500088701 3300515456708345812533263)
          ·
            refine ⟨4950773185062518718799895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300515456708345812533263 4950773185062518718799895)
            ·
              refine ⟨7426159777593778078199843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4950773185062518718799895 7426159777593778078199843)
              ·
                refine ⟨11139239666390667117299765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7426159777593778078199843 11139239666390667117299765)
                ·
                  refine ⟨1044303718724125042246853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11139239666390667117299765 1044303718724125042246853)
                  ·
                    refine ⟨195806947260773445421285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044303718724125042246853 195806947260773445421285)
                    ·
                      rfl

theorem cell23_1143998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1143998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1143998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1143998 prefixEnd_1143998 := by exact prefixLift 1143998
  have htrace : WordTrace (prefixWord ++ tailWord_1143998) baseStart_1143998 baseEnd_1143998 := by
    simpa [prefixWord, tailWord_1143998, baseEnd_1143998] using wordTrace_append hprefix tailTrace_1143998
  have hstable : (prefixWord ++ tailWord_1143998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1143998).length < 2 ^ (prefixWord ++ tailWord_1143998).sum := by decide
  have hdescent : baseEnd_1143998 < baseStart_1143998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1143998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144008 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_1144008 : Nat := 118140960795 + 1144008 * 2 ^ 59
def prefixEnd_1144008 : Nat := 4983230072969 + 3 ^ 40 * 1144008 * 2
def baseEnd_1144008 : Nat := 587425976588865297138809

theorem tailTrace_1144008 : CollatzResearch.WordTrace tailWord_1144008 prefixEnd_1144008 587425976588865297138809 := by
  unfold tailWord_1144008
  simp only [CollatzResearch.WordTrace]
  refine ⟨20862699819730935928216339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27816933092974581237621785 20862699819730935928216339)
  ·
    refine ⟨31294049729596403892324509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20862699819730935928216339 31294049729596403892324509)
    ·
      refine ⟨11735268648598651459621691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31294049729596403892324509 11735268648598651459621691)
      ·
        refine ⟨17602902972897977189432537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11735268648598651459621691 17602902972897977189432537)
        ·
          refine ⟨13202177229673482892074403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17602902972897977189432537 13202177229673482892074403)
          ·
            refine ⟨19803265844510224338111605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13202177229673482892074403 19803265844510224338111605)
            ·
              refine ⟨1856556172922833531697963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19803265844510224338111605 1856556172922833531697963)
              ·
                refine ⟨2784834259384250297546945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856556172922833531697963 2784834259384250297546945)
                ·
                  refine ⟨2088625694538187723160209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2784834259384250297546945 2088625694538187723160209)
                  ·
                    refine ⟨1566469270903640792370157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088625694538187723160209 1566469270903640792370157)
                    ·
                      refine ⟨587425976588865297138809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566469270903640792370157 587425976588865297138809)
                      ·
                        rfl

theorem cell23_1144008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_1144008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144008 prefixEnd_1144008 := by exact prefixLift 1144008
  have htrace : WordTrace (prefixWord ++ tailWord_1144008) baseStart_1144008 baseEnd_1144008 := by
    simpa [prefixWord, tailWord_1144008, baseEnd_1144008] using wordTrace_append hprefix tailTrace_1144008
  have hstable : (prefixWord ++ tailWord_1144008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144008).length < 2 ^ (prefixWord ++ tailWord_1144008).sum := by decide
  have hdescent : baseEnd_1144008 < baseStart_1144008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144045 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 6]
def baseStart_1144045 : Nat := 118140960795 + 1144045 * 2 ^ 59
def prefixEnd_1144045 : Nat := 4983230072969 + 3 ^ 40 * 1144045 * 2
def baseEnd_1144045 : Nat := 65271663930342405819571

theorem tailTrace_1144045 : CollatzResearch.WordTrace tailWord_1144045 prefixEnd_1144045 65271663930342405819571 := by
  unfold tailWord_1144045
  simp only [CollatzResearch.WordTrace]
  refine ⟨41726749140327827175529589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27817832760218551450353059 41726749140327827175529589)
  ·
    refine ⟨3911882731905733797705899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41726749140327827175529589 3911882731905733797705899)
    ·
      refine ⟨5867824097858600696558849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3911882731905733797705899 5867824097858600696558849)
      ·
        refine ⟨4400868073393950522419137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5867824097858600696558849 4400868073393950522419137)
        ·
          refine ⟨3300651055045462891814353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4400868073393950522419137 3300651055045462891814353)
          ·
            refine ⟨2475488291284097168860765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3300651055045462891814353 2475488291284097168860765)
            ·
              refine ⟨928308109231536438322787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2475488291284097168860765 928308109231536438322787)
              ·
                refine ⟨1392462163847304657484181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 928308109231536438322787 1392462163847304657484181)
                ·
                  refine ⟨65271663930342405819571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1392462163847304657484181 65271663930342405819571)
                  ·
                    rfl

theorem cell23_1144045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_1144045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144045 prefixEnd_1144045 := by exact prefixLift 1144045
  have htrace : WordTrace (prefixWord ++ tailWord_1144045) baseStart_1144045 baseEnd_1144045 := by
    simpa [prefixWord, tailWord_1144045, baseEnd_1144045] using wordTrace_append hprefix tailTrace_1144045
  have hstable : (prefixWord ++ tailWord_1144045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144045).length < 2 ^ (prefixWord ++ tailWord_1144045).sum := by decide
  have hdescent : baseEnd_1144045 < baseStart_1144045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144058 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_1144058 : Nat := 118140960795 + 1144058 * 2 ^ 59
def prefixEnd_1144058 : Nat := 4983230072969 + 3 ^ 40 * 1144058 * 2
def baseEnd_1144058 : Nat := 195817216873863367171193

theorem tailTrace_1144058 : CollatzResearch.WordTrace tailWord_1144058 prefixEnd_1144058 195817216873863367171193 := by
  unfold tailWord_1144058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431805822320182598938207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27818148859520486930501885 10431805822320182598938207)
  ·
    refine ⟨15647708733480273898407311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10431805822320182598938207 15647708733480273898407311)
    ·
      refine ⟨23471563100220410847610967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15647708733480273898407311 23471563100220410847610967)
      ·
        refine ⟨35207344650330616271416451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23471563100220410847610967 35207344650330616271416451)
        ·
          refine ⟨52811016975495924407124677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35207344650330616271416451 52811016975495924407124677)
          ·
            refine ⟨9902065682905485826335877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52811016975495924407124677 9902065682905485826335877)
            ·
              refine ⟨1856637315544778592437977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9902065682905485826335877 1856637315544778592437977)
              ·
                refine ⟨1392477986658583944328483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856637315544778592437977 1392477986658583944328483)
                ·
                  refine ⟨2088716979987875916492725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392477986658583944328483 2088716979987875916492725)
                  ·
                    refine ⟨195817216873863367171193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2088716979987875916492725 195817216873863367171193)
                    ·
                      rfl

theorem cell23_1144058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_1144058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144058 prefixEnd_1144058 := by exact prefixLift 1144058
  have htrace : WordTrace (prefixWord ++ tailWord_1144058) baseStart_1144058 baseEnd_1144058 := by
    simpa [prefixWord, tailWord_1144058, baseEnd_1144058] using wordTrace_append hprefix tailTrace_1144058
  have hstable : (prefixWord ++ tailWord_1144058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144058).length < 2 ^ (prefixWord ++ tailWord_1144058).sum := by decide
  have hdescent : baseEnd_1144058 < baseStart_1144058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144066 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_1144066 : Nat := 118140960795 + 1144066 * 2 ^ 59
def prefixEnd_1144066 : Nat := 4983230072969 + 3 ^ 40 * 1144066 * 2
def baseEnd_1144066 : Nat := 195818586155608690071181

theorem tailTrace_1144066 : CollatzResearch.WordTrace tailWord_1144066 prefixEnd_1144066 195818586155608690071181 := by
  unfold tailWord_1144066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10431878768312936940511013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27818343382167831841362701 10431878768312936940511013)
  ·
    refine ⟨1955977269058675676345815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10431878768312936940511013 1955977269058675676345815)
    ·
      refine ⟨2933965903588013514518723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1955977269058675676345815 2933965903588013514518723)
      ·
        refine ⟨4400948855382020271778085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2933965903588013514518723 4400948855382020271778085)
        ·
          refine ⟨825177910384128800958391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4400948855382020271778085 825177910384128800958391)
          ·
            refine ⟨1237766865576193201437587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 825177910384128800958391 1237766865576193201437587)
            ·
              refine ⟨1856650298364289802156381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237766865576193201437587 1856650298364289802156381)
              ·
                refine ⟨696243861886608675808643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1856650298364289802156381 696243861886608675808643)
                ·
                  refine ⟨1044365792829913013712965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696243861886608675808643 1044365792829913013712965)
                  ·
                    refine ⟨195818586155608690071181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044365792829913013712965 195818586155608690071181)
                    ·
                      rfl

theorem cell23_1144066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_1144066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144066 prefixEnd_1144066 := by exact prefixLift 1144066
  have htrace : WordTrace (prefixWord ++ tailWord_1144066) baseStart_1144066 baseEnd_1144066 := by
    simpa [prefixWord, tailWord_1144066, baseEnd_1144066] using wordTrace_append hprefix tailTrace_1144066
  have hstable : (prefixWord ++ tailWord_1144066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144066).length < 2 ^ (prefixWord ++ tailWord_1144066).sum := by decide
  have hdescent : baseEnd_1144066 < baseStart_1144066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144088 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_1144088 : Nat := 118140960795 + 1144088 * 2 ^ 59
def prefixEnd_1144088 : Nat := 4983230072969 + 3 ^ 40 * 1144088 * 2
def baseEnd_1144088 : Nat := 195822351680408328046147

theorem tailTrace_1144088 : CollatzResearch.WordTrace tailWord_1144088 prefixEnd_1144088 195822351680408328046147 := by
  unfold tailWord_1144088
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864158739586022759672459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27818878319448030346229945 20864158739586022759672459)
  ·
    refine ⟨31296238109379034139508689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20864158739586022759672459 31296238109379034139508689)
    ·
      refine ⟨23472178582034275604631517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31296238109379034139508689 23472178582034275604631517)
      ·
        refine ⟨8802066968262853351736819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23472178582034275604631517 8802066968262853351736819)
        ·
          refine ⟨13203100452394280027605229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8802066968262853351736819 13203100452394280027605229)
          ·
            refine ⟨4951162669647855010351961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13203100452394280027605229 4951162669647855010351961)
            ·
              refine ⟨3713372002235891257763971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4951162669647855010351961 3713372002235891257763971)
              ·
                refine ⟨5570058003353836886645957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713372002235891257763971 5570058003353836886645957)
                ·
                  refine ⟨1044385875628844416246117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5570058003353836886645957 1044385875628844416246117)
                  ·
                    refine ⟨195822351680408328046147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1044385875628844416246117 195822351680408328046147)
                    ·
                      rfl

theorem cell23_1144088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_1144088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144088 prefixEnd_1144088 := by exact prefixLift 1144088
  have htrace : WordTrace (prefixWord ++ tailWord_1144088) baseStart_1144088 baseEnd_1144088 := by
    simpa [prefixWord, tailWord_1144088, baseEnd_1144088] using wordTrace_append hprefix tailTrace_1144088
  have hstable : (prefixWord ++ tailWord_1144088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144088).length < 2 ^ (prefixWord ++ tailWord_1144088).sum := by decide
  have hdescent : baseEnd_1144088 < baseStart_1144088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144101 : List Nat := [1, 3, 1, 2, 4, 1, 1, 10]
def baseStart_1144101 : Nat := 118140960795 + 1144101 * 2 ^ 59
def prefixEnd_1144101 : Nat := 4983230072969 + 3 ^ 40 * 1144101 * 2
def baseEnd_1144101 : Nat := 21758286307027164195403

theorem tailTrace_1144101 : CollatzResearch.WordTrace tailWord_1144101 prefixEnd_1144101 21758286307027164195403 := by
  unfold tailWord_1144101
  simp only [CollatzResearch.WordTrace]
  refine ⟨41728791628124948739568157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27819194418749965826378771 41728791628124948739568157)
  ·
    refine ⟨15648296860546855777338059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41728791628124948739568157 15648296860546855777338059)
    ·
      refine ⟨23472445290820283666007089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15648296860546855777338059 23472445290820283666007089)
      ·
        refine ⟨17604333968115212749505317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23472445290820283666007089 17604333968115212749505317)
        ·
          refine ⟨3300812619021602390532247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17604333968115212749505317 3300812619021602390532247)
          ·
            refine ⟨4951218928532403585798371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3300812619021602390532247 4951218928532403585798371)
            ·
              refine ⟨7426828392798605378697557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951218928532403585798371 7426828392798605378697557)
              ·
                refine ⟨21758286307027164195403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7426828392798605378697557 21758286307027164195403)
                ·
                  rfl

theorem cell23_1144101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 10].length) (baseStart_1144101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144101 prefixEnd_1144101 := by exact prefixLift 1144101
  have htrace : WordTrace (prefixWord ++ tailWord_1144101) baseStart_1144101 baseEnd_1144101 := by
    simpa [prefixWord, tailWord_1144101, baseEnd_1144101] using wordTrace_append hprefix tailTrace_1144101
  have hstable : (prefixWord ++ tailWord_1144101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144101).length < 2 ^ (prefixWord ++ tailWord_1144101).sum := by decide
  have hdescent : baseEnd_1144101 < baseStart_1144101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144115 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 3]
def baseStart_1144115 : Nat := 118140960795 + 1144115 * 2 ^ 59
def prefixEnd_1144115 : Nat := 4983230072969 + 3 ^ 40 * 1144115 * 2
def baseEnd_1144115 : Nat := 587480919018896378500817

theorem tailTrace_1144115 : CollatzResearch.WordTrace tailWord_1144115 prefixEnd_1144115 587480919018896378500817 := by
  unfold tailWord_1144115
  simp only [CollatzResearch.WordTrace]
  refine ⟨41729302250074229130577799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27819534833382819420385199 41729302250074229130577799)
  ·
    refine ⟨62593953375111343695866699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41729302250074229130577799 62593953375111343695866699)
    ·
      refine ⟨93890930062667015543800049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62593953375111343695866699 93890930062667015543800049)
      ·
        refine ⟨70418197547000261657850037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93890930062667015543800049 70418197547000261657850037)
        ·
          refine ⟨6601706020031274530423441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70418197547000261657850037 6601706020031274530423441)
          ·
            refine ⟨4951279515023455897817581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6601706020031274530423441 4951279515023455897817581)
            ·
              refine ⟨1856729818133795961681593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4951279515023455897817581 1856729818133795961681593)
              ·
                refine ⟨1392547363600346971261195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856729818133795961681593 1392547363600346971261195)
                ·
                  refine ⟨2088821045400520456891793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392547363600346971261195 2088821045400520456891793)
                  ·
                    refine ⟨1566615784050390342668845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2088821045400520456891793 1566615784050390342668845)
                    ·
                      refine ⟨587480919018896378500817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566615784050390342668845 587480919018896378500817)
                      ·
                        rfl

theorem cell23_1144115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_1144115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144115 prefixEnd_1144115 := by exact prefixLift 1144115
  have htrace : WordTrace (prefixWord ++ tailWord_1144115) baseStart_1144115 baseEnd_1144115 := by
    simpa [prefixWord, tailWord_1144115, baseEnd_1144115] using wordTrace_append hprefix tailTrace_1144115
  have hstable : (prefixWord ++ tailWord_1144115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144115).length < 2 ^ (prefixWord ++ tailWord_1144115).sum := by decide
  have hdescent : baseEnd_1144115 < baseStart_1144115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144128 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_1144128 : Nat := 118140960795 + 1144128 * 2 ^ 59
def prefixEnd_1144128 : Nat := 4983230072969 + 3 ^ 40 * 1144128 * 2
def baseEnd_1144128 : Nat := 587487594267404827638257

theorem tailTrace_1144128 : CollatzResearch.WordTrace tailWord_1144128 prefixEnd_1144128 587487594267404827638257 := by
  unfold tailWord_1144128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864888199513566175400519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27819850932684754900534025 20864888199513566175400519)
  ·
    refine ⟨31297332299270349263100779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20864888199513566175400519 31297332299270349263100779)
    ·
      refine ⟨46945998448905523894651169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31297332299270349263100779 46945998448905523894651169)
      ·
        refine ⟨35209498836679142920988377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46945998448905523894651169 35209498836679142920988377)
        ·
          refine ⟨26407124127509357190741283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35209498836679142920988377 26407124127509357190741283)
          ·
            refine ⟨39610686191264035786111925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26407124127509357190741283 39610686191264035786111925)
            ·
              refine ⟨3713501830431003354947993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39610686191264035786111925 3713501830431003354947993)
              ·
                refine ⟨2785126372823252516210995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3713501830431003354947993 2785126372823252516210995)
                ·
                  refine ⟨4177689559234878774316493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785126372823252516210995 4177689559234878774316493)
                  ·
                    refine ⟨1566633584713079540368685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4177689559234878774316493 1566633584713079540368685)
                    ·
                      refine ⟨587487594267404827638257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566633584713079540368685 587487594267404827638257)
                      ·
                        rfl

theorem cell23_1144128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_1144128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144128 prefixEnd_1144128 := by exact prefixLift 1144128
  have htrace : WordTrace (prefixWord ++ tailWord_1144128) baseStart_1144128 baseEnd_1144128 := by
    simpa [prefixWord, tailWord_1144128, baseEnd_1144128] using wordTrace_append hprefix tailTrace_1144128
  have hstable : (prefixWord ++ tailWord_1144128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144128).length < 2 ^ (prefixWord ++ tailWord_1144128).sum := by decide
  have hdescent : baseEnd_1144128 < baseStart_1144128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144132 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_1144132 : Nat := 118140960795 + 1144132 * 2 ^ 59
def prefixEnd_1144132 : Nat := 4983230072969 + 3 ^ 40 * 1144132 * 2
def baseEnd_1144132 : Nat := 587489648190022811988239

theorem tailTrace_1144132 : CollatzResearch.WordTrace tailWord_1144132 prefixEnd_1144132 587489648190022811988239 := by
  unfold tailWord_1144132
  simp only [CollatzResearch.WordTrace]
  refine ⟨20864961145506320516973325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27819948194008427355964433 20864961145506320516973325)
  ·
    refine ⟨7824360429564870193864997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20864961145506320516973325 7824360429564870193864997)
    ·
      refine ⟨1467067580543413161349687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7824360429564870193864997 1467067580543413161349687)
      ·
        refine ⟨2200601370815119742024531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1467067580543413161349687 2200601370815119742024531)
        ·
          refine ⟨3300902056222679613036797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2200601370815119742024531 3300902056222679613036797)
          ·
            refine ⟨1237838271083504854888799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3300902056222679613036797 1237838271083504854888799)
            ·
              refine ⟨1856757406625257282333199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1237838271083504854888799 1856757406625257282333199)
              ·
                refine ⟨2785136109937885923499799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856757406625257282333199 2785136109937885923499799)
                ·
                  refine ⟨4177704164906828885249699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785136109937885923499799 4177704164906828885249699)
                  ·
                    refine ⟨6266556247360243327874549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4177704164906828885249699 6266556247360243327874549)
                    ·
                      refine ⟨587489648190022811988239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6266556247360243327874549 587489648190022811988239)
                      ·
                        rfl

theorem cell23_1144132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_1144132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144132 prefixEnd_1144132 := by exact prefixLift 1144132
  have htrace : WordTrace (prefixWord ++ tailWord_1144132) baseStart_1144132 baseEnd_1144132 := by
    simpa [prefixWord, tailWord_1144132, baseEnd_1144132] using wordTrace_append hprefix tailTrace_1144132
  have hstable : (prefixWord ++ tailWord_1144132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144132).length < 2 ^ (prefixWord ++ tailWord_1144132).sum := by decide
  have hdescent : baseEnd_1144132 < baseStart_1144132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144162 : List Nat := [3, 3, 2, 1, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1144162 : Nat := 118140960795 + 1144162 * 2 ^ 59
def prefixEnd_1144162 : Nat := 4983230072969 + 3 ^ 40 * 1144162 * 2
def baseEnd_1144162 : Nat := 587505052609657694613101

theorem tailTrace_1144162 : CollatzResearch.WordTrace tailWord_1144162 prefixEnd_1144162 587505052609657694613101 := by
  unfold tailWord_1144162
  simp only [CollatzResearch.WordTrace]
  refine ⟨10432754120225989039384685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27820677653935970771692493 10432754120225989039384685)
  ·
    refine ⟨3912282795084745889769257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10432754120225989039384685 3912282795084745889769257)
    ·
      refine ⟨2934212096313559417326943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3912282795084745889769257 2934212096313559417326943)
      ·
        refine ⟨4401318144470339125990415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934212096313559417326943 4401318144470339125990415)
        ·
          refine ⟨6601977216705508688985623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401318144470339125990415 6601977216705508688985623)
          ·
            refine ⟨9902965825058263033478435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6601977216705508688985623 9902965825058263033478435)
            ·
              refine ⟨14854448737587394550217653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9902965825058263033478435 14854448737587394550217653)
              ·
                refine ⟨1392604569148818239082905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14854448737587394550217653 1392604569148818239082905)
                ·
                  refine ⟨1044453426861613679312179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1392604569148818239082905 1044453426861613679312179)
                  ·
                    refine ⟨1566680140292420518968269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1044453426861613679312179 1566680140292420518968269)
                    ·
                      refine ⟨587505052609657694613101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1566680140292420518968269 587505052609657694613101)
                      ·
                        rfl

theorem cell23_1144162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1144162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144162 prefixEnd_1144162 := by exact prefixLift 1144162
  have htrace : WordTrace (prefixWord ++ tailWord_1144162) baseStart_1144162 baseEnd_1144162 := by
    simpa [prefixWord, tailWord_1144162, baseEnd_1144162] using wordTrace_append hprefix tailTrace_1144162
  have hstable : (prefixWord ++ tailWord_1144162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144162).length < 2 ^ (prefixWord ++ tailWord_1144162).sum := by decide
  have hdescent : baseEnd_1144162 < baseStart_1144162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144185 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 1, 4, 2]
def baseStart_1144185 : Nat := 118140960795 + 1144185 * 2 ^ 59
def prefixEnd_1144185 : Nat := 4983230072969 + 3 ^ 40 * 1144185 * 2
def baseEnd_1144185 : Nat := 587516862664711104625495

theorem tailTrace_1144185 : CollatzResearch.WordTrace tailWord_1144185 prefixEnd_1144185 587516862664711104625495 := by
  unfold tailWord_1144185
  simp only [CollatzResearch.WordTrace]
  refine ⟨41731855359820631085626009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27821236906547087390417339 41731855359820631085626009)
  ·
    refine ⟨31298891519865473314219507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41731855359820631085626009 31298891519865473314219507)
    ·
      refine ⟨46948337279798209971329261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31298891519865473314219507 46948337279798209971329261)
      ·
        refine ⟨17605626479924328739248473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46948337279798209971329261 17605626479924328739248473)
        ·
          refine ⟨13204219859943246554436355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17605626479924328739248473 13204219859943246554436355)
          ·
            refine ⟨19806329789914869831654533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13204219859943246554436355 19806329789914869831654533)
            ·
              refine ⟨3713686835609038093435225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19806329789914869831654533 3713686835609038093435225)
              ·
                refine ⟨2785265126706778570076419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3713686835609038093435225 2785265126706778570076419)
                ·
                  refine ⟨4177897690060167855114629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785265126706778570076419 4177897690060167855114629)
                  ·
                    refine ⟨783355816886281472833993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177897690060167855114629 783355816886281472833993)
                    ·
                      refine ⟨587516862664711104625495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783355816886281472833993 587516862664711104625495)
                      ·
                        rfl

theorem cell23_1144185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_1144185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144185 prefixEnd_1144185 := by exact prefixLift 1144185
  have htrace : WordTrace (prefixWord ++ tailWord_1144185) baseStart_1144185 baseEnd_1144185 := by
    simpa [prefixWord, tailWord_1144185, baseEnd_1144185] using wordTrace_append hprefix tailTrace_1144185
  have hstable : (prefixWord ++ tailWord_1144185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144185).length < 2 ^ (prefixWord ++ tailWord_1144185).sum := by decide
  have hdescent : baseEnd_1144185 < baseStart_1144185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144362 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1144362 : Nat := 118140960795 + 1144362 * 2 ^ 59
def prefixEnd_1144362 : Nat := 4983230072969 + 3 ^ 40 * 1144362 * 2
def baseEnd_1144362 : Nat := 195869249580185637370727

theorem tailTrace_1144362 : CollatzResearch.WordTrace tailWord_1144362 prefixEnd_1144362 195869249580185637370727 := by
  unfold tailWord_1144362
  simp only [CollatzResearch.WordTrace]
  refine ⟨10434577770044847578704835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27825540720119593543212893 10434577770044847578704835)
  ·
    refine ⟨15651866655067271368057253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10434577770044847578704835 15651866655067271368057253)
    ·
      refine ⟨2934724997825113381510735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15651866655067271368057253 2934724997825113381510735)
      ·
        refine ⟨4402087496737670072266103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2934724997825113381510735 4402087496737670072266103)
        ·
          refine ⟨6603131245106505108399155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402087496737670072266103 6603131245106505108399155)
          ·
            refine ⟨9904696867659757662598733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6603131245106505108399155 9904696867659757662598733)
            ·
              refine ⟨3714261325372409123474525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9904696867659757662598733 3714261325372409123474525)
              ·
                refine ⟨1392847997014653421302947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714261325372409123474525 1392847997014653421302947)
                ·
                  refine ⟨2089271995521980131954421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392847997014653421302947 2089271995521980131954421)
                  ·
                    refine ⟨195869249580185637370727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2089271995521980131954421 195869249580185637370727)
                    ·
                      rfl

theorem cell23_1144362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1144362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144362 prefixEnd_1144362 := by exact prefixLift 1144362
  have htrace : WordTrace (prefixWord ++ tailWord_1144362) baseStart_1144362 baseEnd_1144362 := by
    simpa [prefixWord, tailWord_1144362, baseEnd_1144362] using wordTrace_append hprefix tailTrace_1144362
  have hstable : (prefixWord ++ tailWord_1144362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144362).length < 2 ^ (prefixWord ++ tailWord_1144362).sum := by decide
  have hdescent : baseEnd_1144362 < baseStart_1144362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144495 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 7]
def baseStart_1144495 : Nat := 118140960795 + 1144495 * 2 ^ 59
def prefixEnd_1144495 : Nat := 4983230072969 + 3 ^ 40 * 1144495 * 2
def baseEnd_1144495 : Nat := 65297337963067210194341

theorem tailTrace_1144495 : CollatzResearch.WordTrace tailWord_1144495 prefixEnd_1144495 65297337963067210194341 := by
  unfold tailWord_1144495
  simp only [CollatzResearch.WordTrace]
  refine ⟨41743161988697554029410939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27828774659131702686273959 41743161988697554029410939)
  ·
    refine ⟨62614742983046331044116409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41743161988697554029410939 62614742983046331044116409)
    ·
      refine ⟨46961057237284748283087307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62614742983046331044116409 46961057237284748283087307)
      ·
        refine ⟨70441585855927122424630961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46961057237284748283087307 70441585855927122424630961)
        ·
          refine ⟨52831189391945341818473221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70441585855927122424630961 52831189391945341818473221)
          ·
            refine ⟨9905848010989751590963729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52831189391945341818473221 9905848010989751590963729)
            ·
              refine ⟨7429386008242313693222797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9905848010989751590963729 7429386008242313693222797)
              ·
                refine ⟨2786019753090867634958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7429386008242313693222797 2786019753090867634958549)
                ·
                  refine ⟨65297337963067210194341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2786019753090867634958549 65297337963067210194341)
                  ·
                    rfl

theorem cell23_1144495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 7].length) (baseStart_1144495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144495 prefixEnd_1144495 := by exact prefixLift 1144495
  have htrace : WordTrace (prefixWord ++ tailWord_1144495) baseStart_1144495 baseEnd_1144495 := by
    simpa [prefixWord, tailWord_1144495, baseEnd_1144495] using wordTrace_append hprefix tailTrace_1144495
  have hstable : (prefixWord ++ tailWord_1144495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144495).length < 2 ^ (prefixWord ++ tailWord_1144495).sum := by decide
  have hdescent : baseEnd_1144495 < baseStart_1144495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144506 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2]
def baseStart_1144506 : Nat := 118140960795 + 1144506 * 2 ^ 59
def prefixEnd_1144506 : Nat := 4983230072969 + 3 ^ 40 * 1144506 * 2
def baseEnd_1144506 : Nat := 587681689954804348711519

theorem tailTrace_1144506 : CollatzResearch.WordTrace tailWord_1144506 prefixEnd_1144506 587681689954804348711519 := by
  unfold tailWord_1144506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10435890797914425727015343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27829042127771801938707581 10435890797914425727015343)
  ·
    refine ⟨15653836196871638590523015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10435890797914425727015343 15653836196871638590523015)
    ·
      refine ⟨23480754295307457885784523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15653836196871638590523015 23480754295307457885784523)
      ·
        refine ⟨35221131442961186828676785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23480754295307457885784523 35221131442961186828676785)
        ·
          refine ⟨26415848582220890121507589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35221131442961186828676785 26415848582220890121507589)
          ·
            refine ⟨4952971609166416897782673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26415848582220890121507589 4952971609166416897782673)
            ·
              refine ⟨3714728706874812673337005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952971609166416897782673 3714728706874812673337005)
              ·
                refine ⟨1393023265078054752501377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714728706874812673337005 1393023265078054752501377)
                ·
                  refine ⟨1044767448808541064376033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393023265078054752501377 1044767448808541064376033)
                  ·
                    refine ⟨783575586606405798282025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1044767448808541064376033 783575586606405798282025)
                    ·
                      refine ⟨587681689954804348711519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783575586606405798282025 587681689954804348711519)
                      ·
                        rfl

theorem cell23_1144506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2].length) (baseStart_1144506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144506 prefixEnd_1144506 := by exact prefixLift 1144506
  have htrace : WordTrace (prefixWord ++ tailWord_1144506) baseStart_1144506 baseEnd_1144506 := by
    simpa [prefixWord, tailWord_1144506, baseEnd_1144506] using wordTrace_append hprefix tailTrace_1144506
  have hstable : (prefixWord ++ tailWord_1144506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144506).length < 2 ^ (prefixWord ++ tailWord_1144506).sum := by decide
  have hdescent : baseEnd_1144506 < baseStart_1144506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144529 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 5]
def baseStart_1144529 : Nat := 118140960795 + 1144529 * 2 ^ 59
def prefixEnd_1144529 : Nat := 4983230072969 + 3 ^ 40 * 1144529 * 2
def baseEnd_1144529 : Nat := 65299277778873084302657

theorem tailTrace_1144529 : CollatzResearch.WordTrace tailWord_1144529 prefixEnd_1144529 65299277778873084302657 := by
  unfold tailWord_1144529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41744402070574377836148641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27829601380382918557432427 41744402070574377836148641)
  ·
    refine ⟨31308301552930783377111481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41744402070574377836148641 31308301552930783377111481)
    ·
      refine ⟨23481226164698087532833611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31308301552930783377111481 23481226164698087532833611)
      ·
        refine ⟨35221839247047131299250417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23481226164698087532833611 35221839247047131299250417)
        ·
          refine ⟨26416379435285348474437813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35221839247047131299250417 26416379435285348474437813)
          ·
            refine ⟨2476535572058001419478545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26416379435285348474437813 2476535572058001419478545)
            ·
              refine ⟨1857401679043501064608909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476535572058001419478545 1857401679043501064608909)
              ·
                refine ⟨696525629641312899228341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1857401679043501064608909 696525629641312899228341)
                ·
                  refine ⟨65299277778873084302657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 696525629641312899228341 65299277778873084302657)
                  ·
                    rfl

theorem cell23_1144529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 5].length) (baseStart_1144529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144529 prefixEnd_1144529 := by exact prefixLift 1144529
  have htrace : WordTrace (prefixWord ++ tailWord_1144529) baseStart_1144529 baseEnd_1144529 := by
    simpa [prefixWord, tailWord_1144529, baseEnd_1144529] using wordTrace_append hprefix tailTrace_1144529
  have hstable : (prefixWord ++ tailWord_1144529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144529).length < 2 ^ (prefixWord ++ tailWord_1144529).sum := by decide
  have hdescent : baseEnd_1144529 < baseStart_1144529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144562 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_1144562 : Nat := 118140960795 + 1144562 * 2 ^ 59
def prefixEnd_1144562 : Nat := 4983230072969 + 3 ^ 40 * 1144562 * 2
def baseEnd_1144562 : Nat := 587710444871456129611261

theorem tailTrace_1144562 : CollatzResearch.WordTrace tailWord_1144562 prefixEnd_1144562 587710444871456129611261 := by
  unfold tailWord_1144562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436401419863706118024985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27830403786303216314733293 10436401419863706118024985)
  ·
    refine ⟨7827301064897779588518739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10436401419863706118024985 7827301064897779588518739)
    ·
      refine ⟨11740951597346669382778109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7827301064897779588518739 11740951597346669382778109)
      ·
        refine ⟨4402856849005001018541791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11740951597346669382778109 4402856849005001018541791)
        ·
          refine ⟨6604285273507501527812687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402856849005001018541791 6604285273507501527812687)
          ·
            refine ⟨9906427910261252291719031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604285273507501527812687 9906427910261252291719031)
            ·
              refine ⟨14859641865391878437578547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9906427910261252291719031 14859641865391878437578547)
              ·
                refine ⟨22289462798087817656367821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14859641865391878437578547 22289462798087817656367821)
                ·
                  refine ⟨8358548549282931621137933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22289462798087817656367821 8358548549282931621137933)
                  ·
                    refine ⟨3134455705981099357926725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8358548549282931621137933 3134455705981099357926725)
                    ·
                      refine ⟨587710444871456129611261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3134455705981099357926725 587710444871456129611261)
                      ·
                        rfl

theorem cell23_1144562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_1144562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144562 prefixEnd_1144562 := by exact prefixLift 1144562
  have htrace : WordTrace (prefixWord ++ tailWord_1144562) baseStart_1144562 baseEnd_1144562 := by
    simpa [prefixWord, tailWord_1144562, baseEnd_1144562] using wordTrace_append hprefix tailTrace_1144562
  have hstable : (prefixWord ++ tailWord_1144562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144562).length < 2 ^ (prefixWord ++ tailWord_1144562).sum := by decide
  have hdescent : baseEnd_1144562 < baseStart_1144562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144599 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1144599 : Nat := 118140960795 + 1144599 * 2 ^ 59
def prefixEnd_1144599 : Nat := 4983230072969 + 3 ^ 40 * 1144599 * 2
def baseEnd_1144599 : Nat := 587729443655672484848591

theorem tailTrace_1144599 : CollatzResearch.WordTrace tailWord_1144599 prefixEnd_1144599 587729443655672484848591 := by
  unfold tailWord_1144599
  simp only [CollatzResearch.WordTrace]
  refine ⟨41746955180320779791196851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27831303453547186527464567 41746955180320779791196851)
  ·
    refine ⟨62620432770481169686795277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41746955180320779791196851 62620432770481169686795277)
    ·
      refine ⟨23482662288930438632548229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62620432770481169686795277 23482662288930438632548229)
      ·
        refine ⟨4402999179174457243602793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23482662288930438632548229 4402999179174457243602793)
        ·
          refine ⟨3302249384380842932702095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402999179174457243602793 3302249384380842932702095)
          ·
            refine ⟨4953374076571264399053143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302249384380842932702095 4953374076571264399053143)
            ·
              refine ⟨7430061114856896598579715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953374076571264399053143 7430061114856896598579715)
              ·
                refine ⟨11145091672285344897869573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7430061114856896598579715 11145091672285344897869573)
                ·
                  refine ⟨2089704688553502168350545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11145091672285344897869573 2089704688553502168350545)
                  ·
                    refine ⟨1567278516415126626262909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089704688553502168350545 1567278516415126626262909)
                    ·
                      refine ⟨587729443655672484848591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567278516415126626262909 587729443655672484848591)
                      ·
                        rfl

theorem cell23_1144599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1144599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144599 prefixEnd_1144599 := by exact prefixLift 1144599
  have htrace : WordTrace (prefixWord ++ tailWord_1144599) baseStart_1144599 baseEnd_1144599 := by
    simpa [prefixWord, tailWord_1144599, baseEnd_1144599] using wordTrace_append hprefix tailTrace_1144599
  have hstable : (prefixWord ++ tailWord_1144599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144599).length < 2 ^ (prefixWord ++ tailWord_1144599).sum := by decide
  have hdescent : baseEnd_1144599 < baseStart_1144599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144602 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_1144602 : Nat := 118140960795 + 1144602 * 2 ^ 59
def prefixEnd_1144602 : Nat := 4983230072969 + 3 ^ 40 * 1144602 * 2
def baseEnd_1144602 : Nat := 65303442677515108123453

theorem tailTrace_1144602 : CollatzResearch.WordTrace tailWord_1144602 prefixEnd_1144602 65303442677515108123453 := by
  unfold tailWord_1144602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10436766149827477825889015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27831376399539940869037373 10436766149827477825889015)
  ·
    refine ⟨15655149224741216738833523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10436766149827477825889015 15655149224741216738833523)
    ·
      refine ⟨23482723837111825108250285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15655149224741216738833523 23482723837111825108250285)
      ·
        refine ⟨8806021438916934415593857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23482723837111825108250285 8806021438916934415593857)
        ·
          refine ⟨6604516079187700811695393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8806021438916934415593857 6604516079187700811695393)
          ·
            refine ⟨4953387059390775608771545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6604516079187700811695393 4953387059390775608771545)
            ·
              refine ⟨3715040294543081706578659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953387059390775608771545 3715040294543081706578659)
              ·
                refine ⟨5572560441814622559867989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715040294543081706578659 5572560441814622559867989)
                ·
                  refine ⟨65303442677515108123453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5572560441814622559867989 65303442677515108123453)
                  ·
                    rfl

theorem cell23_1144602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_1144602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144602 prefixEnd_1144602 := by exact prefixLift 1144602
  have htrace : WordTrace (prefixWord ++ tailWord_1144602) baseStart_1144602 baseEnd_1144602 := by
    simpa [prefixWord, tailWord_1144602, baseEnd_1144602] using wordTrace_append hprefix tailTrace_1144602
  have hstable : (prefixWord ++ tailWord_1144602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144602).length < 2 ^ (prefixWord ++ tailWord_1144602).sum := by decide
  have hdescent : baseEnd_1144602 < baseStart_1144602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144633 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1144633 : Nat := 118140960795 + 1144633 * 2 ^ 59
def prefixEnd_1144633 : Nat := 4983230072969 + 3 ^ 40 * 1144633 * 2
def baseEnd_1144633 : Nat := 587746901997925351823435

theorem tailTrace_1144633 : CollatzResearch.WordTrace tailWord_1144633 prefixEnd_1144633 587746901997925351823435 := by
  unfold tailWord_1144633
  simp only [CollatzResearch.WordTrace]
  refine ⟨41748195262197603597934553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27832130174798402398623035 41748195262197603597934553)
  ·
    refine ⟨31311146446648202698450915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41748195262197603597934553 31311146446648202698450915)
    ·
      refine ⟨46966719669972304047676373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31311146446648202698450915 46966719669972304047676373)
      ·
        refine ⟨1100782492264975876117415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46966719669972304047676373 1100782492264975876117415)
        ·
          refine ⟨1651173738397463814176123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1100782492264975876117415 1651173738397463814176123)
          ·
            refine ⟨2476760607596195721264185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651173738397463814176123 2476760607596195721264185)
            ·
              refine ⟨1857570455697146790948139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2476760607596195721264185 1857570455697146790948139)
              ·
                refine ⟨2786355683545720186422209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857570455697146790948139 2786355683545720186422209)
                ·
                  refine ⟨2089766762659290139816657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786355683545720186422209 2089766762659290139816657)
                  ·
                    refine ⟨1567325071994467604862493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089766762659290139816657 1567325071994467604862493)
                    ·
                      refine ⟨587746901997925351823435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567325071994467604862493 587746901997925351823435)
                      ·
                        rfl

theorem cell23_1144633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1144633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144633 prefixEnd_1144633 := by exact prefixLift 1144633
  have htrace : WordTrace (prefixWord ++ tailWord_1144633) baseStart_1144633 baseEnd_1144633 := by
    simpa [prefixWord, tailWord_1144633, baseEnd_1144633] using wordTrace_append hprefix tailTrace_1144633
  have hstable : (prefixWord ++ tailWord_1144633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144633).length < 2 ^ (prefixWord ++ tailWord_1144633).sum := by decide
  have hdescent : baseEnd_1144633 < baseStart_1144633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144679 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 1, 6]
def baseStart_1144679 : Nat := 118140960795 + 1144679 * 2 ^ 59
def prefixEnd_1144679 : Nat := 4983230072969 + 3 ^ 40 * 1144679 * 2
def baseEnd_1144679 : Nat := 195923507369344057282741

theorem tailTrace_1144679 : CollatzResearch.WordTrace tailWord_1144679 prefixEnd_1144679 195923507369344057282741 := by
  unfold tailWord_1144679
  simp only [CollatzResearch.WordTrace]
  refine ⟨41749873020030953454109091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27833248680020635636072727 41749873020030953454109091)
  ·
    refine ⟨62624809530046430181163637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41749873020030953454109091 62624809530046430181163637)
    ·
      refine ⟨5871075893441852829484091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62624809530046430181163637 5871075893441852829484091)
      ·
        refine ⟨8806613840162779244226137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871075893441852829484091 8806613840162779244226137)
        ·
          refine ⟨6604960380122084433169603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8806613840162779244226137 6604960380122084433169603)
          ·
            refine ⟨9907440570183126649754405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604960380122084433169603 9907440570183126649754405)
            ·
              refine ⟨1857645106909336246828951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9907440570183126649754405 1857645106909336246828951)
              ·
                refine ⟨2786467660364004370243427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857645106909336246828951 2786467660364004370243427)
                ·
                  refine ⟨4179701490546006555365141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786467660364004370243427 4179701490546006555365141)
                  ·
                    refine ⟨195923507369344057282741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4179701490546006555365141 195923507369344057282741)
                    ·
                      rfl

theorem cell23_1144679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_1144679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144679 prefixEnd_1144679 := by exact prefixLift 1144679
  have htrace : WordTrace (prefixWord ++ tailWord_1144679) baseStart_1144679 baseEnd_1144679 := by
    simpa [prefixWord, tailWord_1144679, baseEnd_1144679] using wordTrace_append hprefix tailTrace_1144679
  have hstable : (prefixWord ++ tailWord_1144679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144679).length < 2 ^ (prefixWord ++ tailWord_1144679).sum := by decide
  have hdescent : baseEnd_1144679 < baseStart_1144679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144686 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1144686 : Nat := 118140960795 + 1144686 * 2 ^ 59
def prefixEnd_1144686 : Nat := 4983230072969 + 3 ^ 40 * 1144686 * 2
def baseEnd_1144686 : Nat := 587774116472613644460691

theorem tailTrace_1144686 : CollatzResearch.WordTrace tailWord_1144686 prefixEnd_1144686 587774116472613644460691 := by
  unfold tailWord_1144686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5218766041375699206201739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27833418887337062433075941 5218766041375699206201739)
  ·
    refine ⟨7828149062063548809302609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5218766041375699206201739 7828149062063548809302609)
    ·
      refine ⟨5871111796547661606976957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7828149062063548809302609 5871111796547661606976957)
      ·
        refine ⟨2201666923705373102616359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5871111796547661606976957 2201666923705373102616359)
        ·
          refine ⟨3302500385558059653924539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201666923705373102616359 3302500385558059653924539)
          ·
            refine ⟨4953750578337089480886809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302500385558059653924539 4953750578337089480886809)
            ·
              refine ⟨3715312933752817110665107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4953750578337089480886809 3715312933752817110665107)
              ·
                refine ⟨5572969400629225665997661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715312933752817110665107 5572969400629225665997661)
                ·
                  refine ⟨2089863525235959624749123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5572969400629225665997661 2089863525235959624749123)
                  ·
                    refine ⟨3134795287853939437123685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2089863525235959624749123 3134795287853939437123685)
                    ·
                      refine ⟨587774116472613644460691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3134795287853939437123685 587774116472613644460691)
                      ·
                        rfl

theorem cell23_1144686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1144686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144686 prefixEnd_1144686 := by exact prefixLift 1144686
  have htrace : WordTrace (prefixWord ++ tailWord_1144686) baseStart_1144686 baseEnd_1144686 := by
    simpa [prefixWord, tailWord_1144686, baseEnd_1144686] using wordTrace_append hprefix tailTrace_1144686
  have hstable : (prefixWord ++ tailWord_1144686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144686).length < 2 ^ (prefixWord ++ tailWord_1144686).sum := by decide
  have hdescent : baseEnd_1144686 < baseStart_1144686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144689 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 3]
def baseStart_1144689 : Nat := 118140960795 + 1144689 * 2 ^ 59
def prefixEnd_1144689 : Nat := 4983230072969 + 3 ^ 40 * 1144689 * 2
def baseEnd_1144689 : Nat := 587775656914577132723177

theorem tailTrace_1144689 : CollatzResearch.WordTrace tailWord_1144689 prefixEnd_1144689 587775656914577132723177 := by
  unfold tailWord_1144689
  simp only [CollatzResearch.WordTrace]
  refine ⟨41750237749994725161973121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27833491833329816774648747 41750237749994725161973121)
  ·
    refine ⟨31312678312496043871479841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41750237749994725161973121 31312678312496043871479841)
    ·
      refine ⟨23484508734372032903609881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31312678312496043871479841 23484508734372032903609881)
      ·
        refine ⟨17613381550779024677707411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23484508734372032903609881 17613381550779024677707411)
        ·
          refine ⟨26420072326168537016561117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17613381550779024677707411 26420072326168537016561117)
          ·
            refine ⟨9907527122313201381210419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26420072326168537016561117 9907527122313201381210419)
            ·
              refine ⟨14861290683469802071815629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9907527122313201381210419 14861290683469802071815629)
              ·
                refine ⟨5572984006301175776930861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14861290683469802071815629 5572984006301175776930861)
                ·
                  refine ⟨2089869002362940916349073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5572984006301175776930861 2089869002362940916349073)
                  ·
                    refine ⟨1567401751772205687261805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2089869002362940916349073 1567401751772205687261805)
                    ·
                      refine ⟨587775656914577132723177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567401751772205687261805 587775656914577132723177)
                      ·
                        rfl

theorem cell23_1144689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_1144689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144689 prefixEnd_1144689 := by exact prefixLift 1144689
  have htrace : WordTrace (prefixWord ++ tailWord_1144689) baseStart_1144689 baseEnd_1144689 := by
    simpa [prefixWord, tailWord_1144689, baseEnd_1144689] using wordTrace_append hprefix tailTrace_1144689
  have hstable : (prefixWord ++ tailWord_1144689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144689).length < 2 ^ (prefixWord ++ tailWord_1144689).sum := by decide
  have hdescent : baseEnd_1144689 < baseStart_1144689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144779 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3]
def baseStart_1144779 : Nat := 118140960795 + 1144779 * 2 ^ 59
def prefixEnd_1144779 : Nat := 4983230072969 + 3 ^ 40 * 1144779 * 2
def baseEnd_1144779 : Nat := 587821870173481780597763

theorem tailTrace_1144779 : CollatzResearch.WordTrace tailWord_1144779 prefixEnd_1144779 587821870173481780597763 := by
  unfold tailWord_1144779
  simp only [CollatzResearch.WordTrace]
  refine ⟨41753520319668670532749391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27835680213112447021832927 41753520319668670532749391)
  ·
    refine ⟨62630280479503005799124087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41753520319668670532749391 62630280479503005799124087)
    ·
      refine ⟨93945420719254508698686131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62630280479503005799124087 93945420719254508698686131)
      ·
        refine ⟨140918131078881763048029197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93945420719254508698686131 140918131078881763048029197)
        ·
          refine ⟨52844299154580661143010949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140918131078881763048029197 52844299154580661143010949)
          ·
            refine ⟨9908306091483873964314553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52844299154580661143010949 9908306091483873964314553)
            ·
              refine ⟨7431229568612905473235915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9908306091483873964314553 7431229568612905473235915)
              ·
                refine ⟨11146844352919358209853873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431229568612905473235915 11146844352919358209853873)
                ·
                  refine ⟨8360133264689518657390405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11146844352919358209853873 8360133264689518657390405)
                  ·
                    refine ⟨1567524987129284748260701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8360133264689518657390405 1567524987129284748260701)
                    ·
                      refine ⟨587821870173481780597763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567524987129284748260701 587821870173481780597763)
                      ·
                        rfl

theorem cell23_1144779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 3].length) (baseStart_1144779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144779 prefixEnd_1144779 := by exact prefixLift 1144779
  have htrace : WordTrace (prefixWord ++ tailWord_1144779) baseStart_1144779 baseEnd_1144779 := by
    simpa [prefixWord, tailWord_1144779, baseEnd_1144779] using wordTrace_append hprefix tailTrace_1144779
  have hstable : (prefixWord ++ tailWord_1144779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144779).length < 2 ^ (prefixWord ++ tailWord_1144779).sum := by decide
  have hdescent : baseEnd_1144779 < baseStart_1144779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144797 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_1144797 : Nat := 118140960795 + 1144797 * 2 ^ 59
def prefixEnd_1144797 : Nat := 4983230072969 + 3 ^ 40 * 1144797 * 2
def baseEnd_1144797 : Nat := 587831112825262710172681

theorem tailTrace_1144797 : CollatzResearch.WordTrace tailWord_1144797 prefixEnd_1144797 587831112825262710172681 := by
  unfold tailWord_1144797
  simp only [CollatzResearch.WordTrace]
  refine ⟨41754176833603459606904645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27836117889068973071269763 41754176833603459606904645)
  ·
    refine ⟨7828908156300648676294621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41754176833603459606904645 7828908156300648676294621)
    ·
      refine ⟨2935840558612743253610483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7828908156300648676294621 2935840558612743253610483)
      ·
        refine ⟨4403760837919114880415725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935840558612743253610483 4403760837919114880415725)
        ·
          refine ⟨1651410314219668080155897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403760837919114880415725 1651410314219668080155897)
          ·
            refine ⟨1238557735664751060116923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1651410314219668080155897 1238557735664751060116923)
            ·
              refine ⟨1857836603497126590175385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238557735664751060116923 1857836603497126590175385)
              ·
                refine ⟨1393377452622844942631539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1857836603497126590175385 1393377452622844942631539)
                ·
                  refine ⟨2090066178934267413947309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393377452622844942631539 2090066178934267413947309)
                  ·
                    refine ⟨783774817100350280230241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090066178934267413947309 783774817100350280230241)
                    ·
                      refine ⟨587831112825262710172681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783774817100350280230241 587831112825262710172681)
                      ·
                        rfl

theorem cell23_1144797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_1144797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144797 prefixEnd_1144797 := by exact prefixLift 1144797
  have htrace : WordTrace (prefixWord ++ tailWord_1144797) baseStart_1144797 baseEnd_1144797 := by
    simpa [prefixWord, tailWord_1144797, baseEnd_1144797] using wordTrace_append hprefix tailTrace_1144797
  have hstable : (prefixWord ++ tailWord_1144797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144797).length < 2 ^ (prefixWord ++ tailWord_1144797).sum := by decide
  have hdescent : baseEnd_1144797 < baseStart_1144797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144866 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 3, 4]
def baseStart_1144866 : Nat := 118140960795 + 1144866 * 2 ^ 59
def prefixEnd_1144866 : Nat := 4983230072969 + 3 ^ 40 * 1144866 * 2
def baseEnd_1144866 : Nat := 587866542990422940209863

theorem tailTrace_1144866 : CollatzResearch.WordTrace tailWord_1144866 prefixEnd_1144866 587866542990422940209863 := by
  unfold tailWord_1144866
  simp only [CollatzResearch.WordTrace]
  refine ⟨10439173367588371097791613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27837795646902322927444301 10439173367588371097791613)
  ·
    refine ⟨3914690012845639161671855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10439173367588371097791613 3914690012845639161671855)
    ·
      refine ⟨5872035019268458742507783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3914690012845639161671855 5872035019268458742507783)
      ·
        refine ⟨8808052528902688113761675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5872035019268458742507783 8808052528902688113761675)
        ·
          refine ⟨13212078793354032170642513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808052528902688113761675 13212078793354032170642513)
          ·
            refine ⟨9909059095015524127981885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13212078793354032170642513 9909059095015524127981885)
            ·
              refine ⟨3715897160630821547993207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9909059095015524127981885 3715897160630821547993207)
              ·
                refine ⟨5573845740946232321989811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715897160630821547993207 5573845740946232321989811)
                ·
                  refine ⟨8360768611419348482984717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5573845740946232321989811 8360768611419348482984717)
                  ·
                    refine ⟨3135288229282255681119269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8360768611419348482984717 3135288229282255681119269)
                    ·
                      refine ⟨587866542990422940209863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3135288229282255681119269 587866542990422940209863)
                      ·
                        rfl

theorem cell23_1144866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_1144866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144866 prefixEnd_1144866 := by exact prefixLift 1144866
  have htrace : WordTrace (prefixWord ++ tailWord_1144866) baseStart_1144866 baseEnd_1144866 := by
    simpa [prefixWord, tailWord_1144866, baseEnd_1144866] using wordTrace_append hprefix tailTrace_1144866
  have hstable : (prefixWord ++ tailWord_1144866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144866).length < 2 ^ (prefixWord ++ tailWord_1144866).sum := by decide
  have hdescent : baseEnd_1144866 < baseStart_1144866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144893 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1144893 : Nat := 118140960795 + 1144893 * 2 ^ 59
def prefixEnd_1144893 : Nat := 4983230072969 + 3 ^ 40 * 1144893 * 2
def baseEnd_1144893 : Nat := 195960135656031444857413

theorem tailTrace_1144893 : CollatzResearch.WordTrace tailWord_1144893 prefixEnd_1144893 195960135656031444857413 := by
  unfold tailWord_1144893
  simp only [CollatzResearch.WordTrace]
  refine ⟨41757678241255668002399333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27838452160837112001599555 41757678241255668002399333)
  ·
    refine ⟨7829564670235437750449875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41757678241255668002399333 7829564670235437750449875)
    ·
      refine ⟨11744347005353156625674813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7829564670235437750449875 11744347005353156625674813)
      ·
        refine ⟨4404130127007433734628055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11744347005353156625674813 4404130127007433734628055)
        ·
          refine ⟨6606195190511150601942083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404130127007433734628055 6606195190511150601942083)
          ·
            refine ⟨9909292785766725902913125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6606195190511150601942083 9909292785766725902913125)
            ·
              refine ⟨1857992397331261106796211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9909292785766725902913125 1857992397331261106796211)
              ·
                refine ⟨2786988595996891660194317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857992397331261106796211 2786988595996891660194317)
                ·
                  refine ⟨1045120723498834372572869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2786988595996891660194317 1045120723498834372572869)
                  ·
                    refine ⟨195960135656031444857413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045120723498834372572869 195960135656031444857413)
                    ·
                      rfl

theorem cell23_1144893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1144893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144893 prefixEnd_1144893 := by exact prefixLift 1144893
  have htrace : WordTrace (prefixWord ++ tailWord_1144893) baseStart_1144893 baseEnd_1144893 := by
    simpa [prefixWord, tailWord_1144893, baseEnd_1144893] using wordTrace_append hprefix tailTrace_1144893
  have hstable : (prefixWord ++ tailWord_1144893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144893).length < 2 ^ (prefixWord ++ tailWord_1144893).sum := by decide
  have hdescent : baseEnd_1144893 < baseStart_1144893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144916 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1144916 : Nat := 118140960795 + 1144916 * 2 ^ 59
def prefixEnd_1144916 : Nat := 4983230072969 + 3 ^ 40 * 1144916 * 2
def baseEnd_1144916 : Nat := 587892217023147744584633

theorem tailTrace_1144916 : CollatzResearch.WordTrace tailWord_1144916 prefixEnd_1144916 587892217023147744584633 := by
  unfold tailWord_1144916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20879258560086171465243301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27839011413448228620324401 20879258560086171465243301)
  ·
    refine ⟨3914860980016157149733119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20879258560086171465243301 3914860980016157149733119)
    ·
      refine ⟨5872291470024235724599679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3914860980016157149733119 5872291470024235724599679)
      ·
        refine ⟨8808437205036353586899519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5872291470024235724599679 8808437205036353586899519)
        ·
          refine ⟨13212655807554530380349279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808437205036353586899519 13212655807554530380349279)
          ·
            refine ⟨19818983711331795570523919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13212655807554530380349279 19818983711331795570523919)
            ·
              refine ⟨29728475566997693355785879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19818983711331795570523919 29728475566997693355785879)
              ·
                refine ⟨44592713350496540033678819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29728475566997693355785879 44592713350496540033678819)
                ·
                  refine ⟨66889070025744810050518229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44592713350496540033678819 66889070025744810050518229)
                  ·
                    refine ⟨1567712578728393985559021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66889070025744810050518229 1567712578728393985559021)
                    ·
                      refine ⟨587892217023147744584633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567712578728393985559021 587892217023147744584633)
                      ·
                        rfl

theorem cell23_1144916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1144916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144916 prefixEnd_1144916 := by exact prefixLift 1144916
  have htrace : WordTrace (prefixWord ++ tailWord_1144916) baseStart_1144916 baseEnd_1144916 := by
    simpa [prefixWord, tailWord_1144916, baseEnd_1144916] using wordTrace_append hprefix tailTrace_1144916
  have hstable : (prefixWord ++ tailWord_1144916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144916).length < 2 ^ (prefixWord ++ tailWord_1144916).sum := by decide
  have hdescent : baseEnd_1144916 < baseStart_1144916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144943 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 4, 3, 2]
def baseStart_1144943 : Nat := 118140960795 + 1144943 * 2 ^ 59
def prefixEnd_1144943 : Nat := 4983230072969 + 3 ^ 40 * 1144943 * 2
def baseEnd_1144943 : Nat := 587906081000819138947009

theorem tailTrace_1144943 : CollatzResearch.WordTrace tailWord_1144943 prefixEnd_1144943 587906081000819138947009 := by
  unfold tailWord_1144943
  simp only [CollatzResearch.WordTrace]
  refine ⟨41759501891074526541719483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27839667927383017694479655 41759501891074526541719483)
  ·
    refine ⟨62639252836611789812579225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41759501891074526541719483 62639252836611789812579225)
    ·
      refine ⟨46979439627458842359434419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62639252836611789812579225 46979439627458842359434419)
      ·
        refine ⟨70469159441188263539151629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46979439627458842359434419 70469159441188263539151629)
        ·
          refine ⟨26425934790445598827181861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70469159441188263539151629 26425934790445598827181861)
          ·
            refine ⟨4954862773208549780096599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26425934790445598827181861 4954862773208549780096599)
            ·
              refine ⟨7432294159812824670144899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954862773208549780096599 7432294159812824670144899)
              ·
                refine ⟨11148441239719237005217349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7432294159812824670144899 11148441239719237005217349)
                ·
                  refine ⟨2090332732447356938478253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11148441239719237005217349 2090332732447356938478253)
                  ·
                    refine ⟨783874774667758851929345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090332732447356938478253 783874774667758851929345)
                    ·
                      refine ⟨587906081000819138947009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783874774667758851929345 587906081000819138947009)
                      ·
                        rfl

theorem cell23_1144943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 3, 2].length) (baseStart_1144943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144943 prefixEnd_1144943 := by exact prefixLift 1144943
  have htrace : WordTrace (prefixWord ++ tailWord_1144943) baseStart_1144943 baseEnd_1144943 := by
    simpa [prefixWord, tailWord_1144943, baseEnd_1144943] using wordTrace_append hprefix tailTrace_1144943
  have hstable : (prefixWord ++ tailWord_1144943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144943).length < 2 ^ (prefixWord ++ tailWord_1144943).sum := by decide
  have hdescent : baseEnd_1144943 < baseStart_1144943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144970 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_1144970 : Nat := 118140960795 + 1144970 * 2 ^ 59
def prefixEnd_1144970 : Nat := 4983230072969 + 3 ^ 40 * 1144970 * 2
def baseEnd_1144970 : Nat := 195973314992830177769795

theorem tailTrace_1144970 : CollatzResearch.WordTrace tailWord_1144970 prefixEnd_1144970 195973314992830177769795 := by
  unfold tailWord_1144970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440121665494177538238091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27840324441317806768634909 10440121665494177538238091)
  ·
    refine ⟨15660182498241266307357137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10440121665494177538238091 15660182498241266307357137)
    ·
      refine ⟨11745136873680949730517853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15660182498241266307357137 11745136873680949730517853)
      ·
        refine ⟨4404426327630356148944195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11745136873680949730517853 4404426327630356148944195)
        ·
          refine ⟨6606639491445534223416293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404426327630356148944195 6606639491445534223416293)
          ·
            refine ⟨1238744904646037666890555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6606639491445534223416293 1238744904646037666890555)
            ·
              refine ⟨1858117356969056500335833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238744904646037666890555 1858117356969056500335833)
              ·
                refine ⟨1393588017726792375251875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858117356969056500335833 1393588017726792375251875)
                ·
                  refine ⟨2090382026590188562877813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393588017726792375251875 2090382026590188562877813)
                  ·
                    refine ⟨195973314992830177769795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2090382026590188562877813 195973314992830177769795)
                    ·
                      rfl

theorem cell23_1144970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_1144970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144970 prefixEnd_1144970 := by exact prefixLift 1144970
  have htrace : WordTrace (prefixWord ++ tailWord_1144970) baseStart_1144970 baseEnd_1144970 := by
    simpa [prefixWord, tailWord_1144970, baseEnd_1144970] using wordTrace_append hprefix tailTrace_1144970
  have hstable : (prefixWord ++ tailWord_1144970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144970).length < 2 ^ (prefixWord ++ tailWord_1144970).sum := by decide
  have hdescent : baseEnd_1144970 < baseStart_1144970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144983 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 1, 6]
def baseStart_1144983 : Nat := 118140960795 + 1144983 * 2 ^ 59
def prefixEnd_1144983 : Nat := 4983230072969 + 3 ^ 40 * 1144983 * 2
def baseEnd_1144983 : Nat := 195975540075666327482275

theorem tailTrace_1144983 : CollatzResearch.WordTrace tailWord_1144983 prefixEnd_1144983 195975540075666327482275 := by
  unfold tailWord_1144983
  simp only [CollatzResearch.WordTrace]
  refine ⟨41760960810929613373175603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27840640540619742248783735 41760960810929613373175603)
  ·
    refine ⟨62641441216394420059763405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41760960810929613373175603 62641441216394420059763405)
    ·
      refine ⟨23490540456147907522411277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62641441216394420059763405 23490540456147907522411277)
      ·
        refine ⟨8808952671055465320904229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23490540456147907522411277 8808952671055465320904229)
        ·
          refine ⟨1651678625822899747669543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8808952671055465320904229 1651678625822899747669543)
          ·
            refine ⟨2477517938734349621504315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651678625822899747669543 2477517938734349621504315)
            ·
              refine ⟨3716276908101524432256473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477517938734349621504315 3716276908101524432256473)
              ·
                refine ⟨2787207681076143324192355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3716276908101524432256473 2787207681076143324192355)
                ·
                  refine ⟨4180811521614214986288533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787207681076143324192355 4180811521614214986288533)
                  ·
                    refine ⟨195975540075666327482275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4180811521614214986288533 195975540075666327482275)
                    ·
                      rfl

theorem cell23_1144983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_1144983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144983 prefixEnd_1144983 := by exact prefixLift 1144983
  have htrace : WordTrace (prefixWord ++ tailWord_1144983) baseStart_1144983 baseEnd_1144983 := by
    simpa [prefixWord, tailWord_1144983, baseEnd_1144983] using wordTrace_append hprefix tailTrace_1144983
  have hstable : (prefixWord ++ tailWord_1144983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144983).length < 2 ^ (prefixWord ++ tailWord_1144983).sum := by decide
  have hdescent : baseEnd_1144983 < baseStart_1144983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144993 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1144993 : Nat := 118140960795 + 1144993 * 2 ^ 59
def prefixEnd_1144993 : Nat := 4983230072969 + 3 ^ 40 * 1144993 * 2
def baseEnd_1144993 : Nat := 587931755033543943321779

theorem tailTrace_1144993 : CollatzResearch.WordTrace tailWord_1144993 prefixEnd_1144993 587931755033543943321779 := by
  unfold tailWord_1144993
  simp only [CollatzResearch.WordTrace]
  refine ⟨41761325540893385081039633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27840883693928923387359755 41761325540893385081039633)
  ·
    refine ⟨31320994155670038810779725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41761325540893385081039633 31320994155670038810779725)
    ·
      refine ⟨11745372808376264554042397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31320994155670038810779725 11745372808376264554042397)
      ·
        refine ⟨4404514803141099207765899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11745372808376264554042397 4404514803141099207765899)
        ·
          refine ⟨6606772204711648811648849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404514803141099207765899 6606772204711648811648849)
          ·
            refine ⟨4955079153533736608736637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6606772204711648811648849 4955079153533736608736637)
            ·
              refine ⟨1858154682575151228276239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4955079153533736608736637 1858154682575151228276239)
              ·
                refine ⟨2787232023862726842414359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858154682575151228276239 2787232023862726842414359)
                ·
                  refine ⟨4180848035794090263621539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787232023862726842414359 4180848035794090263621539)
                  ·
                    refine ⟨6271272053691135395432309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4180848035794090263621539 6271272053691135395432309)
                    ·
                      refine ⟨587931755033543943321779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6271272053691135395432309 587931755033543943321779)
                      ·
                        rfl

theorem cell23_1144993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1144993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144993 prefixEnd_1144993 := by exact prefixLift 1144993
  have htrace : WordTrace (prefixWord ++ tailWord_1144993) baseStart_1144993 baseEnd_1144993 := by
    simpa [prefixWord, tailWord_1144993, baseEnd_1144993] using wordTrace_append hprefix tailTrace_1144993
  have hstable : (prefixWord ++ tailWord_1144993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144993).length < 2 ^ (prefixWord ++ tailWord_1144993).sum := by decide
  have hdescent : baseEnd_1144993 < baseStart_1144993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1144996 : List Nat := [2, 3, 1, 2, 4, 11]
def baseStart_1144996 : Nat := 118140960795 + 1144996 * 2 ^ 59
def prefixEnd_1144996 : Nat := 4983230072969 + 3 ^ 40 * 1144996 * 2
def baseEnd_1144996 : Nat := 2419478582203734286355

theorem tailTrace_1144996 : CollatzResearch.WordTrace tailWord_1144996 prefixEnd_1144996 2419478582203734286355 := by
  unfold tailWord_1144996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20880717479941258296699421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27840956639921677728932561 20880717479941258296699421)
  ·
    refine ⟨7830269054977971861262283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20880717479941258296699421 7830269054977971861262283)
    ·
      refine ⟨11745403582466957791893425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7830269054977971861262283 11745403582466957791893425)
      ·
        refine ⟨8809052686850218343920069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11745403582466957791893425 8809052686850218343920069)
        ·
          refine ⟨1651697378784415939485013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8809052686850218343920069 1651697378784415939485013)
          ·
            refine ⟨2419478582203734286355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1651697378784415939485013 2419478582203734286355)
            ·
              rfl

theorem cell23_1144996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 11].length) (baseStart_1144996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1144996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1144996 prefixEnd_1144996 := by exact prefixLift 1144996
  have htrace : WordTrace (prefixWord ++ tailWord_1144996) baseStart_1144996 baseEnd_1144996 := by
    simpa [prefixWord, tailWord_1144996, baseEnd_1144996] using wordTrace_append hprefix tailTrace_1144996
  have hstable : (prefixWord ++ tailWord_1144996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1144996).length < 2 ^ (prefixWord ++ tailWord_1144996).sum := by decide
  have hdescent : baseEnd_1144996 < baseStart_1144996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1144996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145020 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_1145020 : Nat := 118140960795 + 1145020 * 2 ^ 59
def prefixEnd_1145020 : Nat := 4983230072969 + 3 ^ 40 * 1145020 * 2
def baseEnd_1145020 : Nat := 587945619011215337684155

theorem tailTrace_1145020 : CollatzResearch.WordTrace tailWord_1145020 prefixEnd_1145020 587945619011215337684155 := by
  unfold tailWord_1145020
  simp only [CollatzResearch.WordTrace]
  refine ⟨20881155155897784346136257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27841540207863712461515009 20881155155897784346136257)
  ·
    refine ⟨15660866366923338259602193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20881155155897784346136257 15660866366923338259602193)
    ·
      refine ⟨11745649775192503694701645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15660866366923338259602193 11745649775192503694701645)
      ·
        refine ⟨4404618665697188885513117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11745649775192503694701645 4404618665697188885513117)
        ·
          refine ⟨1651731999636445832067419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4404618665697188885513117 1651731999636445832067419)
          ·
            refine ⟨2477597999454668748101129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651731999636445832067419 2477597999454668748101129)
            ·
              refine ⟨1858198499591001561075847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477597999454668748101129 1858198499591001561075847)
              ·
                refine ⟨2787297749386502341613771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858198499591001561075847 2787297749386502341613771)
                ·
                  refine ⟨4180946624079753512420657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2787297749386502341613771 4180946624079753512420657)
                  ·
                    refine ⟨3135709968059815134315493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4180946624079753512420657 3135709968059815134315493)
                    ·
                      refine ⟨587945619011215337684155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3135709968059815134315493 587945619011215337684155)
                      ·
                        rfl

theorem cell23_1145020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_1145020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145020 prefixEnd_1145020 := by exact prefixLift 1145020
  have htrace : WordTrace (prefixWord ++ tailWord_1145020) baseStart_1145020 baseEnd_1145020 := by
    simpa [prefixWord, tailWord_1145020, baseEnd_1145020] using wordTrace_append hprefix tailTrace_1145020
  have hstable : (prefixWord ++ tailWord_1145020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145020).length < 2 ^ (prefixWord ++ tailWord_1145020).sum := by decide
  have hdescent : baseEnd_1145020 < baseStart_1145020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145023 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 3]
def baseStart_1145023 : Nat := 118140960795 + 1145023 * 2 ^ 59
def prefixEnd_1145023 : Nat := 4983230072969 + 3 ^ 40 * 1145023 * 2
def baseEnd_1145023 : Nat := 587947159453178825946641

theorem tailTrace_1145023 : CollatzResearch.WordTrace tailWord_1145023 prefixEnd_1145023 587947159453178825946641 := by
  unfold tailWord_1145023
  simp only [CollatzResearch.WordTrace]
  refine ⟨41762419730784700204631723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27841613153856466803087815 41762419730784700204631723)
  ·
    refine ⟨62643629596177050306947585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41762419730784700204631723 62643629596177050306947585)
    ·
      refine ⟨46982722197132787730210689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62643629596177050306947585 46982722197132787730210689)
      ·
        refine ⟨35237041647849590797658017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46982722197132787730210689 35237041647849590797658017)
        ·
          refine ⟨26427781235887193098243513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35237041647849590797658017 26427781235887193098243513)
          ·
            refine ⟨19820835926915394823682635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26427781235887193098243513 19820835926915394823682635)
            ·
              refine ⟨29731253890373092235523953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19820835926915394823682635 29731253890373092235523953)
              ·
                refine ⟨22298440417779819176642965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29731253890373092235523953 22298440417779819176642965)
                ·
                  refine ⟨1045239394583429023905139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 22298440417779819176642965 1045239394583429023905139)
                  ·
                    refine ⟨1567859091875143535857709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045239394583429023905139 1567859091875143535857709)
                    ·
                      refine ⟨587947159453178825946641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567859091875143535857709 587947159453178825946641)
                      ·
                        rfl

theorem cell23_1145023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_1145023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145023 prefixEnd_1145023 := by exact prefixLift 1145023
  have htrace : WordTrace (prefixWord ++ tailWord_1145023) baseStart_1145023 baseEnd_1145023 := by
    simpa [prefixWord, tailWord_1145023, baseEnd_1145023] using wordTrace_append hprefix tailTrace_1145023
  have hstable : (prefixWord ++ tailWord_1145023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145023).length < 2 ^ (prefixWord ++ tailWord_1145023).sum := by decide
  have hdescent : baseEnd_1145023 < baseStart_1145023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145056 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 4, 6]
def baseStart_1145056 : Nat := 118140960795 + 1145056 * 2 ^ 59
def prefixEnd_1145056 : Nat := 4983230072969 + 3 ^ 40 * 1145056 * 2
def baseEnd_1145056 : Nat := 195988034771592398944663

theorem tailTrace_1145056 : CollatzResearch.WordTrace tailWord_1145056 prefixEnd_1145056 195988034771592398944663 := by
  unfold tailWord_1145056
  simp only [CollatzResearch.WordTrace]
  refine ⟨20881811669832573420291511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27842415559776764560388681 20881811669832573420291511)
  ·
    refine ⟨31322717504748860130437267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20881811669832573420291511 31322717504748860130437267)
    ·
      refine ⟨46984076257123290195655901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31322717504748860130437267 46984076257123290195655901)
      ·
        refine ⟨17619028596421233823370963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46984076257123290195655901 17619028596421233823370963)
        ·
          refine ⟨26428542894631850735056445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17619028596421233823370963 26428542894631850735056445)
          ·
            refine ⟨9910703585486944025646167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26428542894631850735056445 9910703585486944025646167)
            ·
              refine ⟨14866055378230416038469251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9910703585486944025646167 14866055378230416038469251)
              ·
                refine ⟨22299083067345624057703877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14866055378230416038469251 22299083067345624057703877)
                ·
                  refine ⟨4181078075127304510819477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22299083067345624057703877 4181078075127304510819477)
                  ·
                    refine ⟨195988034771592398944663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4181078075127304510819477 195988034771592398944663)
                    ·
                      rfl

theorem cell23_1145056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_1145056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145056 prefixEnd_1145056 := by exact prefixLift 1145056
  have htrace : WordTrace (prefixWord ++ tailWord_1145056) baseStart_1145056 baseEnd_1145056 := by
    simpa [prefixWord, tailWord_1145056, baseEnd_1145056] using wordTrace_append hprefix tailTrace_1145056
  have hstable : (prefixWord ++ tailWord_1145056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145056).length < 2 ^ (prefixWord ++ tailWord_1145056).sum := by decide
  have hdescent : baseEnd_1145056 < baseStart_1145056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145058 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 3, 2, 2]
def baseStart_1145058 : Nat := 118140960795 + 1145058 * 2 ^ 59
def prefixEnd_1145058 : Nat := 4983230072969 + 3 ^ 40 * 1145058 * 2
def baseEnd_1145058 : Nat := 587965131276086189008981

theorem tailTrace_1145058 : CollatzResearch.WordTrace tailWord_1145058 prefixEnd_1145058 587965131276086189008981 := by
  unfold tailWord_1145058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10440924071414475295538957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27842464190438600788103885 10440924071414475295538957)
  ·
    refine ⟨3915346526780428235827109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10440924071414475295538957 3915346526780428235827109)
    ·
      refine ⟨734127473771330294217583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3915346526780428235827109 734127473771330294217583)
      ·
        refine ⟨1101191210656995441326375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734127473771330294217583 1101191210656995441326375)
        ·
          refine ⟨1651786815985493161989563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101191210656995441326375 1651786815985493161989563)
          ·
            refine ⟨2477680223978239742984345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651786815985493161989563 2477680223978239742984345)
            ·
              refine ⟨1858260167983679807238259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477680223978239742984345 1858260167983679807238259)
              ·
                refine ⟨2787390251975519710857389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858260167983679807238259 2787390251975519710857389)
                ·
                  refine ⟨1045271344490819891571521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2787390251975519710857389 1045271344490819891571521)
                  ·
                    refine ⟨783953508368114918678641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1045271344490819891571521 783953508368114918678641)
                    ·
                      refine ⟨587965131276086189008981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 783953508368114918678641 587965131276086189008981)
                      ·
                        rfl

theorem cell23_1145058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_1145058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145058 prefixEnd_1145058 := by exact prefixLift 1145058
  have htrace : WordTrace (prefixWord ++ tailWord_1145058) baseStart_1145058 baseEnd_1145058 := by
    simpa [prefixWord, tailWord_1145058, baseEnd_1145058] using wordTrace_append hprefix tailTrace_1145058
  have hstable : (prefixWord ++ tailWord_1145058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145058).length < 2 ^ (prefixWord ++ tailWord_1145058).sum := by decide
  have hdescent : baseEnd_1145058 < baseStart_1145058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145074 : List Nat := [3, 2, 1, 3, 2, 2, 3, 1, 2, 1, 3]
def baseStart_1145074 : Nat := 118140960795 + 1145074 * 2 ^ 59
def prefixEnd_1145074 : Nat := 4983230072969 + 3 ^ 40 * 1145074 * 2
def baseEnd_1145074 : Nat := 587973346966558126408907

theorem tailTrace_1145074 : CollatzResearch.WordTrace tailWord_1145074 prefixEnd_1145074 587973346966558126408907 := by
  unfold tailWord_1145074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441069963399983978684569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27842853235733290609825517 10441069963399983978684569)
  ·
    refine ⟨7830802472549987984013427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10441069963399983978684569 7830802472549987984013427)
    ·
      refine ⟨11746203708824981976020141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7830802472549987984013427 11746203708824981976020141)
      ·
        refine ⟨4404826390809368241007553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11746203708824981976020141 4404826390809368241007553)
        ·
          refine ⟨3303619793107026180755665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404826390809368241007553 3303619793107026180755665)
          ·
            refine ⟨2477714844830269635566749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303619793107026180755665 2477714844830269635566749)
            ·
              refine ⟨929143066811351113337531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2477714844830269635566749 929143066811351113337531)
              ·
                refine ⟨1393714600217026670006297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929143066811351113337531 1393714600217026670006297)
                ·
                  refine ⟨1045285950162770002504723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1393714600217026670006297 1045285950162770002504723)
                  ·
                    refine ⟨1567928925244155003757085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045285950162770002504723 1567928925244155003757085)
                    ·
                      refine ⟨587973346966558126408907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1567928925244155003757085 587973346966558126408907)
                      ·
                        rfl

theorem cell23_1145074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_1145074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145074 prefixEnd_1145074 := by exact prefixLift 1145074
  have htrace : WordTrace (prefixWord ++ tailWord_1145074) baseStart_1145074 baseEnd_1145074 := by
    simpa [prefixWord, tailWord_1145074, baseEnd_1145074] using wordTrace_append hprefix tailTrace_1145074
  have hstable : (prefixWord ++ tailWord_1145074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145074).length < 2 ^ (prefixWord ++ tailWord_1145074).sum := by decide
  have hdescent : baseEnd_1145074 < baseStart_1145074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145120 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 7]
def baseStart_1145120 : Nat := 118140960795 + 1145120 * 2 ^ 59
def prefixEnd_1145120 : Nat := 4983230072969 + 3 ^ 40 * 1145120 * 2
def baseEnd_1145120 : Nat := 65332996341851660714855

theorem tailTrace_1145120 : CollatzResearch.WordTrace tailWord_1145120 prefixEnd_1145120 65332996341851660714855 := by
  unfold tailWord_1145120
  simp only [CollatzResearch.WordTrace]
  refine ⟨20882978805716642885456407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27843971740955523847275209 20882978805716642885456407)
  ·
    refine ⟨31324468208574964328184611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20882978805716642885456407 31324468208574964328184611)
    ·
      refine ⟨46986702312862446492276917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31324468208574964328184611 46986702312862446492276917)
      ·
        refine ⟨4405003341830854358650961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46986702312862446492276917 4405003341830854358650961)
        ·
          refine ⟨3303752506373140768988221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4405003341830854358650961 3303752506373140768988221)
          ·
            refine ⟨1238907189889927788370583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3303752506373140768988221 1238907189889927788370583)
            ·
              refine ⟨1858360784834891682555875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1238907189889927788370583 1858360784834891682555875)
              ·
                refine ⟨2787541177252337523833813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858360784834891682555875 2787541177252337523833813)
                ·
                  refine ⟨65332996341851660714855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2787541177252337523833813 65332996341851660714855)
                  ·
                    rfl

theorem cell23_1145120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_1145120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145120 prefixEnd_1145120 := by exact prefixLift 1145120
  have htrace : WordTrace (prefixWord ++ tailWord_1145120) baseStart_1145120 baseEnd_1145120 := by
    simpa [prefixWord, tailWord_1145120, baseEnd_1145120] using wordTrace_append hprefix tailTrace_1145120
  have hstable : (prefixWord ++ tailWord_1145120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145120).length < 2 ^ (prefixWord ++ tailWord_1145120).sum := by decide
  have hdescent : baseEnd_1145120 < baseStart_1145120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145150 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1145150 : Nat := 118140960795 + 1145150 * 2 ^ 59
def prefixEnd_1145150 : Nat := 4983230072969 + 3 ^ 40 * 1145150 * 2
def baseEnd_1145150 : Nat := 196004123832099943019519

theorem tailTrace_1145150 : CollatzResearch.WordTrace tailWord_1145150 prefixEnd_1145150 196004123832099943019519 := by
  unfold tailWord_1145150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220881475165575111813113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27844701200883067263003269 5220881475165575111813113)
  ·
    refine ⟨3915661106374181333859835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5220881475165575111813113 3915661106374181333859835)
    ·
      refine ⟨5873491659561272000789753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3915661106374181333859835 5873491659561272000789753)
      ·
        refine ⟨4405118744670954000592315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5873491659561272000789753 4405118744670954000592315)
        ·
          refine ⟨6607678117006431000888473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4405118744670954000592315 6607678117006431000888473)
          ·
            refine ⟨4955758587754823250666355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6607678117006431000888473 4955758587754823250666355)
            ·
              refine ⟨7433637881632234875999533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4955758587754823250666355 7433637881632234875999533)
              ·
                refine ⟨2787614205612088078499825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7433637881632234875999533 2787614205612088078499825)
                ·
                  refine ⟨2090710654209066058874869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2787614205612088078499825 2090710654209066058874869)
                  ·
                    refine ⟨196004123832099943019519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2090710654209066058874869 196004123832099943019519)
                    ·
                      rfl

theorem cell23_1145150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1145150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145150 prefixEnd_1145150 := by exact prefixLift 1145150
  have htrace : WordTrace (prefixWord ++ tailWord_1145150) baseStart_1145150 baseEnd_1145150 := by
    simpa [prefixWord, tailWord_1145150, baseEnd_1145150] using wordTrace_append hprefix tailTrace_1145150
  have hstable : (prefixWord ++ tailWord_1145150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145150).length < 2 ^ (prefixWord ++ tailWord_1145150).sum := by decide
  have hdescent : baseEnd_1145150 < baseStart_1145150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145163 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 7, 4]
def baseStart_1145163 : Nat := 118140960795 + 1145163 * 2 ^ 59
def prefixEnd_1145163 : Nat := 4983230072969 + 3 ^ 40 * 1145163 * 2
def baseEnd_1145163 : Nat := 196006348914936092731999

theorem tailTrace_1145163 : CollatzResearch.WordTrace tailWord_1145163 prefixEnd_1145163 196006348914936092731999 := by
  unfold tailWord_1145163
  simp only [CollatzResearch.WordTrace]
  refine ⟨41767525950277504114728143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27845017300185002743152095 41767525950277504114728143)
  ·
    refine ⟨62651288925416256172092215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41767525950277504114728143 62651288925416256172092215)
    ·
      refine ⟨93976933388124384258138323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62651288925416256172092215 93976933388124384258138323)
      ·
        refine ⟨140965400082186576387207485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93976933388124384258138323 140965400082186576387207485)
        ·
          refine ⟨52862025030819966145202807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140965400082186576387207485 52862025030819966145202807)
          ·
            refine ⟨79293037546229949217804211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52862025030819966145202807 79293037546229949217804211)
            ·
              refine ⟨118939556319344923826706317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79293037546229949217804211 118939556319344923826706317)
              ·
                refine ⟨44602333619754346435014869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118939556319344923826706317 44602333619754346435014869)
                ·
                  refine ⟨1045367194212992494570661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44602333619754346435014869 1045367194212992494570661)
                  ·
                    refine ⟨196006348914936092731999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045367194212992494570661 196006348914936092731999)
                    ·
                      rfl

theorem cell23_1145163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 4].length) (baseStart_1145163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145163 prefixEnd_1145163 := by exact prefixLift 1145163
  have htrace : WordTrace (prefixWord ++ tailWord_1145163) baseStart_1145163 baseEnd_1145163 := by
    simpa [prefixWord, tailWord_1145163, baseEnd_1145163] using wordTrace_append hprefix tailTrace_1145163
  have hstable : (prefixWord ++ tailWord_1145163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145163).length < 2 ^ (prefixWord ++ tailWord_1145163).sum := by decide
  have hdescent : baseEnd_1145163 < baseStart_1145163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145170 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_1145170 : Nat := 118140960795 + 1145170 * 2 ^ 59
def prefixEnd_1145170 : Nat := 4983230072969 + 3 ^ 40 * 1145170 * 2
def baseEnd_1145170 : Nat := 588022641109389750808465

theorem tailTrace_1145170 : CollatzResearch.WordTrace tailWord_1145170 prefixEnd_1145170 588022641109389750808465 := by
  unfold tailWord_1145170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10441945315313036077558241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27845187507501429540155309 10441945315313036077558241)
  ·
    refine ⟨7831458986484777058168681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10441945315313036077558241 7831458986484777058168681)
    ·
      refine ⟨5873594239863582793626511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7831458986484777058168681 5873594239863582793626511)
      ·
        refine ⟨8810391359795374190439767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873594239863582793626511 8810391359795374190439767)
        ·
          refine ⟨13215587039693061285659651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8810391359795374190439767 13215587039693061285659651)
          ·
            refine ⟨19823380559539591928489477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13215587039693061285659651 19823380559539591928489477)
            ·
              refine ⟨3716883854913673486591777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19823380559539591928489477 3716883854913673486591777)
              ·
                refine ⟨2787662891185255114943833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3716883854913673486591777 2787662891185255114943833)
                ·
                  refine ⟨2090747168388941336207875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2787662891185255114943833 2090747168388941336207875)
                  ·
                    refine ⟨3136120752583412004311813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090747168388941336207875 3136120752583412004311813)
                    ·
                      refine ⟨588022641109389750808465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3136120752583412004311813 588022641109389750808465)
                      ·
                        rfl

theorem cell23_1145170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_1145170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145170 prefixEnd_1145170 := by exact prefixLift 1145170
  have htrace : WordTrace (prefixWord ++ tailWord_1145170) baseStart_1145170 baseEnd_1145170 := by
    simpa [prefixWord, tailWord_1145170, baseEnd_1145170] using wordTrace_append hprefix tailTrace_1145170
  have hstable : (prefixWord ++ tailWord_1145170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145170).length < 2 ^ (prefixWord ++ tailWord_1145170).sum := by decide
  have hdescent : baseEnd_1145170 < baseStart_1145170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145193 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 6]
def baseStart_1145193 : Nat := 118140960795 + 1145193 * 2 ^ 59
def prefixEnd_1145193 : Nat := 4983230072969 + 3 ^ 40 * 1145193 * 2
def baseEnd_1145193 : Nat := 65337161240493684535651

theorem tailTrace_1145193 : CollatzResearch.WordTrace tailWord_1145193 prefixEnd_1145193 65337161240493684535651 := by
  unfold tailWord_1145193
  simp only [CollatzResearch.WordTrace]
  refine ⟨41768620140168819238320233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27845746760112546158880155 41768620140168819238320233)
  ·
    refine ⟨31326465105126614428740175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41768620140168819238320233 31326465105126614428740175)
    ·
      refine ⟨46989697657689921643110263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31326465105126614428740175 46989697657689921643110263)
      ·
        refine ⟨70484546486534882464665395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46989697657689921643110263 70484546486534882464665395)
        ·
          refine ⟨105726819729802323696998093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70484546486534882464665395 105726819729802323696998093)
          ·
            refine ⟨39647557398675871386374285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105726819729802323696998093 39647557398675871386374285)
            ·
              refine ⟨14867834024503451769890357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39647557398675871386374285 14867834024503451769890357)
              ·
                refine ⟨1393859439797198603427221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14867834024503451769890357 1393859439797198603427221)
                ·
                  refine ⟨65337161240493684535651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1393859439797198603427221 65337161240493684535651)
                  ·
                    rfl

theorem cell23_1145193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_1145193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145193 prefixEnd_1145193 := by exact prefixLift 1145193
  have htrace : WordTrace (prefixWord ++ tailWord_1145193) baseStart_1145193 baseEnd_1145193 := by
    simpa [prefixWord, tailWord_1145193, baseEnd_1145193] using wordTrace_append hprefix tailTrace_1145193
  have hstable : (prefixWord ++ tailWord_1145193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145193).length < 2 ^ (prefixWord ++ tailWord_1145193).sum := by decide
  have hdescent : baseEnd_1145193 < baseStart_1145193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145203 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3]
def baseStart_1145203 : Nat := 118140960795 + 1145203 * 2 ^ 59
def prefixEnd_1145203 : Nat := 4983230072969 + 3 ^ 40 * 1145203 * 2
def baseEnd_1145203 : Nat := 588039585970988121695813

theorem tailTrace_1145203 : CollatzResearch.WordTrace tailWord_1145203 prefixEnd_1145203 588039585970988121695813 := by
  unfold tailWord_1145203
  simp only [CollatzResearch.WordTrace]
  refine ⟨41768984870132590946184263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27845989913421727297456175 41768984870132590946184263)
  ·
    refine ⟨62653477305198886419276395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41768984870132590946184263 62653477305198886419276395)
    ·
      refine ⟨93980215957798329628914593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62653477305198886419276395 93980215957798329628914593)
      ·
        refine ⟨70485161968348747221685945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93980215957798329628914593 70485161968348747221685945)
        ·
          refine ⟨52863871476261560416264459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70485161968348747221685945 52863871476261560416264459)
          ·
            refine ⟨79295807214392340624396689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52863871476261560416264459 79295807214392340624396689)
            ·
              refine ⟨59471855410794255468297517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79295807214392340624396689 59471855410794255468297517)
              ·
                refine ⟨22301945779047845800611569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59471855410794255468297517 22301945779047845800611569)
                ·
                  refine ⟨16726459334285884350458677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22301945779047845800611569 16726459334285884350458677)
                  ·
                    refine ⟨1568105562589301657855501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16726459334285884350458677 1568105562589301657855501)
                    ·
                      refine ⟨588039585970988121695813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568105562589301657855501 588039585970988121695813)
                      ·
                        rfl

theorem cell23_1145203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_1145203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145203 prefixEnd_1145203 := by exact prefixLift 1145203
  have htrace : WordTrace (prefixWord ++ tailWord_1145203) baseStart_1145203 baseEnd_1145203 := by
    simpa [prefixWord, tailWord_1145203, baseEnd_1145203] using wordTrace_append hprefix tailTrace_1145203
  have hstable : (prefixWord ++ tailWord_1145203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145203).length < 2 ^ (prefixWord ++ tailWord_1145203).sum := by decide
  have hdescent : baseEnd_1145203 < baseStart_1145203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145230 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1145230 : Nat := 118140960795 + 1145230 * 2 ^ 59
def prefixEnd_1145230 : Nat := 4983230072969 + 3 ^ 40 * 1145230 * 2
def baseEnd_1145230 : Nat := 588053449948659516058189

theorem tailTrace_1145230 : CollatzResearch.WordTrace tailWord_1145230 prefixEnd_1145230 588053449948659516058189 := by
  unfold tailWord_1145230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5221246205129346819677143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27846646427356516371611429 5221246205129346819677143)
  ·
    refine ⟨7831869307694020229515715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5221246205129346819677143 7831869307694020229515715)
    ·
      refine ⟨11747803961541030344273573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7831869307694020229515715 11747803961541030344273573)
      ·
        refine ⟨2202713242788943189551295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11747803961541030344273573 2202713242788943189551295)
        ·
          refine ⟨3304069864183414784326943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202713242788943189551295 3304069864183414784326943)
          ·
            refine ⟨4956104796275122176490415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304069864183414784326943 4956104796275122176490415)
            ·
              refine ⟨7434157194412683264735623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4956104796275122176490415 7434157194412683264735623)
              ·
                refine ⟨11151235791619024897103435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7434157194412683264735623 11151235791619024897103435)
                ·
                  refine ⟨16726853687428537345655153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11151235791619024897103435 16726853687428537345655153)
                  ·
                    refine ⟨12545140265571403009241365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16726853687428537345655153 12545140265571403009241365)
                    ·
                      refine ⟨588053449948659516058189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12545140265571403009241365 588053449948659516058189)
                      ·
                        rfl

theorem cell23_1145230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1145230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145230 prefixEnd_1145230 := by exact prefixLift 1145230
  have htrace : WordTrace (prefixWord ++ tailWord_1145230) baseStart_1145230 baseEnd_1145230 := by
    simpa [prefixWord, tailWord_1145230, baseEnd_1145230] using wordTrace_append hprefix tailTrace_1145230
  have hstable : (prefixWord ++ tailWord_1145230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145230).length < 2 ^ (prefixWord ++ tailWord_1145230).sum := by decide
  have hdescent : baseEnd_1145230 < baseStart_1145230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145260 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_1145260 : Nat := 118140960795 + 1145260 * 2 ^ 59
def prefixEnd_1145260 : Nat := 4983230072969 + 3 ^ 40 * 1145260 * 2
def baseEnd_1145260 : Nat := 588068854368294398683051

theorem tailTrace_1145260 : CollatzResearch.WordTrace tailWord_1145260 prefixEnd_1145260 588068854368294398683051 := by
  unfold tailWord_1145260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20885531915463044840504617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27847375887284059787339489 20885531915463044840504617)
  ·
    refine ⟨15664148936597283630378463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20885531915463044840504617 15664148936597283630378463)
    ·
      refine ⟨23496223404895925445567695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15664148936597283630378463 23496223404895925445567695)
      ·
        refine ⟨35244335107343888168351543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23496223404895925445567695 35244335107343888168351543)
        ·
          refine ⟨52866502661015832252527315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35244335107343888168351543 52866502661015832252527315)
          ·
            refine ⟨79299753991523748378790973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52866502661015832252527315 79299753991523748378790973)
            ·
              refine ⟨29737407746821405642046615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79299753991523748378790973 29737407746821405642046615)
              ·
                refine ⟨44606111620232108463069923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29737407746821405642046615 44606111620232108463069923)
                ·
                  refine ⟨66909167430348162694604885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44606111620232108463069923 66909167430348162694604885)
                  ·
                    refine ⟨784091805824392531577401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66909167430348162694604885 784091805824392531577401)
                    ·
                      refine ⟨588068854368294398683051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784091805824392531577401 588068854368294398683051)
                      ·
                        rfl

theorem cell23_1145260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_1145260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145260 prefixEnd_1145260 := by exact prefixLift 1145260
  have htrace : WordTrace (prefixWord ++ tailWord_1145260) baseStart_1145260 baseEnd_1145260 := by
    simpa [prefixWord, tailWord_1145260, baseEnd_1145260] using wordTrace_append hprefix tailTrace_1145260
  have hstable : (prefixWord ++ tailWord_1145260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145260).length < 2 ^ (prefixWord ++ tailWord_1145260).sum := by decide
  have hdescent : baseEnd_1145260 < baseStart_1145260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145271 : List Nat := [1, 1, 3, 1, 3, 5, 1, 3, 1, 1, 3]
def baseStart_1145271 : Nat := 118140960795 + 1145271 * 2 ^ 59
def prefixEnd_1145271 : Nat := 4983230072969 + 3 ^ 40 * 1145271 * 2
def baseEnd_1145271 : Nat := 588074502655493855645501

theorem tailTrace_1145271 : CollatzResearch.WordTrace tailWord_1145271 prefixEnd_1145271 588074502655493855645501 := by
  unfold tailWord_1145271
  simp only [CollatzResearch.WordTrace]
  refine ⟨41771465033886238559659667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27847643355924159039773111 41771465033886238559659667)
  ·
    refine ⟨62657197550829357839489501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41771465033886238559659667 62657197550829357839489501)
    ·
      refine ⟨23496449081561009189808563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62657197550829357839489501 23496449081561009189808563)
      ·
        refine ⟨35244673622341513784712845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23496449081561009189808563 35244673622341513784712845)
        ·
          refine ⟨13216752608378067669267317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35244673622341513784712845 13216752608378067669267317)
          ·
            refine ⟨1239070557035443843993811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13216752608378067669267317 1239070557035443843993811)
            ·
              refine ⟨1858605835553165765990717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239070557035443843993811 1858605835553165765990717)
              ·
                refine ⟨696977188332437162246519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1858605835553165765990717 696977188332437162246519)
                ·
                  refine ⟨1045465782498655743369779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696977188332437162246519 1045465782498655743369779)
                  ·
                    refine ⟨1568198673747983615054669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045465782498655743369779 1568198673747983615054669)
                    ·
                      refine ⟨588074502655493855645501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568198673747983615054669 588074502655493855645501)
                      ·
                        rfl

theorem cell23_1145271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 3, 1, 1, 3].length) (baseStart_1145271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145271 prefixEnd_1145271 := by exact prefixLift 1145271
  have htrace : WordTrace (prefixWord ++ tailWord_1145271) baseStart_1145271 baseEnd_1145271 := by
    simpa [prefixWord, tailWord_1145271, baseEnd_1145271] using wordTrace_append hprefix tailTrace_1145271
  have hstable : (prefixWord ++ tailWord_1145271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145271).length < 2 ^ (prefixWord ++ tailWord_1145271).sum := by decide
  have hdescent : baseEnd_1145271 < baseStart_1145271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145277 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_1145277 : Nat := 118140960795 + 1145277 * 2 ^ 59
def prefixEnd_1145277 : Nat := 4983230072969 + 3 ^ 40 * 1145277 * 2
def baseEnd_1145277 : Nat := 588077583539420832170473

theorem tailTrace_1145277 : CollatzResearch.WordTrace tailWord_1145277 prefixEnd_1145277 588077583539420832170473 := by
  unfold tailWord_1145277
  simp only [CollatzResearch.WordTrace]
  refine ⟨41771683871864501584378085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27847789247909667722918723 41771683871864501584378085)
  ·
    refine ⟨7832190725974594047070891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41771683871864501584378085 7832190725974594047070891)
    ·
      refine ⟨11748286088961891070606337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7832190725974594047070891 11748286088961891070606337)
      ·
        refine ⟨8811214566721418302954753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11748286088961891070606337 8811214566721418302954753)
        ·
          refine ⟨6608410925041063727216065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8811214566721418302954753 6608410925041063727216065)
          ·
            refine ⟨4956308193780797795412049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6608410925041063727216065 4956308193780797795412049)
            ·
              refine ⟨3717231145335598346559037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4956308193780797795412049 3717231145335598346559037)
              ·
                refine ⟨1393961679500849379959639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3717231145335598346559037 1393961679500849379959639)
                ·
                  refine ⟨2090942519251274069939459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393961679500849379959639 2090942519251274069939459)
                  ·
                    refine ⟨3136413778876911104909189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2090942519251274069939459 3136413778876911104909189)
                    ·
                      refine ⟨588077583539420832170473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3136413778876911104909189 588077583539420832170473)
                      ·
                        rfl

theorem cell23_1145277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_1145277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145277 prefixEnd_1145277 := by exact prefixLift 1145277
  have htrace : WordTrace (prefixWord ++ tailWord_1145277) baseStart_1145277 baseEnd_1145277 := by
    simpa [prefixWord, tailWord_1145277, baseEnd_1145277] using wordTrace_append hprefix tailTrace_1145277
  have hstable : (prefixWord ++ tailWord_1145277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145277).length < 2 ^ (prefixWord ++ tailWord_1145277).sum := by decide
  have hdescent : baseEnd_1145277 < baseStart_1145277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145280 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_1145280 : Nat := 118140960795 + 1145280 * 2 ^ 59
def prefixEnd_1145280 : Nat := 4983230072969 + 3 ^ 40 * 1145280 * 2
def baseEnd_1145280 : Nat := 588079123981384320432959

theorem tailTrace_1145280 : CollatzResearch.WordTrace tailWord_1145280 prefixEnd_1145280 588079123981384320432959 := by
  unfold tailWord_1145280
  simp only [CollatzResearch.WordTrace]
  refine ⟨20885896645426816548368647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27847862193902422064491529 20885896645426816548368647)
  ·
    refine ⟨31328844968140224822552971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20885896645426816548368647 31328844968140224822552971)
    ·
      refine ⟨46993267452210337233829457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31328844968140224822552971 46993267452210337233829457)
      ·
        refine ⟨35244950589157752925372093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46993267452210337233829457 35244950589157752925372093)
        ·
          refine ⟨13216856470934157347014535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35244950589157752925372093 13216856470934157347014535)
          ·
            refine ⟨19825284706401236020521803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13216856470934157347014535 19825284706401236020521803)
            ·
              refine ⟨29737927059601854030782705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19825284706401236020521803 29737927059601854030782705)
              ·
                refine ⟨22303445294701390523087029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29737927059601854030782705 22303445294701390523087029)
                ·
                  refine ⟨2090947996378255361539409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22303445294701390523087029 2090947996378255361539409)
                  ·
                    refine ⟨1568210997283691521154557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2090947996378255361539409 1568210997283691521154557)
                    ·
                      refine ⟨588079123981384320432959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568210997283691521154557 588079123981384320432959)
                      ·
                        rfl

theorem cell23_1145280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_1145280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145280 prefixEnd_1145280 := by exact prefixLift 1145280
  have htrace : WordTrace (prefixWord ++ tailWord_1145280) baseStart_1145280 baseEnd_1145280 := by
    simpa [prefixWord, tailWord_1145280, baseEnd_1145280] using wordTrace_append hprefix tailTrace_1145280
  have hstable : (prefixWord ++ tailWord_1145280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145280).length < 2 ^ (prefixWord ++ tailWord_1145280).sum := by decide
  have hdescent : baseEnd_1145280 < baseStart_1145280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145300 : List Nat := [2, 4, 1, 2, 2, 1, 1, 10]
def baseStart_1145300 : Nat := 118140960795 + 1145300 * 2 ^ 59
def prefixEnd_1145300 : Nat := 4983230072969 + 3 ^ 40 * 1145300 * 2
def baseEnd_1145300 : Nat := 21781088651647194154921

theorem tailTrace_1145300 : CollatzResearch.WordTrace tailWord_1145300 prefixEnd_1145300 21781088651647194154921 := by
  unfold tailWord_1145300
  simp only [CollatzResearch.WordTrace]
  refine ⟨20886261375390588256232677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27848348500520784341643569 20886261375390588256232677)
  ·
    refine ⟨3916174007885735298043627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20886261375390588256232677 3916174007885735298043627)
    ·
      refine ⟨5874261011828602947065441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3916174007885735298043627 5874261011828602947065441)
      ·
        refine ⟨4405695758871452210299081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5874261011828602947065441 4405695758871452210299081)
        ·
          refine ⟨3304271819153589157724311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4405695758871452210299081 3304271819153589157724311)
          ·
            refine ⟨4956407728730383736586467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3304271819153589157724311 4956407728730383736586467)
            ·
              refine ⟨7434611593095575604879701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4956407728730383736586467 7434611593095575604879701)
              ·
                refine ⟨21781088651647194154921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7434611593095575604879701 21781088651647194154921)
                ·
                  rfl

theorem cell23_1145300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 10].length) (baseStart_1145300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145300 prefixEnd_1145300 := by exact prefixLift 1145300
  have htrace : WordTrace (prefixWord ++ tailWord_1145300) baseStart_1145300 baseEnd_1145300 := by
    simpa [prefixWord, tailWord_1145300, baseEnd_1145300] using wordTrace_append hprefix tailTrace_1145300
  have hstable : (prefixWord ++ tailWord_1145300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145300).length < 2 ^ (prefixWord ++ tailWord_1145300).sum := by decide
  have hdescent : baseEnd_1145300 < baseStart_1145300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145345 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_1145345 : Nat := 118140960795 + 1145345 * 2 ^ 59
def prefixEnd_1145345 : Nat := 4983230072969 + 3 ^ 40 * 1145345 * 2
def baseEnd_1145345 : Nat := 588112500223926566120161

theorem tailTrace_1145345 : CollatzResearch.WordTrace tailWord_1145345 prefixEnd_1145345 588112500223926566120161 := by
  unfold tailWord_1145345
  simp only [CollatzResearch.WordTrace]
  refine ⟨41774164035618149197853489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27849442690412099465235659 41774164035618149197853489)
  ·
    refine ⟨31330623026713611898390117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41774164035618149197853489 31330623026713611898390117)
    ·
      refine ⟨5874491817508802230948147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31330623026713611898390117 5874491817508802230948147)
      ·
        refine ⟨8811737726263203346422221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5874491817508802230948147 8811737726263203346422221)
        ·
          refine ⟨3304401647348701254908333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8811737726263203346422221 3304401647348701254908333)
          ·
            refine ⟨1239150617755762970590625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3304401647348701254908333 1239150617755762970590625)
            ·
              refine ⟨929362963316822227942969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239150617755762970590625 929362963316822227942969)
              ·
                refine ⟨697022222487616670957227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929362963316822227942969 697022222487616670957227)
                ·
                  refine ⟨1045533333731425006435841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697022222487616670957227 1045533333731425006435841)
                  ·
                    refine ⟨784150000298568754826881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1045533333731425006435841 784150000298568754826881)
                    ·
                      refine ⟨588112500223926566120161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784150000298568754826881 588112500223926566120161)
                      ·
                        rfl

theorem cell23_1145345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_1145345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145345 prefixEnd_1145345 := by exact prefixLift 1145345
  have htrace : WordTrace (prefixWord ++ tailWord_1145345) baseStart_1145345 baseEnd_1145345 := by
    simpa [prefixWord, tailWord_1145345, baseEnd_1145345] using wordTrace_append hprefix tailTrace_1145345
  have hstable : (prefixWord ++ tailWord_1145345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145345).length < 2 ^ (prefixWord ++ tailWord_1145345).sum := by decide
  have hdescent : baseEnd_1145345 < baseStart_1145345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145370 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1145370 : Nat := 118140960795 + 1145370 * 2 ^ 59
def prefixEnd_1145370 : Nat := 4983230072969 + 3 ^ 40 * 1145370 * 2
def baseEnd_1145370 : Nat := 588125337240288968307545

theorem tailTrace_1145370 : CollatzResearch.WordTrace tailWord_1145370 prefixEnd_1145370 588125337240288968307545 := by
  unfold tailWord_1145370
  simp only [CollatzResearch.WordTrace]
  refine ⟨10443768965131894616878391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27850050573685052311675709 10443768965131894616878391)
  ·
    refine ⟨15665653447697841925317587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10443768965131894616878391 15665653447697841925317587)
    ·
      refine ⟨23498480171546762887976381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15665653447697841925317587 23498480171546762887976381)
      ·
        refine ⟨8811930064330036082991143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23498480171546762887976381 8811930064330036082991143)
        ·
          refine ⟨13217895096495054124486715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8811930064330036082991143 13217895096495054124486715)
          ·
            refine ⟨19826842644742581186730073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13217895096495054124486715 19826842644742581186730073)
            ·
              refine ⟨14870131983556935890047555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19826842644742581186730073 14870131983556935890047555)
              ·
                refine ⟨22305197975335403835071333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14870131983556935890047555 22305197975335403835071333)
                ·
                  refine ⟨4182224620375388219075875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22305197975335403835071333 4182224620375388219075875)
                  ·
                    refine ⟨6273336930563082328613813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182224620375388219075875 6273336930563082328613813)
                    ·
                      refine ⟨588125337240288968307545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6273336930563082328613813 588125337240288968307545)
                      ·
                        rfl

theorem cell23_1145370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1145370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145370 prefixEnd_1145370 := by exact prefixLift 1145370
  have htrace : WordTrace (prefixWord ++ tailWord_1145370) baseStart_1145370 baseEnd_1145370 := by
    simpa [prefixWord, tailWord_1145370, baseEnd_1145370] using wordTrace_append hprefix tailTrace_1145370
  have hstable : (prefixWord ++ tailWord_1145370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145370).length < 2 ^ (prefixWord ++ tailWord_1145370).sum := by decide
  have hdescent : baseEnd_1145370 < baseStart_1145370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145407 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 5]
def baseStart_1145407 : Nat := 118140960795 + 1145407 * 2 ^ 59
def prefixEnd_1145407 : Nat := 4983230072969 + 3 ^ 40 * 1145407 * 2
def baseEnd_1145407 : Nat := 65349370669389480393875

theorem tailTrace_1145407 : CollatzResearch.WordTrace tailWord_1145407 prefixEnd_1145407 65349370669389480393875 := by
  unfold tailWord_1145407
  simp only [CollatzResearch.WordTrace]
  refine ⟨41776425361393533786610475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27850950240929022524406983 41776425361393533786610475)
  ·
    refine ⟨62664638042090300679915713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41776425361393533786610475 62664638042090300679915713)
    ·
      refine ⟨46998478531567725509936785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62664638042090300679915713 46998478531567725509936785)
      ·
        refine ⟨35248858898675794132452589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46998478531567725509936785 35248858898675794132452589)
        ·
          refine ⟨13218322087003422799669721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35248858898675794132452589 13218322087003422799669721)
          ·
            refine ⟨9913741565252567099752291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13218322087003422799669721 9913741565252567099752291)
            ·
              refine ⟨14870612347878850649628437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913741565252567099752291 14870612347878850649628437)
              ·
                refine ⟨697059953806821124201333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14870612347878850649628437 697059953806821124201333)
                ·
                  refine ⟨65349370669389480393875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697059953806821124201333 65349370669389480393875)
                  ·
                    rfl

theorem cell23_1145407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 5].length) (baseStart_1145407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145407 prefixEnd_1145407 := by exact prefixLift 1145407
  have htrace : WordTrace (prefixWord ++ tailWord_1145407) baseStart_1145407 baseEnd_1145407 := by
    simpa [prefixWord, tailWord_1145407, baseEnd_1145407] using wordTrace_append hprefix tailTrace_1145407
  have hstable : (prefixWord ++ tailWord_1145407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145407).length < 2 ^ (prefixWord ++ tailWord_1145407).sum := by decide
  have hdescent : baseEnd_1145407 < baseStart_1145407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145412 : List Nat := [2, 3, 5, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1145412 : Nat := 118140960795 + 1145412 * 2 ^ 59
def prefixEnd_1145412 : Nat := 4983230072969 + 3 ^ 40 * 1145412 * 2
def baseEnd_1145412 : Nat := 588146903427777803982353

theorem tailTrace_1145412 : CollatzResearch.WordTrace tailWord_1145412 prefixEnd_1145412 588146903427777803982353 := by
  unfold tailWord_1145412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888303863187709820271245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27851071817583613093694993 20888303863187709820271245)
  ·
    refine ⟨7833113948695391182601717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20888303863187709820271245 7833113948695391182601717)
    ·
      refine ⟨734354432690192923368911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7833113948695391182601717 734354432690192923368911)
      ·
        refine ⟨1101531649035289385053367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734354432690192923368911 1101531649035289385053367)
        ·
          refine ⟨1652297473552934077580051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101531649035289385053367 1652297473552934077580051)
          ·
            refine ⟨2478446210329401116370077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652297473552934077580051 2478446210329401116370077)
            ·
              refine ⟨929417328873525418638779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478446210329401116370077 929417328873525418638779)
              ·
                refine ⟨1394125993310288127958169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929417328873525418638779 1394125993310288127958169)
                ·
                  refine ⟨1045594494982716095968627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394125993310288127958169 1045594494982716095968627)
                  ·
                    refine ⟨1568391742474074143952941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045594494982716095968627 1568391742474074143952941)
                    ·
                      refine ⟨588146903427777803982353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568391742474074143952941 588146903427777803982353)
                      ·
                        rfl

theorem cell23_1145412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1145412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145412 prefixEnd_1145412 := by exact prefixLift 1145412
  have htrace : WordTrace (prefixWord ++ tailWord_1145412) baseStart_1145412 baseEnd_1145412 := by
    simpa [prefixWord, tailWord_1145412, baseEnd_1145412] using wordTrace_append hprefix tailTrace_1145412
  have hstable : (prefixWord ++ tailWord_1145412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145412).length < 2 ^ (prefixWord ++ tailWord_1145412).sum := by decide
  have hdescent : baseEnd_1145412 < baseStart_1145412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145418 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_1145418 : Nat := 118140960795 + 1145418 * 2 ^ 59
def prefixEnd_1145418 : Nat := 4983230072969 + 3 ^ 40 * 1145418 * 2
def baseEnd_1145418 : Nat := 588149984311704780507325

theorem tailTrace_1145418 : CollatzResearch.WordTrace tailWord_1145418 prefixEnd_1145418 588149984311704780507325 := by
  unfold tailWord_1145418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10444206641088420666315227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27851217709569121776840605 10444206641088420666315227)
  ·
    refine ⟨15666309961632630999472841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10444206641088420666315227 15666309961632630999472841)
    ·
      refine ⟨11749732471224473249604631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15666309961632630999472841 11749732471224473249604631)
      ·
        refine ⟨17624598706836709874406947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11749732471224473249604631 17624598706836709874406947)
        ·
          refine ⟨26436898060255064811610421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17624598706836709874406947 26436898060255064811610421)
          ·
            refine ⟨2478459193148912326088477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26436898060255064811610421 2478459193148912326088477)
            ·
              refine ⟨929422197430842122283179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478459193148912326088477 929422197430842122283179)
              ·
                refine ⟨1394133296146263183424769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929422197430842122283179 1394133296146263183424769)
                ·
                  refine ⟨1045599972109697387568577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394133296146263183424769 1045599972109697387568577)
                  ·
                    refine ⟨784199979082273040676433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1045599972109697387568577 784199979082273040676433)
                    ·
                      refine ⟨588149984311704780507325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784199979082273040676433 588149984311704780507325)
                      ·
                        rfl

theorem cell23_1145418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_1145418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145418 prefixEnd_1145418 := by exact prefixLift 1145418
  have htrace : WordTrace (prefixWord ++ tailWord_1145418) baseStart_1145418 baseEnd_1145418 := by
    simpa [prefixWord, tailWord_1145418, baseEnd_1145418] using wordTrace_append hprefix tailTrace_1145418
  have hstable : (prefixWord ++ tailWord_1145418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145418).length < 2 ^ (prefixWord ++ tailWord_1145418).sum := by decide
  have hdescent : baseEnd_1145418 < baseStart_1145418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145420 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_1145420 : Nat := 118140960795 + 1145420 * 2 ^ 59
def prefixEnd_1145420 : Nat := 4983230072969 + 3 ^ 40 * 1145420 * 2
def baseEnd_1145420 : Nat := 196050337091004590894105

theorem tailTrace_1145420 : CollatzResearch.WordTrace tailWord_1145420 prefixEnd_1145420 196050337091004590894105 := by
  unfold tailWord_1145420
  simp only [CollatzResearch.WordTrace]
  refine ⟨20888449755173218503416857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27851266340230958004555809 20888449755173218503416857)
  ·
    refine ⟨15666337316379913877562643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20888449755173218503416857 15666337316379913877562643)
    ·
      refine ⟨23499505974569870816343965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666337316379913877562643 23499505974569870816343965)
      ·
        refine ⟨8812314740463701556128987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23499505974569870816343965 8812314740463701556128987)
        ·
          refine ⟨13218472110695552334193481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812314740463701556128987 13218472110695552334193481)
          ·
            refine ⟨9913854083021664250645111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13218472110695552334193481 9913854083021664250645111)
            ·
              refine ⟨14870781124532496375967667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9913854083021664250645111 14870781124532496375967667)
              ·
                refine ⟨22306171686798744563951501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14870781124532496375967667 22306171686798744563951501)
                ·
                  refine ⟨8364814382549529211481813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22306171686798744563951501 8364814382549529211481813)
                  ·
                    refine ⟨196050337091004590894105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8364814382549529211481813 196050337091004590894105)
                    ·
                      rfl

theorem cell23_1145420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_1145420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145420 prefixEnd_1145420 := by exact prefixLift 1145420
  have htrace : WordTrace (prefixWord ++ tailWord_1145420) baseStart_1145420 baseEnd_1145420 := by
    simpa [prefixWord, tailWord_1145420, baseEnd_1145420] using wordTrace_append hprefix tailTrace_1145420
  have hstable : (prefixWord ++ tailWord_1145420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145420).length < 2 ^ (prefixWord ++ tailWord_1145420).sum := by decide
  have hdescent : baseEnd_1145420 < baseStart_1145420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145438 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1145438 : Nat := 118140960795 + 1145438 * 2 ^ 59
def prefixEnd_1145438 : Nat := 4983230072969 + 3 ^ 40 * 1145438 * 2
def baseEnd_1145438 : Nat := 588160253924794702257233

theorem tailTrace_1145438 : CollatzResearch.WordTrace tailWord_1145438 prefixEnd_1145438 588160253924794702257233 := by
  unfold tailWord_1145438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222194503035153260123621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27851704016187484053992645 5222194503035153260123621)
  ·
    refine ⟨979161469319091236273179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5222194503035153260123621 979161469319091236273179)
    ·
      refine ⟨1468742203978636854409769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 979161469319091236273179 1468742203978636854409769)
      ·
        refine ⟨1101556652983977640807327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468742203978636854409769 1101556652983977640807327)
        ·
          refine ⟨1652334979475966461210991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101556652983977640807327 1652334979475966461210991)
          ·
            refine ⟨2478502469213949691816487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652334979475966461210991 2478502469213949691816487)
            ·
              refine ⟨3717753703820924537724731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478502469213949691816487 3717753703820924537724731)
              ·
                refine ⟨5576630555731386806587097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717753703820924537724731 5576630555731386806587097)
                ·
                  refine ⟨4182472916798540104940323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576630555731386806587097 4182472916798540104940323)
                  ·
                    refine ⟨6273709375197810157410485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4182472916798540104940323 6273709375197810157410485)
                    ·
                      refine ⟨588160253924794702257233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6273709375197810157410485 588160253924794702257233)
                      ·
                        rfl

theorem cell23_1145438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1145438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145438 prefixEnd_1145438 := by exact prefixLift 1145438
  have htrace : WordTrace (prefixWord ++ tailWord_1145438) baseStart_1145438 baseEnd_1145438 := by
    simpa [prefixWord, tailWord_1145438, baseEnd_1145438] using wordTrace_append hprefix tailTrace_1145438
  have hstable : (prefixWord ++ tailWord_1145438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145438).length < 2 ^ (prefixWord ++ tailWord_1145438).sum := by decide
  have hdescent : baseEnd_1145438 < baseStart_1145438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145454 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_1145454 : Nat := 118140960795 + 1145454 * 2 ^ 59
def prefixEnd_1145454 : Nat := 4983230072969 + 3 ^ 40 * 1145454 * 2
def baseEnd_1145454 : Nat := 196056156538422213219053

theorem tailTrace_1145454 : CollatzResearch.WordTrace tailWord_1145454 prefixEnd_1145454 196056156538422213219053 := by
  unfold tailWord_1145454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222267449027907601696427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27852093061482173875714277 5222267449027907601696427)
  ·
    refine ⟨7833401173541861402544641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222267449027907601696427 7833401173541861402544641)
    ·
      refine ⟨5875050880156396051908481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7833401173541861402544641 5875050880156396051908481)
      ·
        refine ⟨4406288160117297038931361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5875050880156396051908481 4406288160117297038931361)
        ·
          refine ⟨3304716120087972779198521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4406288160117297038931361 3304716120087972779198521)
          ·
            refine ⟨2478537090065979584398891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3304716120087972779198521 2478537090065979584398891)
            ·
              refine ⟨3717805635098969376598337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478537090065979584398891 3717805635098969376598337)
              ·
                refine ⟨2788354226324227032448753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3717805635098969376598337 2788354226324227032448753)
                ·
                  refine ⟨2091265669743170274336565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2788354226324227032448753 2091265669743170274336565)
                  ·
                    refine ⟨196056156538422213219053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2091265669743170274336565 196056156538422213219053)
                    ·
                      rfl

theorem cell23_1145454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_1145454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145454 prefixEnd_1145454 := by exact prefixLift 1145454
  have htrace : WordTrace (prefixWord ++ tailWord_1145454) baseStart_1145454 baseEnd_1145454 := by
    simpa [prefixWord, tailWord_1145454, baseEnd_1145454] using wordTrace_append hprefix tailTrace_1145454
  have hstable : (prefixWord ++ tailWord_1145454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145454).length < 2 ^ (prefixWord ++ tailWord_1145454).sum := by decide
  have hdescent : baseEnd_1145454 < baseStart_1145454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145467 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 3, 4]
def baseStart_1145467 : Nat := 118140960795 + 1145467 * 2 ^ 59
def prefixEnd_1145467 : Nat := 4983230072969 + 3 ^ 40 * 1145467 * 2
def baseEnd_1145467 : Nat := 196058381621258362931533

theorem tailTrace_1145467 : CollatzResearch.WordTrace tailWord_1145467 prefixEnd_1145467 196058381621258362931533 := by
  unfold tailWord_1145467
  simp only [CollatzResearch.WordTrace]
  refine ⟨41778613741176164033794655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27852409160784109355863103 41778613741176164033794655)
  ·
    refine ⟨62667920611764246050691983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41778613741176164033794655 62667920611764246050691983)
    ·
      refine ⟨94001880917646369076037975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62667920611764246050691983 94001880917646369076037975)
      ·
        refine ⟨141002821376469553614056963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94001880917646369076037975 141002821376469553614056963)
        ·
          refine ⟨211504232064704330421085445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141002821376469553614056963 211504232064704330421085445)
          ·
            refine ⟨39657043512132061953953521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211504232064704330421085445 39657043512132061953953521)
            ·
              refine ⟨29742782634099046465465141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39657043512132061953953521 29742782634099046465465141)
              ·
                refine ⟨2788385871946785606137357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29742782634099046465465141 2788385871946785606137357)
                ·
                  refine ⟨1045644701980044602301509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2788385871946785606137357 1045644701980044602301509)
                  ·
                    refine ⟨196058381621258362931533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045644701980044602301509 196058381621258362931533)
                    ·
                      rfl

theorem cell23_1145467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 4].length) (baseStart_1145467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145467 prefixEnd_1145467 := by exact prefixLift 1145467
  have htrace : WordTrace (prefixWord ++ tailWord_1145467) baseStart_1145467 baseEnd_1145467 := by
    simpa [prefixWord, tailWord_1145467, baseEnd_1145467] using wordTrace_append hprefix tailTrace_1145467
  have hstable : (prefixWord ++ tailWord_1145467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145467).length < 2 ^ (prefixWord ++ tailWord_1145467).sum := by decide
  have hdescent : baseEnd_1145467 < baseStart_1145467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145542 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_1145542 : Nat := 118140960795 + 1145542 * 2 ^ 59
def prefixEnd_1145542 : Nat := 4983230072969 + 3 ^ 40 * 1145542 * 2
def baseEnd_1145542 : Nat := 588213655912862295356755

theorem tailTrace_1145542 : CollatzResearch.WordTrace tailWord_1145542 prefixEnd_1145542 588213655912862295356755 := by
  unfold tailWord_1145542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1305667162997014120086715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27854232810602967895183253 1305667162997014120086715)
  ·
    refine ⟨1958500744495521180130073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1305667162997014120086715 1958500744495521180130073)
    ·
      refine ⟨1468875558371640885097555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1958500744495521180130073 1468875558371640885097555)
      ·
        refine ⟨2203313337557461327646333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468875558371640885097555 2203313337557461327646333)
        ·
          refine ⟨826242501584047997867375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2203313337557461327646333 826242501584047997867375)
          ·
            refine ⟨1239363752376071996801063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826242501584047997867375 1239363752376071996801063)
            ·
              refine ⟨1859045628564107995201595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239363752376071996801063 1859045628564107995201595)
              ·
                refine ⟨2788568442846161992802393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859045628564107995201595 2788568442846161992802393)
                ·
                  refine ⟨2091426332134621494601795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2788568442846161992802393 2091426332134621494601795)
                  ·
                    refine ⟨3137139498201932241902693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2091426332134621494601795 3137139498201932241902693)
                    ·
                      refine ⟨588213655912862295356755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3137139498201932241902693 588213655912862295356755)
                      ·
                        rfl

theorem cell23_1145542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_1145542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145542 prefixEnd_1145542 := by exact prefixLift 1145542
  have htrace : WordTrace (prefixWord ++ tailWord_1145542) baseStart_1145542 baseEnd_1145542 := by
    simpa [prefixWord, tailWord_1145542, baseEnd_1145542] using wordTrace_append hprefix tailTrace_1145542
  have hstable : (prefixWord ++ tailWord_1145542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145542).length < 2 ^ (prefixWord ++ tailWord_1145542).sum := by decide
  have hdescent : baseEnd_1145542 < baseStart_1145542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145577 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 4]
def baseStart_1145577 : Nat := 118140960795 + 1145577 * 2 ^ 59
def prefixEnd_1145577 : Nat := 4983230072969 + 3 ^ 40 * 1145577 * 2
def baseEnd_1145577 : Nat := 588231627735769658419093

theorem tailTrace_1145577 : CollatzResearch.WordTrace tailWord_1145577 prefixEnd_1145577 588231627735769658419093 := by
  unfold tailWord_1145577
  simp only [CollatzResearch.WordTrace]
  refine ⟨41782625770777652820298985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27855083847185101880199323 41782625770777652820298985)
  ·
    refine ⟨31336969328083239615224239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41782625770777652820298985 31336969328083239615224239)
    ·
      refine ⟨47005453992124859422836359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31336969328083239615224239 47005453992124859422836359)
      ·
        refine ⟨70508180988187289134254539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47005453992124859422836359 70508180988187289134254539)
        ·
          refine ⟨105762271482280933701381809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70508180988187289134254539 105762271482280933701381809)
          ·
            refine ⟨79321703611710700276036357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105762271482280933701381809 79321703611710700276036357)
            ·
              refine ⟨14872819427195756301756817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79321703611710700276036357 14872819427195756301756817)
              ·
                refine ⟨11154614570396817226317613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14872819427195756301756817 11154614570396817226317613)
                ·
                  refine ⟨4182980463898806459869105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154614570396817226317613 4182980463898806459869105)
                  ·
                    refine ⟨3137235347924104844901829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4182980463898806459869105 3137235347924104844901829)
                    ·
                      refine ⟨588231627735769658419093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3137235347924104844901829 588231627735769658419093)
                      ·
                        rfl

theorem cell23_1145577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_1145577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145577 prefixEnd_1145577 := by exact prefixLift 1145577
  have htrace : WordTrace (prefixWord ++ tailWord_1145577) baseStart_1145577 baseEnd_1145577 := by
    simpa [prefixWord, tailWord_1145577, baseEnd_1145577] using wordTrace_append hprefix tailTrace_1145577
  have hstable : (prefixWord ++ tailWord_1145577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145577).length < 2 ^ (prefixWord ++ tailWord_1145577).sum := by decide
  have hdescent : baseEnd_1145577 < baseStart_1145577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145594 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4]
def baseStart_1145594 : Nat := 118140960795 + 1145594 * 2 ^ 59
def prefixEnd_1145594 : Nat := 4983230072969 + 3 ^ 40 * 1145594 * 2
def baseEnd_1145594 : Nat := 588240356906896091906515

theorem tailTrace_1145594 : CollatzResearch.WordTrace tailWord_1145594 prefixEnd_1145594 588240356906896091906515 := by
  unfold tailWord_1145594
  simp only [CollatzResearch.WordTrace]
  refine ⟨10445811452929016180916959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27855497207810709815778557 10445811452929016180916959)
  ·
    refine ⟨15668717179393524271375439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10445811452929016180916959 15668717179393524271375439)
    ·
      refine ⟨23503075769090286407063159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15668717179393524271375439 23503075769090286407063159)
      ·
        refine ⟨35254613653635429610594739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23503075769090286407063159 35254613653635429610594739)
        ·
          refine ⟨52881920480453144415892109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35254613653635429610594739 52881920480453144415892109)
          ·
            refine ⟨19830720180169929155959541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52881920480453144415892109 19830720180169929155959541)
            ·
              refine ⟨1859130016890930858371207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19830720180169929155959541 1859130016890930858371207)
              ·
                refine ⟨2788695025336396287556811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859130016890930858371207 2788695025336396287556811)
                ·
                  refine ⟨4183042538004594431335217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788695025336396287556811 4183042538004594431335217)
                  ·
                    refine ⟨3137281903503445823501413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4183042538004594431335217 3137281903503445823501413)
                    ·
                      refine ⟨588240356906896091906515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3137281903503445823501413 588240356906896091906515)
                      ·
                        rfl

theorem cell23_1145594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4].length) (baseStart_1145594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145594 prefixEnd_1145594 := by exact prefixLift 1145594
  have htrace : WordTrace (prefixWord ++ tailWord_1145594) baseStart_1145594 baseEnd_1145594 := by
    simpa [prefixWord, tailWord_1145594, baseEnd_1145594] using wordTrace_append hprefix tailTrace_1145594
  have hstable : (prefixWord ++ tailWord_1145594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145594).length < 2 ^ (prefixWord ++ tailWord_1145594).sum := by decide
  have hdescent : baseEnd_1145594 < baseStart_1145594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145598 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1145598 : Nat := 118140960795 + 1145598 * 2 ^ 59
def prefixEnd_1145598 : Nat := 4983230072969 + 3 ^ 40 * 1145598 * 2
def baseEnd_1145598 : Nat := 588242410829514076256497

theorem tailTrace_1145598 : CollatzResearch.WordTrace tailWord_1145598 prefixEnd_1145598 588242410829514076256497 := by
  unfold tailWord_1145598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222923962962696675851681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27855594469134382271208965 5222923962962696675851681)
  ·
    refine ⟨3917192972222022506888761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5222923962962696675851681 3917192972222022506888761)
    ·
      refine ⟨2937894729166516880166571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3917192972222022506888761 2937894729166516880166571)
      ·
        refine ⟨4406842093749775320249857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2937894729166516880166571 4406842093749775320249857)
        ·
          refine ⟨3305131570312331490187393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4406842093749775320249857 3305131570312331490187393)
          ·
            refine ⟨2478848677734248617640545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3305131570312331490187393 2478848677734248617640545)
            ·
              refine ⟨1859136508300686463230409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2478848677734248617640545 1859136508300686463230409)
              ·
                refine ⟨1394352381225514847422807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859136508300686463230409 1394352381225514847422807)
                ·
                  refine ⟨2091528571838272271134211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394352381225514847422807 2091528571838272271134211)
                  ·
                    refine ⟨3137292857757408406701317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2091528571838272271134211 3137292857757408406701317)
                    ·
                      refine ⟨588242410829514076256497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3137292857757408406701317 588242410829514076256497)
                      ·
                        rfl

theorem cell23_1145598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1145598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145598 prefixEnd_1145598 := by exact prefixLift 1145598
  have htrace : WordTrace (prefixWord ++ tailWord_1145598) baseStart_1145598 baseEnd_1145598 := by
    simpa [prefixWord, tailWord_1145598, baseEnd_1145598] using wordTrace_append hprefix tailTrace_1145598
  have hstable : (prefixWord ++ tailWord_1145598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145598).length < 2 ^ (prefixWord ++ tailWord_1145598).sum := by decide
  have hdescent : baseEnd_1145598 < baseStart_1145598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145614 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1145614 : Nat := 118140960795 + 1145614 * 2 ^ 59
def prefixEnd_1145614 : Nat := 4983230072969 + 3 ^ 40 * 1145614 * 2
def baseEnd_1145614 : Nat := 588250626519986013656423

theorem tailTrace_1145614 : CollatzResearch.WordTrace tailWord_1145614 prefixEnd_1145614 588250626519986013656423 := by
  unfold tailWord_1145614
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222996908955451017424487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27855983514429072092930597 5222996908955451017424487)
  ·
    refine ⟨7834495363433176526136731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5222996908955451017424487 7834495363433176526136731)
    ·
      refine ⟨11751743045149764789205097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7834495363433176526136731 11751743045149764789205097)
      ·
        refine ⟨8813807283862323591903823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11751743045149764789205097 8813807283862323591903823)
        ·
          refine ⟨13220710925793485387855735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8813807283862323591903823 13220710925793485387855735)
          ·
            refine ⟨19831066388690228081783603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13220710925793485387855735 19831066388690228081783603)
            ·
              refine ⟨29746599583035342122675405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19831066388690228081783603 29746599583035342122675405)
              ·
                refine ⟨11154974843638253296003277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29746599583035342122675405 11154974843638253296003277)
                ·
                  refine ⟨4183115566364344986001229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11154974843638253296003277 4183115566364344986001229)
                  ·
                    refine ⟨1568668337386629369750461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4183115566364344986001229 1568668337386629369750461)
                    ·
                      refine ⟨588250626519986013656423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568668337386629369750461 588250626519986013656423)
                      ·
                        rfl

theorem cell23_1145614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1145614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145614 prefixEnd_1145614 := by exact prefixLift 1145614
  have htrace : WordTrace (prefixWord ++ tailWord_1145614) baseStart_1145614 baseEnd_1145614 := by
    simpa [prefixWord, tailWord_1145614, baseEnd_1145614] using wordTrace_append hprefix tailTrace_1145614
  have hstable : (prefixWord ++ tailWord_1145614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145614).length < 2 ^ (prefixWord ++ tailWord_1145614).sum := by decide
  have hdescent : baseEnd_1145614 < baseStart_1145614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145618 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1145618 : Nat := 118140960795 + 1145618 * 2 ^ 59
def prefixEnd_1145618 : Nat := 4983230072969 + 3 ^ 40 * 1145618 * 2
def baseEnd_1145618 : Nat := 588252680442603998006405

theorem tailTrace_1145618 : CollatzResearch.WordTrace tailWord_1145618 prefixEnd_1145618 588252680442603998006405 := by
  unfold tailWord_1145618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446030290907279205635377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27856080775752744548361005 10446030290907279205635377)
  ·
    refine ⟨7834522718180459404226533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10446030290907279205635377 7834522718180459404226533)
    ·
      refine ⟨1468973009658836138292475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7834522718180459404226533 1468973009658836138292475)
      ·
        refine ⟨2203459514488254207438713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468973009658836138292475 2203459514488254207438713)
        ·
          refine ⟨1652594635866190655579035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2203459514488254207438713 1652594635866190655579035)
          ·
            refine ⟨2478891953799285983368553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652594635866190655579035 2478891953799285983368553)
            ·
              refine ⟨1859168965349464487526415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2478891953799285983368553 1859168965349464487526415)
              ·
                refine ⟨2788753448024196731289623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859168965349464487526415 2788753448024196731289623)
                ·
                  refine ⟨4183130172036295096934435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788753448024196731289623 4183130172036295096934435)
                  ·
                    refine ⟨6274695258054442645401653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4183130172036295096934435 6274695258054442645401653)
                    ·
                      refine ⟨588252680442603998006405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6274695258054442645401653 588252680442603998006405)
                      ·
                        rfl

theorem cell23_1145618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1145618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145618 prefixEnd_1145618 := by exact prefixLift 1145618
  have htrace : WordTrace (prefixWord ++ tailWord_1145618) baseStart_1145618 baseEnd_1145618 := by
    simpa [prefixWord, tailWord_1145618, baseEnd_1145618] using wordTrace_append hprefix tailTrace_1145618
  have hstable : (prefixWord ++ tailWord_1145618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145618).length < 2 ^ (prefixWord ++ tailWord_1145618).sum := by decide
  have hdescent : baseEnd_1145618 < baseStart_1145618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145631 : List Nat := [1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 3]
def baseStart_1145631 : Nat := 118140960795 + 1145631 * 2 ^ 59
def prefixEnd_1145631 : Nat := 4983230072969 + 3 ^ 40 * 1145631 * 2
def baseEnd_1145631 : Nat := 588259355691112447143845

theorem tailTrace_1145631 : CollatzResearch.WordTrace tailWord_1145631 prefixEnd_1145631 588259355691112447143845 := by
  unfold tailWord_1145631
  simp only [CollatzResearch.WordTrace]
  refine ⟨41784595312582020042764747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27856396875054680028509831 41784595312582020042764747)
  ·
    refine ⟨62676892968873030064147121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41784595312582020042764747 62676892968873030064147121)
    ·
      refine ⟨47007669726654772548110341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62676892968873030064147121 47007669726654772548110341)
      ·
        refine ⟨8813938073747769852770689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47007669726654772548110341 8813938073747769852770689)
        ·
          refine ⟨6610453555310827389578017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8813938073747769852770689 6610453555310827389578017)
          ·
            refine ⟨4957840166483120542183513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6610453555310827389578017 4957840166483120542183513)
            ·
              refine ⟨3718380124862340406637635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957840166483120542183513 3718380124862340406637635)
              ·
                refine ⟨5577570187293510609956453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718380124862340406637635 5577570187293510609956453)
                ·
                  refine ⟨1045794410117533239366835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5577570187293510609956453 1045794410117533239366835)
                  ·
                    refine ⟨1568691615176299859050253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1045794410117533239366835 1568691615176299859050253)
                    ·
                      refine ⟨588259355691112447143845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568691615176299859050253 588259355691112447143845)
                      ·
                        rfl

theorem cell23_1145631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_1145631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145631 prefixEnd_1145631 := by exact prefixLift 1145631
  have htrace : WordTrace (prefixWord ++ tailWord_1145631) baseStart_1145631 baseEnd_1145631 := by
    simpa [prefixWord, tailWord_1145631, baseEnd_1145631] using wordTrace_append hprefix tailTrace_1145631
  have hstable : (prefixWord ++ tailWord_1145631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145631).length < 2 ^ (prefixWord ++ tailWord_1145631).sum := by decide
  have hdescent : baseEnd_1145631 < baseStart_1145631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145632 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1145632 : Nat := 118140960795 + 1145632 * 2 ^ 59
def prefixEnd_1145632 : Nat := 4983230072969 + 3 ^ 40 * 1145632 * 2
def baseEnd_1145632 : Nat := 588259869171766943231341

theorem tailTrace_1145632 : CollatzResearch.WordTrace tailWord_1145632 prefixEnd_1145632 588259869171766943231341 := by
  unfold tailWord_1145632
  simp only [CollatzResearch.WordTrace]
  refine ⟨20892315892789198606775575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27856421190385598142367433 20892315892789198606775575)
  ·
    refine ⟨31338473839183797910163363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20892315892789198606775575 31338473839183797910163363)
    ·
      refine ⟨47007710758775696865245045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31338473839183797910163363 47007710758775696865245045)
      ·
        refine ⟨4406972883635221581116723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47007710758775696865245045 4406972883635221581116723)
        ·
          refine ⟨6610459325452832371675085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4406972883635221581116723 6610459325452832371675085)
          ·
            refine ⟨2478922247044812139378157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6610459325452832371675085 2478922247044812139378157)
            ·
              refine ⟨929595842641804552266809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2478922247044812139378157 929595842641804552266809)
              ·
                refine ⟨697196881981353414200107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 929595842641804552266809 697196881981353414200107)
                ·
                  refine ⟨1045795322972030121300161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697196881981353414200107 1045795322972030121300161)
                  ·
                    refine ⟨784346492229022590975121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1045795322972030121300161 784346492229022590975121)
                    ·
                      refine ⟨588259869171766943231341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784346492229022590975121 588259869171766943231341)
                      ·
                        rfl

theorem cell23_1145632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1145632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145632 prefixEnd_1145632 := by exact prefixLift 1145632
  have htrace : WordTrace (prefixWord ++ tailWord_1145632) baseStart_1145632 baseEnd_1145632 := by
    simpa [prefixWord, tailWord_1145632, baseEnd_1145632] using wordTrace_append hprefix tailTrace_1145632
  have hstable : (prefixWord ++ tailWord_1145632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145632).length < 2 ^ (prefixWord ++ tailWord_1145632).sum := by decide
  have hdescent : baseEnd_1145632 < baseStart_1145632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145642 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_1145642 : Nat := 118140960795 + 1145642 * 2 ^ 59
def prefixEnd_1145642 : Nat := 4983230072969 + 3 ^ 40 * 1145642 * 2
def baseEnd_1145642 : Nat := 196088334659437301368765

theorem tailTrace_1145642 : CollatzResearch.WordTrace tailWord_1145642 prefixEnd_1145642 196088334659437301368765 := by
  unfold tailWord_1145642
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446249128885542230353795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27856664343694779280943453 10446249128885542230353795)
  ·
    refine ⟨15669373693328313345530693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10446249128885542230353795 15669373693328313345530693)
    ·
      refine ⟨2938007567499058752287005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15669373693328313345530693 2938007567499058752287005)
      ·
        refine ⟨1101752837812147032107627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2938007567499058752287005 1101752837812147032107627)
        ·
          refine ⟨1652629256718220548161441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101752837812147032107627 1652629256718220548161441)
          ·
            refine ⟨1239471942538665411121081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1652629256718220548161441 1239471942538665411121081)
            ·
              refine ⟨929603956903999058340811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239471942538665411121081 929603956903999058340811)
              ·
                refine ⟨1394405935355998587511217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929603956903999058340811 1394405935355998587511217)
                ·
                  refine ⟨1045804451516998940633413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394405935355998587511217 1045804451516998940633413)
                  ·
                    refine ⟨196088334659437301368765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1045804451516998940633413 196088334659437301368765)
                    ·
                      rfl

theorem cell23_1145642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_1145642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145642 prefixEnd_1145642 := by exact prefixLift 1145642
  have htrace : WordTrace (prefixWord ++ tailWord_1145642) baseStart_1145642 baseEnd_1145642 := by
    simpa [prefixWord, tailWord_1145642, baseEnd_1145642] using wordTrace_append hprefix tailTrace_1145642
  have hstable : (prefixWord ++ tailWord_1145642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145642).length < 2 ^ (prefixWord ++ tailWord_1145642).sum := by decide
  have hdescent : baseEnd_1145642 < baseStart_1145642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145652 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1145652 : Nat := 118140960795 + 1145652 * 2 ^ 59
def prefixEnd_1145652 : Nat := 4983230072969 + 3 ^ 40 * 1145652 * 2
def baseEnd_1145652 : Nat := 588270138784856864981249

theorem tailTrace_1145652 : CollatzResearch.WordTrace tailWord_1145652 prefixEnd_1145652 588270138784856864981249 := by
  unfold tailWord_1145652
  simp only [CollatzResearch.WordTrace]
  refine ⟨20892680622752970314639605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27856907497003960419519473 20892680622752970314639605)
  ·
    refine ⟨1958688808383090966997463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20892680622752970314639605 1958688808383090966997463)
    ·
      refine ⟨2938033212574636450496195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1958688808383090966997463 2938033212574636450496195)
      ·
        refine ⟨4407049818861954675744293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938033212574636450496195 4407049818861954675744293)
        ·
          refine ⟨826321841036616501702055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4407049818861954675744293 826321841036616501702055)
          ·
            refine ⟨1239482761554924752553083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826321841036616501702055 1239482761554924752553083)
            ·
              refine ⟨1859224142332387128829625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239482761554924752553083 1859224142332387128829625)
              ·
                refine ⟨1394418106749290346622219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859224142332387128829625 1394418106749290346622219)
                ·
                  refine ⟨2091627160123935519933329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394418106749290346622219 2091627160123935519933329)
                  ·
                    refine ⟨1568720370092951639949997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2091627160123935519933329 1568720370092951639949997)
                    ·
                      refine ⟨588270138784856864981249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568720370092951639949997 588270138784856864981249)
                      ·
                        rfl

theorem cell23_1145652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1145652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145652 prefixEnd_1145652 := by exact prefixLift 1145652
  have htrace : WordTrace (prefixWord ++ tailWord_1145652) baseStart_1145652 baseEnd_1145652 := by
    simpa [prefixWord, tailWord_1145652, baseEnd_1145652] using wordTrace_append hprefix tailTrace_1145652
  have hstable : (prefixWord ++ tailWord_1145652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145652).length < 2 ^ (prefixWord ++ tailWord_1145652).sum := by decide
  have hdescent : baseEnd_1145652 < baseStart_1145652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145658 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2]
def baseStart_1145658 : Nat := 118140960795 + 1145658 * 2 ^ 59
def prefixEnd_1145658 : Nat := 4983230072969 + 3 ^ 40 * 1145658 * 2
def baseEnd_1145658 : Nat := 588273219668783841506221

theorem tailTrace_1145658 : CollatzResearch.WordTrace tailWord_1145658 prefixEnd_1145658 588273219668783841506221 := by
  unfold tailWord_1145658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10446395020871050913499407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27857053388989469102665085 10446395020871050913499407)
  ·
    refine ⟨15669592531306576370249111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10446395020871050913499407 15669592531306576370249111)
    ·
      refine ⟨23504388796959864555373667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15669592531306576370249111 23504388796959864555373667)
      ·
        refine ⟨35256583195439796833060501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23504388796959864555373667 35256583195439796833060501)
        ·
          refine ⟨1652652337286240476549711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35256583195439796833060501 1652652337286240476549711)
          ·
            refine ⟨2478978505929360714824567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1652652337286240476549711 2478978505929360714824567)
            ·
              refine ⟨3718467758894041072236851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478978505929360714824567 3718467758894041072236851)
              ·
                refine ⟨5577701638341061608355277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3718467758894041072236851 5577701638341061608355277)
                ·
                  refine ⟨2091638114377898103133229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5577701638341061608355277 2091638114377898103133229)
                  ·
                    refine ⟨784364292891711788674961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091638114377898103133229 784364292891711788674961)
                    ·
                      refine ⟨588273219668783841506221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784364292891711788674961 588273219668783841506221)
                      ·
                        rfl

theorem cell23_1145658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2].length) (baseStart_1145658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145658 prefixEnd_1145658 := by exact prefixLift 1145658
  have htrace : WordTrace (prefixWord ++ tailWord_1145658) baseStart_1145658 baseEnd_1145658 := by
    simpa [prefixWord, tailWord_1145658, baseEnd_1145658] using wordTrace_append hprefix tailTrace_1145658
  have hstable : (prefixWord ++ tailWord_1145658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145658).length < 2 ^ (prefixWord ++ tailWord_1145658).sum := by decide
  have hdescent : baseEnd_1145658 < baseStart_1145658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145726 : List Nat := [4, 2, 3, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1145726 : Nat := 118140960795 + 1145726 * 2 ^ 59
def prefixEnd_1145726 : Nat := 4983230072969 + 3 ^ 40 * 1145726 * 2
def baseEnd_1145726 : Nat := 588308136353289575455909

theorem tailTrace_1145726 : CollatzResearch.WordTrace tailWord_1145726 prefixEnd_1145726 588308136353289575455909 := by
  unfold tailWord_1145726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5223507530904731408434129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27858706831491900844982021 5223507530904731408434129)
  ·
    refine ⟨3917630648178548556325597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5223507530904731408434129 3917630648178548556325597)
    ·
      refine ⟨1469111493066955708622099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3917630648178548556325597 1469111493066955708622099)
      ·
        refine ⟨2203667239600433562933149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469111493066955708622099 2203667239600433562933149)
        ·
          refine ⟨826375214850162586099931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2203667239600433562933149 826375214850162586099931)
          ·
            refine ⟨1239562822275243879149897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826375214850162586099931 1239562822275243879149897)
            ·
              refine ⟨929672116706432909362423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1239562822275243879149897 929672116706432909362423)
              ·
                refine ⟨1394508175059649364043635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929672116706432909362423 1394508175059649364043635)
                ·
                  refine ⟨2091762262589474046065453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394508175059649364043635 2091762262589474046065453)
                  ·
                    refine ⟨784410848471052767274545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091762262589474046065453 784410848471052767274545)
                    ·
                      refine ⟨588308136353289575455909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784410848471052767274545 588308136353289575455909)
                      ·
                        rfl

theorem cell23_1145726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1145726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145726 prefixEnd_1145726 := by exact prefixLift 1145726
  have htrace : WordTrace (prefixWord ++ tailWord_1145726) baseStart_1145726 baseEnd_1145726 := by
    simpa [prefixWord, tailWord_1145726, baseEnd_1145726] using wordTrace_append hprefix tailTrace_1145726
  have hstable : (prefixWord ++ tailWord_1145726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145726).length < 2 ^ (prefixWord ++ tailWord_1145726).sum := by decide
  have hdescent : baseEnd_1145726 < baseStart_1145726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145761 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1145761 : Nat := 118140960795 + 1145761 * 2 ^ 59
def prefixEnd_1145761 : Nat := 4983230072969 + 3 ^ 40 * 1145761 * 2
def baseEnd_1145761 : Nat := 588326108176196938518247

theorem tailTrace_1145761 : CollatzResearch.WordTrace tailWord_1145761 prefixEnd_1145761 588326108176196938518247 := by
  unfold tailWord_1145761
  simp only [CollatzResearch.WordTrace]
  refine ⟨41789336802111052244997137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27859557868074034829998091 41789336802111052244997137)
  ·
    refine ⟨31342002601583289183747853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41789336802111052244997137 31342002601583289183747853)
    ·
      refine ⟨11753250975593733443905445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31342002601583289183747853 11753250975593733443905445)
      ·
        refine ⟨2203734557923825020732271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11753250975593733443905445 2203734557923825020732271)
        ·
          refine ⟨3305601836885737531098407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203734557923825020732271 3305601836885737531098407)
          ·
            refine ⟨4958402755328606296647611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305601836885737531098407 4958402755328606296647611)
            ·
              refine ⟨7437604132992909444971417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4958402755328606296647611 7437604132992909444971417)
              ·
                refine ⟨5578203099744682083728563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7437604132992909444971417 5578203099744682083728563)
                ·
                  refine ⟨8367304649617023125592845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578203099744682083728563 8367304649617023125592845)
                  ·
                    refine ⟨3137739243606383672097317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8367304649617023125592845 3137739243606383672097317)
                    ·
                      refine ⟨588326108176196938518247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3137739243606383672097317 588326108176196938518247)
                      ·
                        rfl

theorem cell23_1145761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1145761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145761 prefixEnd_1145761 := by exact prefixLift 1145761
  have htrace : WordTrace (prefixWord ++ tailWord_1145761) baseStart_1145761 baseEnd_1145761 := by
    simpa [prefixWord, tailWord_1145761, baseEnd_1145761] using wordTrace_append hprefix tailTrace_1145761
  have hstable : (prefixWord ++ tailWord_1145761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145761).length < 2 ^ (prefixWord ++ tailWord_1145761).sum := by decide
  have hdescent : baseEnd_1145761 < baseStart_1145761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145781 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_1145781 : Nat := 118140960795 + 1145781 * 2 ^ 59
def prefixEnd_1145781 : Nat := 4983230072969 + 3 ^ 40 * 1145781 * 2
def baseEnd_1145781 : Nat := 588336377789286860268155

theorem tailTrace_1145781 : CollatzResearch.WordTrace tailWord_1145781 prefixEnd_1145781 588336377789286860268155 := by
  unfold tailWord_1145781
  simp only [CollatzResearch.WordTrace]
  refine ⟨41790066262038595660725197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27860044174692397107150131 41790066262038595660725197)
  ·
    refine ⟨15671274848264473372771949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41790066262038595660725197 15671274848264473372771949)
    ·
      refine ⟨5876728068099177514789481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15671274848264473372771949 5876728068099177514789481)
      ·
        refine ⟨4407546051074383136092111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5876728068099177514789481 4407546051074383136092111)
        ·
          refine ⟨6611319076611574704138167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407546051074383136092111 6611319076611574704138167)
          ·
            refine ⟨9916978614917362056207251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611319076611574704138167 9916978614917362056207251)
            ·
              refine ⟨14875467922376043084310877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9916978614917362056207251 14875467922376043084310877)
              ·
                refine ⟨5578300470891016156616579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14875467922376043084310877 5578300470891016156616579)
                ·
                  refine ⟨8367450706336524234924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5578300470891016156616579 8367450706336524234924869)
                  ·
                    refine ⟨1568897007438098294048413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8367450706336524234924869 1568897007438098294048413)
                    ·
                      refine ⟨588336377789286860268155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1568897007438098294048413 588336377789286860268155)
                      ·
                        rfl

theorem cell23_1145781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_1145781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145781 prefixEnd_1145781 := by exact prefixLift 1145781
  have htrace : WordTrace (prefixWord ++ tailWord_1145781) baseStart_1145781 baseEnd_1145781 := by
    simpa [prefixWord, tailWord_1145781, baseEnd_1145781] using wordTrace_append hprefix tailTrace_1145781
  have hstable : (prefixWord ++ tailWord_1145781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145781).length < 2 ^ (prefixWord ++ tailWord_1145781).sum := by decide
  have hdescent : baseEnd_1145781 < baseStart_1145781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145784 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 8]
def baseStart_1145784 : Nat := 118140960795 + 1145784 * 2 ^ 59
def prefixEnd_1145784 : Nat := 4983230072969 + 3 ^ 40 * 1145784 * 2
def baseEnd_1145784 : Nat := 65370879803472260947849

theorem tailTrace_1145784 : CollatzResearch.WordTrace tailWord_1145784 prefixEnd_1145784 65370879803472260947849 := by
  unfold tailWord_1145784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20895087840513863586542203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27860117120685151448722937 20895087840513863586542203)
  ·
    refine ⟨31342631760770795379813305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20895087840513863586542203 31342631760770795379813305)
    ·
      refine ⟨23506973820578096534859979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31342631760770795379813305 23506973820578096534859979)
      ·
        refine ⟨35260460730867144802289969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23506973820578096534859979 35260460730867144802289969)
        ·
          refine ⟨26445345548150358601717477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35260460730867144802289969 26445345548150358601717477)
          ·
            refine ⟨4958502290278192237822027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26445345548150358601717477 4958502290278192237822027)
            ·
              refine ⟨7437753435417288356733041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4958502290278192237822027 7437753435417288356733041)
              ·
                refine ⟨5578315076562966267549781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7437753435417288356733041 5578315076562966267549781)
                ·
                  refine ⟨65370879803472260947849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5578315076562966267549781 65370879803472260947849)
                  ·
                    rfl

theorem cell23_1145784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 8].length) (baseStart_1145784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145784 prefixEnd_1145784 := by exact prefixLift 1145784
  have htrace : WordTrace (prefixWord ++ tailWord_1145784) baseStart_1145784 baseEnd_1145784 := by
    simpa [prefixWord, tailWord_1145784, baseEnd_1145784] using wordTrace_append hprefix tailTrace_1145784
  have hstable : (prefixWord ++ tailWord_1145784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145784).length < 2 ^ (prefixWord ++ tailWord_1145784).sum := by decide
  have hdescent : baseEnd_1145784 < baseStart_1145784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145818 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 6]
def baseStart_1145818 : Nat := 118140960795 + 1145818 * 2 ^ 59
def prefixEnd_1145818 : Nat := 4983230072969 + 3 ^ 40 * 1145818 * 2
def baseEnd_1145818 : Nat := 65372819619278135056165

theorem tailTrace_1145818 : CollatzResearch.WordTrace tailWord_1145818 prefixEnd_1145818 65372819619278135056165 := by
  unfold tailWord_1145818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10447853940726137744955527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27860943841936367319881405 10447853940726137744955527)
  ·
    refine ⟨15671780911089206617433291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10447853940726137744955527 15671780911089206617433291)
    ·
      refine ⟨23507671366633809926149937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15671780911089206617433291 23507671366633809926149937)
      ·
        refine ⟨17630753524975357444612453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23507671366633809926149937 17630753524975357444612453)
        ·
          refine ⟨3305766285932879520864835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17630753524975357444612453 3305766285932879520864835)
          ·
            refine ⟨4958649428899319281297253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305766285932879520864835 4958649428899319281297253)
            ·
              refine ⟨929746767918622365243235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4958649428899319281297253 929746767918622365243235)
              ·
                refine ⟨1394620151877933547864853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929746767918622365243235 1394620151877933547864853)
                ·
                  refine ⟨65372819619278135056165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1394620151877933547864853 65372819619278135056165)
                  ·
                    rfl

theorem cell23_1145818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 6].length) (baseStart_1145818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145818 prefixEnd_1145818 := by exact prefixLift 1145818
  have htrace : WordTrace (prefixWord ++ tailWord_1145818) baseStart_1145818 baseEnd_1145818 := by
    simpa [prefixWord, tailWord_1145818, baseEnd_1145818] using wordTrace_append hprefix tailTrace_1145818
  have hstable : (prefixWord ++ tailWord_1145818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145818).length < 2 ^ (prefixWord ++ tailWord_1145818).sum := by decide
  have hdescent : baseEnd_1145818 < baseStart_1145818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145881 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 4]
def baseStart_1145881 : Nat := 118140960795 + 1145881 * 2 ^ 59
def prefixEnd_1145881 : Nat := 4983230072969 + 3 ^ 40 * 1145881 * 2
def baseEnd_1145881 : Nat := 588387725854736469017695

theorem tailTrace_1145881 : CollatzResearch.WordTrace tailWord_1145881 prefixEnd_1145881 588387725854736469017695 := by
  unfold tailWord_1145881
  simp only [CollatzResearch.WordTrace]
  refine ⟨41793713561676312739365497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27862475707784208492910331 41793713561676312739365497)
  ·
    refine ⟨31345285171257234554524123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41793713561676312739365497 31345285171257234554524123)
    ·
      refine ⟨47017927756885851831786185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31345285171257234554524123 47017927756885851831786185)
      ·
        refine ⟨35263445817664388873839639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47017927756885851831786185 35263445817664388873839639)
        ·
          refine ⟨52895168726496583310759459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35263445817664388873839639 52895168726496583310759459)
          ·
            refine ⟨79342753089744874966139189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52895168726496583310759459 79342753089744874966139189)
            ·
              refine ⟨7438383102163582028075549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79342753089744874966139189 7438383102163582028075549)
              ·
                refine ⟨2789393663311343260528331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7438383102163582028075549 2789393663311343260528331)
                ·
                  refine ⟨4184090494967014890792497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789393663311343260528331 4184090494967014890792497)
                  ·
                    refine ⟨3138067871225261168094373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4184090494967014890792497 3138067871225261168094373)
                    ·
                      refine ⟨588387725854736469017695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3138067871225261168094373 588387725854736469017695)
                      ·
                        rfl

theorem cell23_1145881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_1145881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145881 prefixEnd_1145881 := by exact prefixLift 1145881
  have htrace : WordTrace (prefixWord ++ tailWord_1145881) baseStart_1145881 baseEnd_1145881 := by
    simpa [prefixWord, tailWord_1145881, baseEnd_1145881] using wordTrace_append hprefix tailTrace_1145881
  have hstable : (prefixWord ++ tailWord_1145881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145881).length < 2 ^ (prefixWord ++ tailWord_1145881).sum := by decide
  have hdescent : baseEnd_1145881 < baseStart_1145881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145908 : List Nat := [2, 5, 1, 2, 1, 2, 10]
def baseStart_1145908 : Nat := 118140960795 + 1145908 * 2 ^ 59
def prefixEnd_1145908 : Nat := 4983230072969 + 3 ^ 40 * 1145908 * 2
def baseEnd_1145908 : Nat := 7264217158424788436791

theorem tailTrace_1145908 : CollatzResearch.WordTrace tailWord_1145908 prefixEnd_1145908 7264217158424788436791 := by
  unfold tailWord_1145908
  simp only [CollatzResearch.WordTrace]
  refine ⟨20897349166289248175299189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27863132221718997567065585 20897349166289248175299189)
  ·
    refine ⟨1959126484339617016434299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20897349166289248175299189 1959126484339617016434299)
    ·
      refine ⟨2938689726509425524651449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1959126484339617016434299 2938689726509425524651449)
      ·
        refine ⟨2204017294882069143488587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2938689726509425524651449 2204017294882069143488587)
        ·
          refine ⟨3306025942323103715232881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204017294882069143488587 3306025942323103715232881)
          ·
            refine ⟨2479519456742327786424661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306025942323103715232881 2479519456742327786424661)
            ·
              refine ⟨7264217158424788436791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2479519456742327786424661 7264217158424788436791)
              ·
                rfl

theorem cell23_1145908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 10].length) (baseStart_1145908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145908 prefixEnd_1145908 := by exact prefixLift 1145908
  have htrace : WordTrace (prefixWord ++ tailWord_1145908) baseStart_1145908 baseEnd_1145908 := by
    simpa [prefixWord, tailWord_1145908, baseEnd_1145908] using wordTrace_append hprefix tailTrace_1145908
  have hstable : (prefixWord ++ tailWord_1145908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145908).length < 2 ^ (prefixWord ++ tailWord_1145908).sum := by decide
  have hdescent : baseEnd_1145908 < baseStart_1145908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145961 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 5]
def baseStart_1145961 : Nat := 118140960795 + 1145961 * 2 ^ 59
def prefixEnd_1145961 : Nat := 4983230072969 + 3 ^ 40 * 1145961 * 2
def baseEnd_1145961 : Nat := 588428804307096156017327

theorem tailTrace_1145961 : CollatzResearch.WordTrace tailWord_1145961 prefixEnd_1145961 588428804307096156017327 := by
  unfold tailWord_1145961
  simp only [CollatzResearch.WordTrace]
  refine ⟨41796631401386486402277737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27864420934257657601518491 41796631401386486402277737)
  ·
    refine ⟨31347473551039864801708303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41796631401386486402277737 31347473551039864801708303)
    ·
      refine ⟨47021210326559797202562455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31347473551039864801708303 47021210326559797202562455)
      ·
        refine ⟨70531815489839695803843683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47021210326559797202562455 70531815489839695803843683)
        ·
          refine ⟨105797723234759543705765525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70531815489839695803843683 105797723234759543705765525)
          ·
            refine ⟨4959268276629353611207759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105797723234759543705765525 4959268276629353611207759)
            ·
              refine ⟨7438902414944030416811639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4959268276629353611207759 7438902414944030416811639)
              ·
                refine ⟨11158353622416045625217459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7438902414944030416811639 11158353622416045625217459)
                ·
                  refine ⟨16737530433624068437826189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11158353622416045625217459 16737530433624068437826189)
                  ·
                    refine ⟨6276573912609025664184821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16737530433624068437826189 6276573912609025664184821)
                    ·
                      refine ⟨588428804307096156017327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6276573912609025664184821 588428804307096156017327)
                      ·
                        rfl

theorem cell23_1145961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_1145961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145961 prefixEnd_1145961 := by exact prefixLift 1145961
  have htrace : WordTrace (prefixWord ++ tailWord_1145961) baseStart_1145961 baseEnd_1145961 := by
    simpa [prefixWord, tailWord_1145961, baseEnd_1145961] using wordTrace_append hprefix tailTrace_1145961
  have hstable : (prefixWord ++ tailWord_1145961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145961).length < 2 ^ (prefixWord ++ tailWord_1145961).sum := by decide
  have hdescent : baseEnd_1145961 < baseStart_1145961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145962 : List Nat := [3, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1145962 : Nat := 118140960795 + 1145962 * 2 ^ 59
def prefixEnd_1145962 : Nat := 4983230072969 + 3 ^ 40 * 1145962 * 2
def baseEnd_1145962 : Nat := 588429317787750652104823

theorem tailTrace_1145962 : CollatzResearch.WordTrace tailWord_1145962 prefixEnd_1145962 588429317787750652104823 := by
  unfold tailWord_1145962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449166968595715893266035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27864445249588575715376093 10449166968595715893266035)
  ·
    refine ⟨15673750452893573839899053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449166968595715893266035 15673750452893573839899053)
    ·
      refine ⟨5877656419835090189962145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15673750452893573839899053 5877656419835090189962145)
      ·
        refine ⟨4408242314876317642471609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5877656419835090189962145 4408242314876317642471609)
        ·
          refine ⟨3306181736157238231853707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4408242314876317642471609 3306181736157238231853707)
          ·
            refine ⟨4959272604235857347780561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3306181736157238231853707 4959272604235857347780561)
            ·
              refine ⟨3719454453176893010835421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959272604235857347780561 3719454453176893010835421)
              ·
                refine ⟨1394795419941334879063283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3719454453176893010835421 1394795419941334879063283)
                ·
                  refine ⟨2092193129912002318594925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394795419941334879063283 2092193129912002318594925)
                  ·
                    refine ⟨784572423717000869473097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2092193129912002318594925 784572423717000869473097)
                    ·
                      refine ⟨588429317787750652104823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784572423717000869473097 588429317787750652104823)
                      ·
                        rfl

theorem cell23_1145962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1145962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145962 prefixEnd_1145962 := by exact prefixLift 1145962
  have htrace : WordTrace (prefixWord ++ tailWord_1145962) baseStart_1145962 baseEnd_1145962 := by
    simpa [prefixWord, tailWord_1145962, baseEnd_1145962] using wordTrace_append hprefix tailTrace_1145962
  have hstable : (prefixWord ++ tailWord_1145962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145962).length < 2 ^ (prefixWord ++ tailWord_1145962).sum := by decide
  have hdescent : baseEnd_1145962 < baseStart_1145962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1145975 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_1145975 : Nat := 118140960795 + 1145975 * 2 ^ 59
def prefixEnd_1145975 : Nat := 4983230072969 + 3 ^ 40 * 1145975 * 2
def baseEnd_1145975 : Nat := 588435993036259101242263

theorem tailTrace_1145975 : CollatzResearch.WordTrace tailWord_1145975 prefixEnd_1145975 588435993036259101242263 := by
  unfold tailWord_1145975
  simp only [CollatzResearch.WordTrace]
  refine ⟨41797142023335766793287379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27864761348890511195524919 41797142023335766793287379)
  ·
    refine ⟨62695713035003650189931069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41797142023335766793287379 62695713035003650189931069)
    ·
      refine ⟨23510892388126368821224151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62695713035003650189931069 23510892388126368821224151)
      ·
        refine ⟨35266338582189553231836227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23510892388126368821224151 35266338582189553231836227)
        ·
          refine ⟨52899507873284329847754341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35266338582189553231836227 52899507873284329847754341)
          ·
            refine ⟨9918657726240811846453939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52899507873284329847754341 9918657726240811846453939)
            ·
              refine ⟨14877986589361217769680909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9918657726240811846453939 14877986589361217769680909)
              ·
                refine ⟨5579244971010456663630341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14877986589361217769680909 5579244971010456663630341)
                ·
                  refine ⟨1046108432064460624430689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5579244971010456663630341 1046108432064460624430689)
                  ·
                    refine ⟨784581324048345468323017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046108432064460624430689 784581324048345468323017)
                    ·
                      refine ⟨588435993036259101242263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784581324048345468323017 588435993036259101242263)
                      ·
                        rfl

theorem cell23_1145975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_1145975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1145975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1145975 prefixEnd_1145975 := by exact prefixLift 1145975
  have htrace : WordTrace (prefixWord ++ tailWord_1145975) baseStart_1145975 baseEnd_1145975 := by
    simpa [prefixWord, tailWord_1145975, baseEnd_1145975] using wordTrace_append hprefix tailTrace_1145975
  have hstable : (prefixWord ++ tailWord_1145975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1145975).length < 2 ^ (prefixWord ++ tailWord_1145975).sum := by decide
  have hdescent : baseEnd_1145975 < baseStart_1145975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1145975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146026 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1146026 : Nat := 118140960795 + 1146026 * 2 ^ 59
def prefixEnd_1146026 : Nat := 4983230072969 + 3 ^ 40 * 1146026 * 2
def baseEnd_1146026 : Nat := 588462180549638401704529

theorem tailTrace_1146026 : CollatzResearch.WordTrace tailWord_1146026 prefixEnd_1146026 588462180549638401704529 := by
  unfold tailWord_1146026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10449750536537750625848483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27866001430767335002262621 10449750536537750625848483)
  ·
    refine ⟨15674625804806625938772725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10449750536537750625848483 15674625804806625938772725)
    ·
      refine ⟨1469496169200621181759943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15674625804806625938772725 1469496169200621181759943)
      ·
        refine ⟨2204244253800931772639915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1469496169200621181759943 2204244253800931772639915)
        ·
          refine ⟨3306366380701397658959873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2204244253800931772639915 3306366380701397658959873)
          ·
            refine ⟨2479774785526048244219905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3306366380701397658959873 2479774785526048244219905)
            ·
              refine ⟨1859831089144536183164929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479774785526048244219905 1859831089144536183164929)
              ·
                refine ⟨1394873316858402137373697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859831089144536183164929 1394873316858402137373697)
                ·
                  refine ⟨1046154987643801603030273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1394873316858402137373697 1046154987643801603030273)
                  ·
                    refine ⟨784616240732851202272705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046154987643801603030273 784616240732851202272705)
                    ·
                      refine ⟨588462180549638401704529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784616240732851202272705 588462180549638401704529)
                      ·
                        rfl

theorem cell23_1146026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1146026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146026 prefixEnd_1146026 := by exact prefixLift 1146026
  have htrace : WordTrace (prefixWord ++ tailWord_1146026) baseStart_1146026 baseEnd_1146026 := by
    simpa [prefixWord, tailWord_1146026, baseEnd_1146026] using wordTrace_append hprefix tailTrace_1146026
  have hstable : (prefixWord ++ tailWord_1146026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146026).length < 2 ^ (prefixWord ++ tailWord_1146026).sum := by decide
  have hdescent : baseEnd_1146026 < baseStart_1146026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146062 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_1146062 : Nat := 118140960795 + 1146062 * 2 ^ 59
def prefixEnd_1146062 : Nat := 4983230072969 + 3 ^ 40 * 1146062 * 2
def baseEnd_1146062 : Nat := 196160221951066753618121

theorem tailTrace_1146062 : CollatzResearch.WordTrace tailWord_1146062 prefixEnd_1146062 196160221951066753618121 := by
  unfold tailWord_1146062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5225039396752572581463055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27866876782680387101136293 5225039396752572581463055)
  ·
    refine ⟨7837559095128858872194583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5225039396752572581463055 7837559095128858872194583)
    ·
      refine ⟨11756338642693288308291875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7837559095128858872194583 11756338642693288308291875)
      ·
        refine ⟨17634507964039932462437813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11756338642693288308291875 17634507964039932462437813)
        ·
          refine ⟨1653235121628743668353545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17634507964039932462437813 1653235121628743668353545)
          ·
            refine ⟨1239926341221557751265159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653235121628743668353545 1239926341221557751265159)
            ·
              refine ⟨1859889511832336626897739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1239926341221557751265159 1859889511832336626897739)
              ·
                refine ⟨2789834267748504940346609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859889511832336626897739 2789834267748504940346609)
                ·
                  refine ⟨2092375700811378705259957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2789834267748504940346609 2092375700811378705259957)
                  ·
                    refine ⟨196160221951066753618121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2092375700811378705259957 196160221951066753618121)
                    ·
                      rfl

theorem cell23_1146062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_1146062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146062 prefixEnd_1146062 := by exact prefixLift 1146062
  have htrace : WordTrace (prefixWord ++ tailWord_1146062) baseStart_1146062 baseEnd_1146062 := by
    simpa [prefixWord, tailWord_1146062, baseEnd_1146062] using wordTrace_append hprefix tailTrace_1146062
  have hstable : (prefixWord ++ tailWord_1146062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146062).length < 2 ^ (prefixWord ++ tailWord_1146062).sum := by decide
  have hdescent : baseEnd_1146062 < baseStart_1146062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146088 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 8]
def baseStart_1146088 : Nat := 118140960795 + 1146088 * 2 ^ 59
def prefixEnd_1146088 : Nat := 4983230072969 + 3 ^ 40 * 1146088 * 2
def baseEnd_1146088 : Nat := 65388224038913017681027

theorem tailTrace_1146088 : CollatzResearch.WordTrace tailWord_1146088 prefixEnd_1146088 65388224038913017681027 := by
  unfold tailWord_1146088
  simp only [CollatzResearch.WordTrace]
  refine ⟨20900631735963193546075459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27867508981284258061433945 20900631735963193546075459)
  ·
    refine ⟨31350947603944790319113189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20900631735963193546075459 31350947603944790319113189)
    ·
      refine ⟨5878302675739648184833723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31350947603944790319113189 5878302675739648184833723)
      ·
        refine ⟨8817454013609472277250585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5878302675739648184833723 8817454013609472277250585)
        ·
          refine ⟨6613090510207104207937939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8817454013609472277250585 6613090510207104207937939)
          ·
            refine ⟨9919635765310656311906909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613090510207104207937939 9919635765310656311906909)
            ·
              refine ⟨3719863411991496116965091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9919635765310656311906909 3719863411991496116965091)
              ·
                refine ⟨5579795117987244175447637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3719863411991496116965091 5579795117987244175447637)
                ·
                  refine ⟨65388224038913017681027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5579795117987244175447637 65388224038913017681027)
                  ·
                    rfl

theorem cell23_1146088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 8].length) (baseStart_1146088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146088 prefixEnd_1146088 := by exact prefixLift 1146088
  have htrace : WordTrace (prefixWord ++ tailWord_1146088) baseStart_1146088 baseEnd_1146088 := by
    simpa [prefixWord, tailWord_1146088, baseEnd_1146088] using wordTrace_append hprefix tailTrace_1146088
  have hstable : (prefixWord ++ tailWord_1146088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146088).length < 2 ^ (prefixWord ++ tailWord_1146088).sum := by decide
  have hdescent : baseEnd_1146088 < baseStart_1146088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146092 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_1146092 : Nat := 118140960795 + 1146092 * 2 ^ 59
def prefixEnd_1146092 : Nat := 4983230072969 + 3 ^ 40 * 1146092 * 2
def baseEnd_1146092 : Nat := 196165356757611714493075

theorem tailTrace_1146092 : CollatzResearch.WordTrace tailWord_1146092 prefixEnd_1146092 196165356757611714493075 := by
  unfold tailWord_1146092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20900704681955947887648265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27867606242607930516864353 20900704681955947887648265)
  ·
    refine ⟨15675528511466960915736199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20900704681955947887648265 15675528511466960915736199)
    ·
      refine ⟨23513292767200441373604299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15675528511466960915736199 23513292767200441373604299)
      ·
        refine ⟨35269939150800662060406449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23513292767200441373604299 35269939150800662060406449)
        ·
          refine ⟨26452454363100496545304837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35269939150800662060406449 26452454363100496545304837)
          ·
            refine ⟨4959835193081343102244657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26452454363100496545304837 4959835193081343102244657)
            ·
              refine ⟨3719876394811007326683493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4959835193081343102244657 3719876394811007326683493)
              ·
                refine ⟨697476824027063873753155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3719876394811007326683493 697476824027063873753155)
                ·
                  refine ⟨1046215236040595810629733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697476824027063873753155 1046215236040595810629733)
                  ·
                    refine ⟨196165356757611714493075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046215236040595810629733 196165356757611714493075)
                    ·
                      rfl

theorem cell23_1146092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_1146092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146092 prefixEnd_1146092 := by exact prefixLift 1146092
  have htrace : WordTrace (prefixWord ++ tailWord_1146092) baseStart_1146092 baseEnd_1146092 := by
    simpa [prefixWord, tailWord_1146092, baseEnd_1146092] using wordTrace_append hprefix tailTrace_1146092
  have hstable : (prefixWord ++ tailWord_1146092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146092).length < 2 ^ (prefixWord ++ tailWord_1146092).sum := by decide
  have hdescent : baseEnd_1146092 < baseStart_1146092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146105 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 6]
def baseStart_1146105 : Nat := 118140960795 + 1146105 * 2 ^ 59
def prefixEnd_1146105 : Nat := 4983230072969 + 3 ^ 40 * 1146105 * 2
def baseEnd_1146105 : Nat := 65389193946815954735185

theorem tailTrace_1146105 : CollatzResearch.WordTrace tailWord_1146105 prefixEnd_1146105 65389193946815954735185 := by
  unfold tailWord_1146105
  simp only [CollatzResearch.WordTrace]
  refine ⟨41801883512864798995519769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27867922341909865997013179 41801883512864798995519769)
  ·
    refine ⟨31351412634648599246639827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41801883512864798995519769 31351412634648599246639827)
    ·
      refine ⟨47027118951972898869959741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31351412634648599246639827 47027118951972898869959741)
      ·
        refine ⟨17635169606989837076234903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47027118951972898869959741 17635169606989837076234903)
        ·
          refine ⟨26452754410484755614352355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17635169606989837076234903 26452754410484755614352355)
          ·
            refine ⟨39679131615727133421528533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26452754410484755614352355 39679131615727133421528533)
            ·
              refine ⟨929979647243604689567075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39679131615727133421528533 929979647243604689567075)
              ·
                refine ⟨1394969470865407034350613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929979647243604689567075 1394969470865407034350613)
                ·
                  refine ⟨65389193946815954735185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1394969470865407034350613 65389193946815954735185)
                  ·
                    rfl

theorem cell23_1146105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 6].length) (baseStart_1146105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146105 prefixEnd_1146105 := by exact prefixLift 1146105
  have htrace : WordTrace (prefixWord ++ tailWord_1146105) baseStart_1146105 baseEnd_1146105 := by
    simpa [prefixWord, tailWord_1146105, baseEnd_1146105] using wordTrace_append hprefix tailTrace_1146105
  have hstable : (prefixWord ++ tailWord_1146105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146105).length < 2 ^ (prefixWord ++ tailWord_1146105).sum := by decide
  have hdescent : baseEnd_1146105 < baseStart_1146105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146135 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 1, 5]
def baseStart_1146135 : Nat := 118140960795 + 1146135 * 2 ^ 59
def prefixEnd_1146135 : Nat := 4983230072969 + 3 ^ 40 * 1146135 * 2
def baseEnd_1146135 : Nat := 196172716646992825080509

theorem tailTrace_1146135 : CollatzResearch.WordTrace tailWord_1146135 prefixEnd_1146135 196172716646992825080509 := by
  unfold tailWord_1146135
  simp only [CollatzResearch.WordTrace]
  refine ⟨41802977702756114119111859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27868651801837409412741239 41802977702756114119111859)
  ·
    refine ⟨62704466554134171178667789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41802977702756114119111859 62704466554134171178667789)
    ·
      refine ⟨23514174957800314192000421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62704466554134171178667789 23514174957800314192000421)
      ·
        refine ⟨4408907804587558911000079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23514174957800314192000421 4408907804587558911000079)
        ·
          refine ⟨6613361706881338366500119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4408907804587558911000079 6613361706881338366500119)
          ·
            refine ⟨9920042560322007549750179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6613361706881338366500119 9920042560322007549750179)
            ·
              refine ⟨14880063840483011324625269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9920042560322007549750179 14880063840483011324625269)
              ·
                refine ⟨1395005985045282311683619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14880063840483011324625269 1395005985045282311683619)
                ·
                  refine ⟨2092508977567923467525429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395005985045282311683619 2092508977567923467525429)
                  ·
                    refine ⟨196172716646992825080509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2092508977567923467525429 196172716646992825080509)
                    ·
                      rfl

theorem cell23_1146135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_1146135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146135 prefixEnd_1146135 := by exact prefixLift 1146135
  have htrace : WordTrace (prefixWord ++ tailWord_1146135) baseStart_1146135 baseEnd_1146135 := by
    simpa [prefixWord, tailWord_1146135, baseEnd_1146135] using wordTrace_append hprefix tailTrace_1146135
  have hstable : (prefixWord ++ tailWord_1146135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146135).length < 2 ^ (prefixWord ++ tailWord_1146135).sum := by decide
  have hdescent : baseEnd_1146135 < baseStart_1146135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146149 : List Nat := [1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_1146149 : Nat := 118140960795 + 1146149 * 2 ^ 59
def prefixEnd_1146149 : Nat := 4983230072969 + 3 ^ 40 * 1146149 * 2
def baseEnd_1146149 : Nat := 588525338670141420466463

theorem tailTrace_1146149 : CollatzResearch.WordTrace tailWord_1146149 prefixEnd_1146149 588525338670141420466463 := by
  unfold tailWord_1146149
  simp only [CollatzResearch.WordTrace]
  refine ⟨41803488324705394510121501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27868992216470263006747667 41803488324705394510121501)
  ·
    refine ⟨15676308121764522941295563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41803488324705394510121501 15676308121764522941295563)
    ·
      refine ⟨23514462182646784411943345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15676308121764522941295563 23514462182646784411943345)
      ·
        refine ⟨17635846636985088308957509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23514462182646784411943345 17635846636985088308957509)
        ·
          refine ⟨3306721244434704057929533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17635846636985088308957509 3306721244434704057929533)
          ·
            refine ⟨1240020466663014021723575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3306721244434704057929533 1240020466663014021723575)
            ·
              refine ⟨1860030699994521032585363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240020466663014021723575 1860030699994521032585363)
              ·
                refine ⟨2790046049991781548878045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860030699994521032585363 2790046049991781548878045)
                ·
                  refine ⟨1046267268746918080829267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2790046049991781548878045 1046267268746918080829267)
                  ·
                    refine ⟨1569400903120377121243901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1046267268746918080829267 1569400903120377121243901)
                    ·
                      refine ⟨588525338670141420466463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1569400903120377121243901 588525338670141420466463)
                      ·
                        rfl

theorem cell23_1146149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_1146149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146149 prefixEnd_1146149 := by exact prefixLift 1146149
  have htrace : WordTrace (prefixWord ++ tailWord_1146149) baseStart_1146149 baseEnd_1146149 := by
    simpa [prefixWord, tailWord_1146149, baseEnd_1146149] using wordTrace_append hprefix tailTrace_1146149
  have hstable : (prefixWord ++ tailWord_1146149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146149).length < 2 ^ (prefixWord ++ tailWord_1146149).sum := by decide
  have hdescent : baseEnd_1146149 < baseStart_1146149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146169 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_1146169 : Nat := 118140960795 + 1146169 * 2 ^ 59
def prefixEnd_1146169 : Nat := 4983230072969 + 3 ^ 40 * 1146169 * 2
def baseEnd_1146169 : Nat := 196178536094410447405457

theorem tailTrace_1146169 : CollatzResearch.WordTrace tailWord_1146169 prefixEnd_1146169 196178536094410447405457 := by
  unfold tailWord_1146169
  simp only [CollatzResearch.WordTrace]
  refine ⟨41804217784632937925849561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27869478523088625283899707 41804217784632937925849561)
  ·
    refine ⟨31353163338474703444387171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41804217784632937925849561 31353163338474703444387171)
    ·
      refine ⟨47029745007712055166580757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31353163338474703444387171 47029745007712055166580757)
      ·
        refine ⟨2204519297236502585933473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 47029745007712055166580757 2204519297236502585933473)
        ·
          refine ⟨1653389472927376939450105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2204519297236502585933473 1653389472927376939450105)
          ·
            refine ⟨1240042104695532704587579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1653389472927376939450105 1240042104695532704587579)
            ·
              refine ⟨1860063157043299056881369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240042104695532704587579 1860063157043299056881369)
              ·
                refine ⟨1395047367782474292661027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860063157043299056881369 1395047367782474292661027)
                ·
                  refine ⟨2092571051673711438991541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395047367782474292661027 2092571051673711438991541)
                  ·
                    refine ⟨196178536094410447405457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2092571051673711438991541 196178536094410447405457)
                    ·
                      rfl

theorem cell23_1146169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_1146169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146169 prefixEnd_1146169 := by exact prefixLift 1146169
  have htrace : WordTrace (prefixWord ++ tailWord_1146169) baseStart_1146169 baseEnd_1146169 := by
    simpa [prefixWord, tailWord_1146169, baseEnd_1146169] using wordTrace_append hprefix tailTrace_1146169
  have hstable : (prefixWord ++ tailWord_1146169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146169).length < 2 ^ (prefixWord ++ tailWord_1146169).sum := by decide
  have hdescent : baseEnd_1146169 < baseStart_1146169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146172 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_1146172 : Nat := 118140960795 + 1146172 * 2 ^ 59
def prefixEnd_1146172 : Nat := 4983230072969 + 3 ^ 40 * 1146172 * 2
def baseEnd_1146172 : Nat := 588537148725194830478857

theorem tailTrace_1146172 : CollatzResearch.WordTrace tailWord_1146172 prefixEnd_1146172 588537148725194830478857 := by
  unfold tailWord_1146172
  simp only [CollatzResearch.WordTrace]
  refine ⟨20902163601811034719104385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27869551469081379625472513 20902163601811034719104385)
  ·
    refine ⟨15676622701358276039328289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20902163601811034719104385 15676622701358276039328289)
    ·
      refine ⟨11757467026018707029496217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15676622701358276039328289 11757467026018707029496217)
      ·
        refine ⟨8818100269514030272122163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11757467026018707029496217 8818100269514030272122163)
        ·
          refine ⟨13227150404271045408183245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8818100269514030272122163 13227150404271045408183245)
          ·
            refine ⟨4960181401601642028068717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13227150404271045408183245 4960181401601642028068717)
            ·
              refine ⟨1860068025600615760525769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4960181401601642028068717 1860068025600615760525769)
              ·
                refine ⟨1395051019200461820394327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860068025600615760525769 1395051019200461820394327)
                ·
                  refine ⟨2092576528800692730591491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395051019200461820394327 2092576528800692730591491)
                  ·
                    refine ⟨3138864793201039095887237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2092576528800692730591491 3138864793201039095887237)
                    ·
                      refine ⟨588537148725194830478857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3138864793201039095887237 588537148725194830478857)
                      ·
                        rfl

theorem cell23_1146172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_1146172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146172 prefixEnd_1146172 := by exact prefixLift 1146172
  have htrace : WordTrace (prefixWord ++ tailWord_1146172) baseStart_1146172 baseEnd_1146172 := by
    simpa [prefixWord, tailWord_1146172, baseEnd_1146172] using wordTrace_append hprefix tailTrace_1146172
  have hstable : (prefixWord ++ tailWord_1146172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146172).length < 2 ^ (prefixWord ++ tailWord_1146172).sum := by decide
  have hdescent : baseEnd_1146172 < baseStart_1146172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146275 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1146275 : Nat := 118140960795 + 1146275 * 2 ^ 59
def prefixEnd_1146275 : Nat := 4983230072969 + 3 ^ 40 * 1146275 * 2
def baseEnd_1146275 : Nat := 588590037232607927490883

theorem tailTrace_1146275 : CollatzResearch.WordTrace tailWord_1146275 prefixEnd_1146275 588590037232607927490883 := by
  unfold tailWord_1146275
  simp only [CollatzResearch.WordTrace]
  refine ⟨41808083922248918029208279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27872055948165945352805519 41808083922248918029208279)
  ·
    refine ⟨62712125883373377043812419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41808083922248918029208279 62712125883373377043812419)
    ·
      refine ⟨94068188825060065565718629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62712125883373377043812419 94068188825060065565718629)
      ·
        refine ⟨17637785404698762293572243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94068188825060065565718629 17637785404698762293572243)
        ·
          refine ⟨26456678107048143440358365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17637785404698762293572243 26456678107048143440358365)
          ·
            refine ⟨9921254290143053790134387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26456678107048143440358365 9921254290143053790134387)
            ·
              refine ⟨14881881435214580685201581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9921254290143053790134387 14881881435214580685201581)
              ·
                refine ⟨5580705538205467756950593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14881881435214580685201581 5580705538205467756950593)
                ·
                  refine ⟨4185529153654100817712945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5580705538205467756950593 4185529153654100817712945)
                  ·
                    refine ⟨3139146865240575613284709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4185529153654100817712945 3139146865240575613284709)
                    ·
                      refine ⟨588590037232607927490883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3139146865240575613284709 588590037232607927490883)
                      ·
                        rfl

theorem cell23_1146275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1146275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146275 prefixEnd_1146275 := by exact prefixLift 1146275
  have htrace : WordTrace (prefixWord ++ tailWord_1146275) baseStart_1146275 baseEnd_1146275 := by
    simpa [prefixWord, tailWord_1146275, baseEnd_1146275] using wordTrace_append hprefix tailTrace_1146275
  have hstable : (prefixWord ++ tailWord_1146275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146275).length < 2 ^ (prefixWord ++ tailWord_1146275).sum := by decide
  have hdescent : baseEnd_1146275 < baseStart_1146275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146315 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 4, 5]
def baseStart_1146315 : Nat := 118140960795 + 1146315 * 2 ^ 59
def prefixEnd_1146315 : Nat := 4983230072969 + 3 ^ 40 * 1146315 * 2
def baseEnd_1146315 : Nat := 196203525486262590330233

theorem tailTrace_1146315 : CollatzResearch.WordTrace tailWord_1146315 prefixEnd_1146315 196203525486262590330233 := by
  unfold tailWord_1146315
  simp only [CollatzResearch.WordTrace]
  refine ⟨41809542842104004860664399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27873028561402669907109599 41809542842104004860664399)
  ·
    refine ⟨62714314263156007290996599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41809542842104004860664399 62714314263156007290996599)
    ·
      refine ⟨94071471394734010936494899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62714314263156007290996599 94071471394734010936494899)
      ·
        refine ⟨141107207092101016404742349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94071471394734010936494899 141107207092101016404742349)
        ·
          refine ⟨52915202659537881151778381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141107207092101016404742349 52915202659537881151778381)
          ·
            refine ⟨19843200997326705431916893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52915202659537881151778381 19843200997326705431916893)
            ·
              refine ⟨7441200373997514536968835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19843200997326705431916893 7441200373997514536968835)
              ·
                refine ⟨11161800560996271805453253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7441200373997514536968835 11161800560996271805453253)
                ·
                  refine ⟨2092837605186800963522485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11161800560996271805453253 2092837605186800963522485)
                  ·
                    refine ⟨196203525486262590330233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2092837605186800963522485 196203525486262590330233)
                    ·
                      rfl

theorem cell23_1146315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 5].length) (baseStart_1146315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146315 prefixEnd_1146315 := by exact prefixLift 1146315
  have htrace : WordTrace (prefixWord ++ tailWord_1146315) baseStart_1146315 baseEnd_1146315 := by
    simpa [prefixWord, tailWord_1146315, baseEnd_1146315] using wordTrace_append hprefix tailTrace_1146315
  have hstable : (prefixWord ++ tailWord_1146315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146315).length < 2 ^ (prefixWord ++ tailWord_1146315).sum := by decide
  have hdescent : baseEnd_1146315 < baseStart_1146315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146352 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_1146352 : Nat := 118140960795 + 1146352 * 2 ^ 59
def prefixEnd_1146352 : Nat := 4983230072969 + 3 ^ 40 * 1146352 * 2
def baseEnd_1146352 : Nat := 588629575243004126228029

theorem tailTrace_1146352 : CollatzResearch.WordTrace tailWord_1146352 prefixEnd_1146352 588629575243004126228029 := by
  unfold tailWord_1146352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20905446171484980089880655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27873928228646640119840873 20905446171484980089880655)
  ·
    refine ⟨31358169257227470134820983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20905446171484980089880655 31358169257227470134820983)
    ·
      refine ⟨47037253885841205202231475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31358169257227470134820983 47037253885841205202231475)
      ·
        refine ⟨70555880828761807803347213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47037253885841205202231475 70555880828761807803347213)
        ·
          refine ⟨26458455310785677926255205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70555880828761807803347213 26458455310785677926255205)
          ·
            refine ⟨4960960370772314611172851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26458455310785677926255205 4960960370772314611172851)
            ·
              refine ⟨7441440556158471916759277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4960960370772314611172851 7441440556158471916759277)
              ·
                refine ⟨2790540208559426968784729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7441440556158471916759277 2790540208559426968784729)
                ·
                  refine ⟨2092905156419570226588547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2790540208559426968784729 2092905156419570226588547)
                  ·
                    refine ⟨3139357734629355339882821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2092905156419570226588547 3139357734629355339882821)
                    ·
                      refine ⟨588629575243004126228029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3139357734629355339882821 588629575243004126228029)
                      ·
                        rfl

theorem cell23_1146352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_1146352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146352 prefixEnd_1146352 := by exact prefixLift 1146352
  have htrace : WordTrace (prefixWord ++ tailWord_1146352) baseStart_1146352 baseEnd_1146352 := by
    simpa [prefixWord, tailWord_1146352, baseEnd_1146352] using wordTrace_append hprefix tailTrace_1146352
  have hstable : (prefixWord ++ tailWord_1146352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146352).length < 2 ^ (prefixWord ++ tailWord_1146352).sum := by decide
  have hdescent : baseEnd_1146352 < baseStart_1146352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146435 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 10]
def baseStart_1146435 : Nat := 118140960795 + 1146435 * 2 ^ 59
def prefixEnd_1146435 : Nat := 4983230072969 + 3 ^ 40 * 1146435 * 2
def baseEnd_1146435 : Nat := 196224064712442433830049

theorem tailTrace_1146435 : CollatzResearch.WordTrace tailWord_1146435 prefixEnd_1146435 196224064712442433830049 := by
  unfold tailWord_1146435
  simp only [CollatzResearch.WordTrace]
  refine ⟨41813919601669265355032759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27875946401112843570021839 41813919601669265355032759)
  ·
    refine ⟨62720879402503898032549139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41813919601669265355032759 62720879402503898032549139)
    ·
      refine ⟨94081319103755847048823709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62720879402503898032549139 94081319103755847048823709)
      ·
        refine ⟨35280494663908442643308891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94081319103755847048823709 35280494663908442643308891)
        ·
          refine ⟨52920741995862663964963337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35280494663908442643308891 52920741995862663964963337)
          ·
            refine ⟨39690556496896997973722503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52920741995862663964963337 39690556496896997973722503)
            ·
              refine ⟨59535834745345496960583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39690556496896997973722503 59535834745345496960583755)
              ·
                refine ⟨89303752118018245440875633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59535834745345496960583755 89303752118018245440875633)
                ·
                  refine ⟨66977814088513684080656725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89303752118018245440875633 66977814088513684080656725)
                  ·
                    refine ⟨196224064712442433830049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 66977814088513684080656725 196224064712442433830049)
                    ·
                      rfl

theorem cell23_1146435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 10].length) (baseStart_1146435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146435 prefixEnd_1146435 := by exact prefixLift 1146435
  have htrace : WordTrace (prefixWord ++ tailWord_1146435) baseStart_1146435 baseEnd_1146435 := by
    simpa [prefixWord, tailWord_1146435, baseEnd_1146435] using wordTrace_append hprefix tailTrace_1146435
  have hstable : (prefixWord ++ tailWord_1146435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146435).length < 2 ^ (prefixWord ++ tailWord_1146435).sum := by decide
  have hdescent : baseEnd_1146435 < baseStart_1146435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146469 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_1146469 : Nat := 118140960795 + 1146469 * 2 ^ 59
def prefixEnd_1146469 : Nat := 4983230072969 + 3 ^ 40 * 1146469 * 2
def baseEnd_1146469 : Nat := 196229884159860056154997

theorem tailTrace_1146469 : CollatzResearch.WordTrace tailWord_1146469 prefixEnd_1146469 196229884159860056154997 := by
  unfold tailWord_1146469
  simp only [CollatzResearch.WordTrace]
  refine ⟨41815159683546089161770461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27876773122364059441180307 41815159683546089161770461)
  ·
    refine ⟨15680684881329783435663923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41815159683546089161770461 15680684881329783435663923)
    ·
      refine ⟨23521027321994675153495885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15680684881329783435663923 23521027321994675153495885)
      ·
        refine ⟨8820385245748003182560957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23521027321994675153495885 8820385245748003182560957)
        ·
          refine ⟨3307644467155501193460359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8820385245748003182560957 3307644467155501193460359)
          ·
            refine ⟨4961466700733251790190539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307644467155501193460359 4961466700733251790190539)
            ·
              refine ⟨7442200051099877685285809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961466700733251790190539 7442200051099877685285809)
              ·
                refine ⟨5581650038324908263964357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7442200051099877685285809 5581650038324908263964357)
                ·
                  refine ⟨1046559382185920299493317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5581650038324908263964357 1046559382185920299493317)
                  ·
                    refine ⟨196229884159860056154997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046559382185920299493317 196229884159860056154997)
                    ·
                      rfl

theorem cell23_1146469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_1146469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146469 prefixEnd_1146469 := by exact prefixLift 1146469
  have htrace : WordTrace (prefixWord ++ tailWord_1146469) baseStart_1146469 baseEnd_1146469 := by
    simpa [prefixWord, tailWord_1146469, baseEnd_1146469] using wordTrace_append hprefix tailTrace_1146469
  have hstable : (prefixWord ++ tailWord_1146469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146469).length < 2 ^ (prefixWord ++ tailWord_1146469).sum := by decide
  have hdescent : baseEnd_1146469 < baseStart_1146469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146482 : List Nat := [3, 2, 1, 2, 3, 1, 11]
def baseStart_1146482 : Nat := 118140960795 + 1146482 * 2 ^ 59
def prefixEnd_1146482 : Nat := 4983230072969 + 3 ^ 40 * 1146482 * 2
def baseEnd_1146482 : Nat := 7267855897877637254351

theorem tailTrace_1146482 : CollatzResearch.WordTrace tailWord_1146482 prefixEnd_1146482 7267855897877637254351 := by
  unfold tailWord_1146482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10453908458124748095498425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27877089221665994921329133 10453908458124748095498425)
  ·
    refine ⟨7840431343593561071623819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10453908458124748095498425 7840431343593561071623819)
    ·
      refine ⟨11760647015390341607435729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7840431343593561071623819 11760647015390341607435729)
      ·
        refine ⟨8820485261542756205576797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11760647015390341607435729 8820485261542756205576797)
        ·
          refine ⟨3307681973078533577091299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8820485261542756205576797 3307681973078533577091299)
          ·
            refine ⟨4961522959617800365636949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307681973078533577091299 4961522959617800365636949)
            ·
              refine ⟨7267855897877637254351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4961522959617800365636949 7267855897877637254351)
              ·
                rfl

theorem cell23_1146482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 11].length) (baseStart_1146482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146482 prefixEnd_1146482 := by exact prefixLift 1146482
  have htrace : WordTrace (prefixWord ++ tailWord_1146482) baseStart_1146482 baseEnd_1146482 := by
    simpa [prefixWord, tailWord_1146482, baseEnd_1146482] using wordTrace_append hprefix tailTrace_1146482
  have hstable : (prefixWord ++ tailWord_1146482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146482).length < 2 ^ (prefixWord ++ tailWord_1146482).sum := by decide
  have hdescent : baseEnd_1146482 < baseStart_1146482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146486 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1146486 : Nat := 118140960795 + 1146486 * 2 ^ 59
def prefixEnd_1146486 : Nat := 4983230072969 + 3 ^ 40 * 1146486 * 2
def baseEnd_1146486 : Nat := 196232793883568867317471

theorem tailTrace_1146486 : CollatzResearch.WordTrace tailWord_1146486 prefixEnd_1146486 196232793883568867317471 := by
  unfold tailWord_1146486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2613486232780281316571207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27877186482989667376759541 2613486232780281316571207)
  ·
    refine ⟨3920229349170421974856811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2613486232780281316571207 3920229349170421974856811)
    ·
      refine ⟨5880344023755632962285217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3920229349170421974856811 5880344023755632962285217)
      ·
        refine ⟨4410258017816724721713913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5880344023755632962285217 4410258017816724721713913)
        ·
          refine ⟨3307693513362543541285435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4410258017816724721713913 3307693513362543541285435)
          ·
            refine ⟨4961540270043815311928153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307693513362543541285435 4961540270043815311928153)
            ·
              refine ⟨3721155202532861483946115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4961540270043815311928153 3721155202532861483946115)
              ·
                refine ⟨5581732803799292225919173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721155202532861483946115 5581732803799292225919173)
                ·
                  refine ⟨1046574900712367292359845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5581732803799292225919173 1046574900712367292359845)
                  ·
                    refine ⟨196232793883568867317471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046574900712367292359845 196232793883568867317471)
                    ·
                      rfl

theorem cell23_1146486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1146486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146486 prefixEnd_1146486 := by exact prefixLift 1146486
  have htrace : WordTrace (prefixWord ++ tailWord_1146486) baseStart_1146486 baseEnd_1146486 := by
    simpa [prefixWord, tailWord_1146486, baseEnd_1146486] using wordTrace_append hprefix tailTrace_1146486
  have hstable : (prefixWord ++ tailWord_1146486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146486).length < 2 ^ (prefixWord ++ tailWord_1146486).sum := by decide
  have hdescent : baseEnd_1146486 < baseStart_1146486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146493 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_1146493 : Nat := 118140960795 + 1146493 * 2 ^ 59
def prefixEnd_1146493 : Nat := 4983230072969 + 3 ^ 40 * 1146493 * 2
def baseEnd_1146493 : Nat := 588701976015288074564881

theorem tailTrace_1146493 : CollatzResearch.WordTrace tailWord_1146493 prefixEnd_1146493 588701976015288074564881 := by
  unfold tailWord_1146493
  simp only [CollatzResearch.WordTrace]
  refine ⟨41816035035459141260644133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27877356690306094173762755 41816035035459141260644133)
  ·
    refine ⟨7840506569148588986370775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41816035035459141260644133 7840506569148588986370775)
    ·
      refine ⟨11760759853722883479556163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7840506569148588986370775 11760759853722883479556163)
      ·
        refine ⟨17641139780584325219334245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11760759853722883479556163 17641139780584325219334245)
        ·
          refine ⟨3307713708859560978625171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17641139780584325219334245 3307713708859560978625171)
          ·
            refine ⟨4961570563289341467937757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3307713708859560978625171 4961570563289341467937757)
            ·
              refine ⟨1860588961233503050476659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4961570563289341467937757 1860588961233503050476659)
              ·
                refine ⟨2790883441850254575714989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860588961233503050476659 2790883441850254575714989)
                ·
                  refine ⟨1046581290693845465893121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2790883441850254575714989 1046581290693845465893121)
                  ·
                    refine ⟨784935968020384099419841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046581290693845465893121 784935968020384099419841)
                    ·
                      refine ⟨588701976015288074564881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 784935968020384099419841 588701976015288074564881)
                      ·
                        rfl

theorem cell23_1146493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_1146493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146493 prefixEnd_1146493 := by exact prefixLift 1146493
  have htrace : WordTrace (prefixWord ++ tailWord_1146493) baseStart_1146493 baseEnd_1146493 := by
    simpa [prefixWord, tailWord_1146493, baseEnd_1146493] using wordTrace_append hprefix tailTrace_1146493
  have hstable : (prefixWord ++ tailWord_1146493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146493).length < 2 ^ (prefixWord ++ tailWord_1146493).sum := by decide
  have hdescent : baseEnd_1146493 < baseStart_1146493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146503 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 2, 4]
def baseStart_1146503 : Nat := 118140960795 + 1146503 * 2 ^ 59
def prefixEnd_1146503 : Nat := 4983230072969 + 3 ^ 40 * 1146503 * 2
def baseEnd_1146503 : Nat := 196235703607277678479945

theorem tailTrace_1146503 : CollatzResearch.WordTrace tailWord_1146503 prefixEnd_1146503 196235703607277678479945 := by
  unfold tailWord_1146503
  simp only [CollatzResearch.WordTrace]
  refine ⟨41816399765422912968508163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27877599843615275312338775 41816399765422912968508163)
  ·
    refine ⟨62724599648134369452762245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41816399765422912968508163 62724599648134369452762245)
    ·
      refine ⟨11760862434025194272392921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62724599648134369452762245 11760862434025194272392921)
      ·
        refine ⟨8820646825518895704294691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11760862434025194272392921 8820646825518895704294691)
        ·
          refine ⟨13230970238278343556442037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8820646825518895704294691 13230970238278343556442037)
          ·
            refine ⟨1240403459838594708416441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13230970238278343556442037 1240403459838594708416441)
            ·
              refine ⟨930302594878946031312331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1240403459838594708416441 930302594878946031312331)
              ·
                refine ⟨1395453892318419046968497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930302594878946031312331 1395453892318419046968497)
                ·
                  refine ⟨1046590419238814285226373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1395453892318419046968497 1046590419238814285226373)
                  ·
                    refine ⟨196235703607277678479945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1046590419238814285226373 196235703607277678479945)
                    ·
                      rfl

theorem cell23_1146503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_1146503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146503 prefixEnd_1146503 := by exact prefixLift 1146503
  have htrace : WordTrace (prefixWord ++ tailWord_1146503) baseStart_1146503 baseEnd_1146503 := by
    simpa [prefixWord, tailWord_1146503, baseEnd_1146503] using wordTrace_append hprefix tailTrace_1146503
  have hstable : (prefixWord ++ tailWord_1146503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146503).length < 2 ^ (prefixWord ++ tailWord_1146503).sum := by decide
  have hdescent : baseEnd_1146503 < baseStart_1146503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146526 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1146526 : Nat := 118140960795 + 1146526 * 2 ^ 59
def prefixEnd_1146526 : Nat := 4983230072969 + 3 ^ 40 * 1146526 * 2
def baseEnd_1146526 : Nat := 588718920876886445452229

theorem tailTrace_1146526 : CollatzResearch.WordTrace tailWord_1146526 prefixEnd_1146526 588718920876886445452229 := by
  unfold tailWord_1146526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227154830542448487074429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27878159096226391931063621 5227154830542448487074429)
  ·
    refine ⟨1960183061453418182652911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5227154830542448487074429 1960183061453418182652911)
    ·
      refine ⟨2940274592180127273979367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1960183061453418182652911 2940274592180127273979367)
      ·
        refine ⟨4410411888270190910969051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940274592180127273979367 4410411888270190910969051)
        ·
          refine ⟨6615617832405286366453577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410411888270190910969051 6615617832405286366453577)
          ·
            refine ⟨4961713374303964774840183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6615617832405286366453577 4961713374303964774840183)
            ·
              refine ⟨7442570061455947162260275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961713374303964774840183 7442570061455947162260275)
              ·
                refine ⟨11163855092183920743390413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7442570061455947162260275 11163855092183920743390413)
                ·
                  refine ⟨4186445659568970278771405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11163855092183920743390413 4186445659568970278771405)
                  ·
                    refine ⟨1569917122338363854539277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4186445659568970278771405 1569917122338363854539277)
                    ·
                      refine ⟨588718920876886445452229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1569917122338363854539277 588718920876886445452229)
                      ·
                        rfl

theorem cell23_1146526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1146526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146526 prefixEnd_1146526 := by exact prefixLift 1146526
  have htrace : WordTrace (prefixWord ++ tailWord_1146526) baseStart_1146526 baseEnd_1146526 := by
    simpa [prefixWord, tailWord_1146526, baseEnd_1146526] using wordTrace_append hprefix tailTrace_1146526
  have hstable : (prefixWord ++ tailWord_1146526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146526).length < 2 ^ (prefixWord ++ tailWord_1146526).sum := by decide
  have hdescent : baseEnd_1146526 < baseStart_1146526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146530 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 1, 1, 5]
def baseStart_1146530 : Nat := 118140960795 + 1146530 * 2 ^ 59
def prefixEnd_1146530 : Nat := 4983230072969 + 3 ^ 40 * 1146530 * 2
def baseEnd_1146530 : Nat := 588720974799504429802211

theorem tailTrace_1146530 : CollatzResearch.WordTrace tailWord_1146530 prefixEnd_1146530 588720974799504429802211 := by
  unfold tailWord_1146530
  simp only [CollatzResearch.WordTrace]
  refine ⟨10454346134081274144935261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27878256357550064386494029 10454346134081274144935261)
  ·
    refine ⟨3920379800280477804350723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10454346134081274144935261 3920379800280477804350723)
    ·
      refine ⟨5880569700420716706526085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3920379800280477804350723 5880569700420716706526085)
      ·
        refine ⟨1102606818828884382473641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5880569700420716706526085 1102606818828884382473641)
        ·
          refine ⟨826955114121663286855231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1102606818828884382473641 826955114121663286855231)
          ·
            refine ⟨1240432671182494930282847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826955114121663286855231 1240432671182494930282847)
            ·
              refine ⟨1860649006773742395424271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1240432671182494930282847 1860649006773742395424271)
              ·
                refine ⟨2790973510160613593136407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1860649006773742395424271 2790973510160613593136407)
                ·
                  refine ⟨4186460265240920389704611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790973510160613593136407 4186460265240920389704611)
                  ·
                    refine ⟨6279690397861380584556917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186460265240920389704611 6279690397861380584556917)
                    ·
                      refine ⟨588720974799504429802211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6279690397861380584556917 588720974799504429802211)
                      ·
                        rfl

theorem cell23_1146530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_1146530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146530 prefixEnd_1146530 := by exact prefixLift 1146530
  have htrace : WordTrace (prefixWord ++ tailWord_1146530) baseStart_1146530 baseEnd_1146530 := by
    simpa [prefixWord, tailWord_1146530, baseEnd_1146530] using wordTrace_append hprefix tailTrace_1146530
  have hstable : (prefixWord ++ tailWord_1146530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146530).length < 2 ^ (prefixWord ++ tailWord_1146530).sum := by decide
  have hdescent : baseEnd_1146530 < baseStart_1146530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146552 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_1146552 : Nat := 118140960795 + 1146552 * 2 ^ 59
def prefixEnd_1146552 : Nat := 4983230072969 + 3 ^ 40 * 1146552 * 2
def baseEnd_1146552 : Nat := 588732271373903343727109

theorem tailTrace_1146552 : CollatzResearch.WordTrace tailWord_1146552 prefixEnd_1146552 588732271373903343727109 := by
  unfold tailWord_1146552
  simp only [CollatzResearch.WordTrace]
  refine ⟨20909093471122697168520955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27878791294830262891361273 20909093471122697168520955)
  ·
    refine ⟨31363640206684045752781433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20909093471122697168520955 31363640206684045752781433)
    ·
      refine ⟨23522730155013034314586075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31363640206684045752781433 23522730155013034314586075)
      ·
        refine ⟨35284095232519551471879113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23522730155013034314586075 35284095232519551471879113)
        ·
          refine ⟨26463071424389663603909335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35284095232519551471879113 26463071424389663603909335)
          ·
            refine ⟨39694607136584495405864003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26463071424389663603909335 39694607136584495405864003)
            ·
              refine ⟨59541910704876743108796005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39694607136584495405864003 59541910704876743108796005)
              ·
                refine ⟨11164108257164389332899251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59541910704876743108796005 11164108257164389332899251)
                ·
                  refine ⟨16746162385746583999348877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11164108257164389332899251 16746162385746583999348877)
                  ·
                    refine ⟨6279810894654968999755829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16746162385746583999348877 6279810894654968999755829)
                    ·
                      refine ⟨588732271373903343727109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6279810894654968999755829 588732271373903343727109)
                      ·
                        rfl

theorem cell23_1146552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_1146552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146552 prefixEnd_1146552 := by exact prefixLift 1146552
  have htrace : WordTrace (prefixWord ++ tailWord_1146552) baseStart_1146552 baseEnd_1146552 := by
    simpa [prefixWord, tailWord_1146552, baseEnd_1146552] using wordTrace_append hprefix tailTrace_1146552
  have hstable : (prefixWord ++ tailWord_1146552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146552).length < 2 ^ (prefixWord ++ tailWord_1146552).sum := by decide
  have hdescent : baseEnd_1146552 < baseStart_1146552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146600 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1146600 : Nat := 118140960795 + 1146600 * 2 ^ 59
def prefixEnd_1146600 : Nat := 4983230072969 + 3 ^ 40 * 1146600 * 2
def baseEnd_1146600 : Nat := 588756918445319155926889

theorem tailTrace_1146600 : CollatzResearch.WordTrace tailWord_1146600 prefixEnd_1146600 588756918445319155926889 := by
  unfold tailWord_1146600
  simp only [CollatzResearch.WordTrace]
  refine ⟨20909968823035749267394627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27879958430714332356526169 20909968823035749267394627)
  ·
    refine ⟨31364953234553623901091941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20909968823035749267394627 31364953234553623901091941)
    ·
      refine ⟨5880928731478804481454739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31364953234553623901091941 5880928731478804481454739)
      ·
        refine ⟨8821393097218206722182109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880928731478804481454739 8821393097218206722182109)
        ·
          refine ⟨3308022411456827520818291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8821393097218206722182109 3308022411456827520818291)
          ·
            refine ⟨4962033617185241281227437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308022411456827520818291 4962033617185241281227437)
            ·
              refine ⟨1860762606444465480460289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4962033617185241281227437 1860762606444465480460289)
              ·
                refine ⟨1395571954833349110345217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860762606444465480460289 1395571954833349110345217)
                ·
                  refine ⟨1046678966125011832758913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1395571954833349110345217 1046678966125011832758913)
                  ·
                    refine ⟨785009224593758874569185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046678966125011832758913 785009224593758874569185)
                    ·
                      refine ⟨588756918445319155926889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785009224593758874569185 588756918445319155926889)
                      ·
                        rfl

theorem cell23_1146600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1146600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146600 prefixEnd_1146600 := by exact prefixLift 1146600
  have htrace : WordTrace (prefixWord ++ tailWord_1146600) baseStart_1146600 baseEnd_1146600 := by
    simpa [prefixWord, tailWord_1146600, baseEnd_1146600] using wordTrace_append hprefix tailTrace_1146600
  have hstable : (prefixWord ++ tailWord_1146600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146600).length < 2 ^ (prefixWord ++ tailWord_1146600).sum := by decide
  have hdescent : baseEnd_1146600 < baseStart_1146600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146606 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_1146606 : Nat := 118140960795 + 1146606 * 2 ^ 59
def prefixEnd_1146606 : Nat := 4983230072969 + 3 ^ 40 * 1146606 * 2
def baseEnd_1146606 : Nat := 65417777703249570272429

theorem tailTrace_1146606 : CollatzResearch.WordTrace tailWord_1146606 prefixEnd_1146606 65417777703249570272429 := by
  unfold tailWord_1146606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227519560506220194938459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27880104322699841039671781 5227519560506220194938459)
  ·
    refine ⟨7841279340759330292407689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227519560506220194938459 7841279340759330292407689)
    ·
      refine ⟨5880959505569497719305767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7841279340759330292407689 5880959505569497719305767)
      ·
        refine ⟨8821439258354246578958651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5880959505569497719305767 8821439258354246578958651)
        ·
          refine ⟨13232158887531369868437977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8821439258354246578958651 13232158887531369868437977)
          ·
            refine ⟨9924119165648527401328483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13232158887531369868437977 9924119165648527401328483)
            ·
              refine ⟨14886178748472791101992725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924119165648527401328483 14886178748472791101992725)
              ·
                refine ⟨697789628834662082905909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14886178748472791101992725 697789628834662082905909)
                ·
                  refine ⟨65417777703249570272429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 697789628834662082905909 65417777703249570272429)
                  ·
                    rfl

theorem cell23_1146606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_1146606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146606 prefixEnd_1146606 := by exact prefixLift 1146606
  have htrace : WordTrace (prefixWord ++ tailWord_1146606) baseStart_1146606 baseEnd_1146606 := by
    simpa [prefixWord, tailWord_1146606, baseEnd_1146606] using wordTrace_append hprefix tailTrace_1146606
  have hstable : (prefixWord ++ tailWord_1146606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146606).length < 2 ^ (prefixWord ++ tailWord_1146606).sum := by decide
  have hdescent : baseEnd_1146606 < baseStart_1146606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146637 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1146637 : Nat := 118140960795 + 1146637 * 2 ^ 59
def prefixEnd_1146637 : Nat := 4983230072969 + 3 ^ 40 * 1146637 * 2
def baseEnd_1146637 : Nat := 588775917229535511164219

theorem tailTrace_1146637 : CollatzResearch.WordTrace tailWord_1146637 prefixEnd_1146637 588775917229535511164219 := by
  unfold tailWord_1146637
  simp only [CollatzResearch.WordTrace]
  refine ⟨41821287146937453853886165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27880858097958302569257443 41821287146937453853886165)
  ·
    refine ⟨980186417506346574700457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 41821287146937453853886165 980186417506346574700457)
    ·
      refine ⟨735139813129759931025343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 980186417506346574700457 735139813129759931025343)
      ·
        refine ⟨1102709719694639896538015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 735139813129759931025343 1102709719694639896538015)
        ·
          refine ⟨1654064579541959844807023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102709719694639896538015 1654064579541959844807023)
          ·
            refine ⟨2481096869312939767210535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654064579541959844807023 2481096869312939767210535)
            ·
              refine ⟨3721645303969409650815803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481096869312939767210535 3721645303969409650815803)
              ·
                refine ⟨5582467955954114476223705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721645303969409650815803 5582467955954114476223705)
                ·
                  refine ⟨4186850966965585857167779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582467955954114476223705 4186850966965585857167779)
                  ·
                    refine ⟨6280276450448378785751669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186850966965585857167779 6280276450448378785751669)
                    ·
                      refine ⟨588775917229535511164219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6280276450448378785751669 588775917229535511164219)
                      ·
                        rfl

theorem cell23_1146637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1146637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146637 prefixEnd_1146637 := by exact prefixLift 1146637
  have htrace : WordTrace (prefixWord ++ tailWord_1146637) baseStart_1146637 baseEnd_1146637 := by
    simpa [prefixWord, tailWord_1146637, baseEnd_1146637] using wordTrace_append hprefix tailTrace_1146637
  have hstable : (prefixWord ++ tailWord_1146637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146637).length < 2 ^ (prefixWord ++ tailWord_1146637).sum := by decide
  have hdescent : baseEnd_1146637 < baseStart_1146637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146656 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1146656 : Nat := 118140960795 + 1146656 * 2 ^ 59
def prefixEnd_1146656 : Nat := 4983230072969 + 3 ^ 40 * 1146656 * 2
def baseEnd_1146656 : Nat := 588785673361970936826631

theorem tailTrace_1146656 : CollatzResearch.WordTrace tailWord_1146656 prefixEnd_1146656 588785673361970936826631 := by
  unfold tailWord_1146656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20910990066934310049413911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27881320089245746732551881 20910990066934310049413911)
  ·
    refine ⟨31366485100401465074120867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20910990066934310049413911 31366485100401465074120867)
    ·
      refine ⟨47049727650602197611181301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31366485100401465074120867 47049727650602197611181301)
      ·
        refine ⟨4410911967243956026048247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47049727650602197611181301 4410911967243956026048247)
        ·
          refine ⟨6616367950865934039072371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410911967243956026048247 6616367950865934039072371)
          ·
            refine ⟨9924551926298901058608557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616367950865934039072371 9924551926298901058608557)
            ·
              refine ⟨3721706972362087896978209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9924551926298901058608557 3721706972362087896978209)
              ·
                refine ⟨2791280229271565922733657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3721706972362087896978209 2791280229271565922733657)
                ·
                  refine ⟨2093460171953674442050243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2791280229271565922733657 2093460171953674442050243)
                  ·
                    refine ⟨3140190257930511663075365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2093460171953674442050243 3140190257930511663075365)
                    ·
                      refine ⟨588785673361970936826631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3140190257930511663075365 588785673361970936826631)
                      ·
                        rfl

theorem cell23_1146656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1146656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146656 prefixEnd_1146656 := by exact prefixLift 1146656
  have htrace : WordTrace (prefixWord ++ tailWord_1146656) baseStart_1146656 baseEnd_1146656 := by
    simpa [prefixWord, tailWord_1146656, baseEnd_1146656] using wordTrace_append hprefix tailTrace_1146656
  have hstable : (prefixWord ++ tailWord_1146656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146656).length < 2 ^ (prefixWord ++ tailWord_1146656).sum := by decide
  have hdescent : baseEnd_1146656 < baseStart_1146656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146733 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1146733 : Nat := 118140960795 + 1146733 * 2 ^ 59
def prefixEnd_1146733 : Nat := 4983230072969 + 3 ^ 40 * 1146733 * 2
def baseEnd_1146733 : Nat := 588825211372367135563777

theorem tailTrace_1146733 : CollatzResearch.WordTrace tailWord_1146733 prefixEnd_1146733 588825211372367135563777 := by
  unfold tailWord_1146733
  simp only [CollatzResearch.WordTrace]
  refine ⟨41824788554589662249380853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27883192369726441499587235 41824788554589662249380853)
  ·
    refine ⟨3921073926992780835879455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41824788554589662249380853 3921073926992780835879455)
    ·
      refine ⟨5881610890489171253819183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3921073926992780835879455 5881610890489171253819183)
      ·
        refine ⟨8822416335733756880728775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881610890489171253819183 8822416335733756880728775)
        ·
          refine ⟨13233624503600635321093163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8822416335733756880728775 13233624503600635321093163)
          ·
            refine ⟨19850436755400952981639745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13233624503600635321093163 19850436755400952981639745)
            ·
              refine ⟨14887827566550714736229809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19850436755400952981639745 14887827566550714736229809)
              ·
                refine ⟨11165870674913036052172357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14887827566550714736229809 11165870674913036052172357)
                ·
                  refine ⟨2093600751546194259782317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11165870674913036052172357 2093600751546194259782317)
                  ·
                    refine ⟨785100281829822847418369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093600751546194259782317 785100281829822847418369)
                    ·
                      refine ⟨588825211372367135563777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785100281829822847418369 588825211372367135563777)
                      ·
                        rfl

theorem cell23_1146733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1146733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146733 prefixEnd_1146733 := by exact prefixLift 1146733
  have htrace : WordTrace (prefixWord ++ tailWord_1146733) baseStart_1146733 baseEnd_1146733 := by
    simpa [prefixWord, tailWord_1146733, baseEnd_1146733] using wordTrace_append hprefix tailTrace_1146733
  have hstable : (prefixWord ++ tailWord_1146733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146733).length < 2 ^ (prefixWord ++ tailWord_1146733).sum := by decide
  have hdescent : baseEnd_1146733 < baseStart_1146733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146746 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1146746 : Nat := 118140960795 + 1146746 * 2 ^ 59
def prefixEnd_1146746 : Nat := 4983230072969 + 3 ^ 40 * 1146746 * 2
def baseEnd_1146746 : Nat := 588831886620875584701217

theorem tailTrace_1146746 : CollatzResearch.WordTrace tailWord_1146746 prefixEnd_1146746 588831886620875584701217 := by
  unfold tailWord_1146746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10456315675885641367401023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27883508469028376979736061 10456315675885641367401023)
  ·
    refine ⟨15684473513828462051101535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10456315675885641367401023 15684473513828462051101535)
    ·
      refine ⟨23526710270742693076652303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15684473513828462051101535 23526710270742693076652303)
      ·
        refine ⟨35290065406114039614978455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23526710270742693076652303 35290065406114039614978455)
        ·
          refine ⟨52935098109171059422467683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35290065406114039614978455 52935098109171059422467683)
          ·
            refine ⟨79402647163756589133701525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52935098109171059422467683 79402647163756589133701525)
            ·
              refine ⟨3721999085801090115642259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79402647163756589133701525 3721999085801090115642259)
              ·
                refine ⟨5582998628701635173463389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721999085801090115642259 5582998628701635173463389)
                ·
                  refine ⟨2093624485763113190048771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5582998628701635173463389 2093624485763113190048771)
                  ·
                    refine ⟨3140436728644669785073157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2093624485763113190048771 3140436728644669785073157)
                    ·
                      refine ⟨588831886620875584701217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3140436728644669785073157 588831886620875584701217)
                      ·
                        rfl

theorem cell23_1146746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1146746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146746 prefixEnd_1146746 := by exact prefixLift 1146746
  have htrace : WordTrace (prefixWord ++ tailWord_1146746) baseStart_1146746 baseEnd_1146746 := by
    simpa [prefixWord, tailWord_1146746, baseEnd_1146746] using wordTrace_append hprefix tailTrace_1146746
  have hstable : (prefixWord ++ tailWord_1146746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146746).length < 2 ^ (prefixWord ++ tailWord_1146746).sum := by decide
  have hdescent : baseEnd_1146746 < baseStart_1146746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146756 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_1146756 : Nat := 118140960795 + 1146756 * 2 ^ 59
def prefixEnd_1146756 : Nat := 4983230072969 + 3 ^ 40 * 1146756 * 2
def baseEnd_1146756 : Nat := 196279007142473515192057

theorem tailTrace_1146756 : CollatzResearch.WordTrace tailWord_1146756 prefixEnd_1146756 196279007142473515192057 := by
  unfold tailWord_1146756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912813716753168588734061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27883751622337558118312081 20912813716753168588734061)
  ·
    refine ⟨7842305143782438220775273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20912813716753168588734061 7842305143782438220775273)
    ·
      refine ⟨5881728857836828665581455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7842305143782438220775273 5881728857836828665581455)
      ·
        refine ⟨8822593286755242998372183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881728857836828665581455 8822593286755242998372183)
        ·
          refine ⟨13233889930132864497558275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8822593286755242998372183 13233889930132864497558275)
          ·
            refine ⟨19850834895199296746337413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13233889930132864497558275 19850834895199296746337413)
            ·
              refine ⟨3722031542849868139938265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19850834895199296746337413 3722031542849868139938265)
              ·
                refine ⟨2791523657137401104953699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722031542849868139938265 2791523657137401104953699)
                ·
                  refine ⟨4187285485706101657430549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791523657137401104953699 4187285485706101657430549)
                  ·
                    refine ⟨196279007142473515192057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4187285485706101657430549 196279007142473515192057)
                    ·
                      rfl

theorem cell23_1146756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_1146756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146756 prefixEnd_1146756 := by exact prefixLift 1146756
  have htrace : WordTrace (prefixWord ++ tailWord_1146756) baseStart_1146756 baseEnd_1146756 := by
    simpa [prefixWord, tailWord_1146756, baseEnd_1146756] using wordTrace_append hprefix tailTrace_1146756
  have hstable : (prefixWord ++ tailWord_1146756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146756).length < 2 ^ (prefixWord ++ tailWord_1146756).sum := by decide
  have hdescent : baseEnd_1146756 < baseStart_1146756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146763 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 7, 2, 2]
def baseStart_1146763 : Nat := 118140960795 + 1146763 * 2 ^ 59
def prefixEnd_1146763 : Nat := 4983230072969 + 3 ^ 40 * 1146763 * 2
def baseEnd_1146763 : Nat := 588840615792002018188639

theorem tailTrace_1146763 : CollatzResearch.WordTrace tailWord_1146763 prefixEnd_1146763 588840615792002018188639 := by
  unfold tailWord_1146763
  simp only [CollatzResearch.WordTrace]
  refine ⟨41825882744480977372972943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27883921829653984915315295 41825882744480977372972943)
  ·
    refine ⟨62738824116721466059459415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41825882744480977372972943 62738824116721466059459415)
    ·
      refine ⟨94108236175082199089189123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62738824116721466059459415 94108236175082199089189123)
      ·
        refine ⟨141162354262623298633783685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94108236175082199089189123 141162354262623298633783685)
        ·
          refine ⟨26467941424241868493834441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141162354262623298633783685 26467941424241868493834441)
          ·
            refine ⟨19850956068181401370375831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26467941424241868493834441 19850956068181401370375831)
            ·
              refine ⟨29776434102272102055563747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19850956068181401370375831 29776434102272102055563747)
              ·
                refine ⟨44664651153408153083345621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29776434102272102055563747 44664651153408153083345621)
                ·
                  refine ⟨1046827761408003587890913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 44664651153408153083345621 1046827761408003587890913)
                  ·
                    refine ⟨785120821056002690918185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046827761408003587890913 785120821056002690918185)
                    ·
                      refine ⟨588840615792002018188639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785120821056002690918185 588840615792002018188639)
                      ·
                        rfl

theorem cell23_1146763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 2, 2].length) (baseStart_1146763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146763 prefixEnd_1146763 := by exact prefixLift 1146763
  have htrace : WordTrace (prefixWord ++ tailWord_1146763) baseStart_1146763 baseEnd_1146763 := by
    simpa [prefixWord, tailWord_1146763, baseEnd_1146763] using wordTrace_append hprefix tailTrace_1146763
  have hstable : (prefixWord ++ tailWord_1146763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146763).length < 2 ^ (prefixWord ++ tailWord_1146763).sum := by decide
  have hdescent : baseEnd_1146763 < baseStart_1146763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146783 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1146783 : Nat := 118140960795 + 1146783 * 2 ^ 59
def prefixEnd_1146783 : Nat := 4983230072969 + 3 ^ 40 * 1146783 * 2
def baseEnd_1146783 : Nat := 588850885405091939938547

theorem tailTrace_1146783 : CollatzResearch.WordTrace tailWord_1146783 prefixEnd_1146783 588850885405091939938547 := by
  unfold tailWord_1146783
  simp only [CollatzResearch.WordTrace]
  refine ⟨41826612204408520788701003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27884408136272347192467335 41826612204408520788701003)
  ·
    refine ⟨62739918306612781183051505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41826612204408520788701003 62739918306612781183051505)
    ·
      refine ⟨47054938729959585887288629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62739918306612781183051505 47054938729959585887288629)
      ·
        refine ⟨4411400505933711176933309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47054938729959585887288629 4411400505933711176933309)
        ·
          refine ⟨1654275189725141691349991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4411400505933711176933309 1654275189725141691349991)
          ·
            refine ⟨2481412784587712537024987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654275189725141691349991 2481412784587712537024987)
            ·
              refine ⟨3722119176881568805537481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481412784587712537024987 3722119176881568805537481)
              ·
                refine ⟨2791589382661176604153111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722119176881568805537481 2791589382661176604153111)
                ·
                  refine ⟨4187384073991764906229667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791589382661176604153111 4187384073991764906229667)
                  ·
                    refine ⟨6281076110987647359344501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187384073991764906229667 6281076110987647359344501)
                    ·
                      refine ⟨588850885405091939938547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6281076110987647359344501 588850885405091939938547)
                      ·
                        rfl

theorem cell23_1146783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1146783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146783 prefixEnd_1146783 := by exact prefixLift 1146783
  have htrace : WordTrace (prefixWord ++ tailWord_1146783) baseStart_1146783 baseEnd_1146783 := by
    simpa [prefixWord, tailWord_1146783, baseEnd_1146783] using wordTrace_append hprefix tailTrace_1146783
  have hstable : (prefixWord ++ tailWord_1146783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146783).length < 2 ^ (prefixWord ++ tailWord_1146783).sum := by decide
  have hdescent : baseEnd_1146783 < baseStart_1146783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146814 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_1146814 : Nat := 118140960795 + 1146814 * 2 ^ 59
def prefixEnd_1146814 : Nat := 4983230072969 + 3 ^ 40 * 1146814 * 2
def baseEnd_1146814 : Nat := 588866803305381318650905

theorem tailTrace_1146814 : CollatzResearch.WordTrace tailWord_1146814 prefixEnd_1146814 588866803305381318650905 := by
  unfold tailWord_1146814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228467858412026635384937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27885161911530808722052997 5228467858412026635384937)
  ·
    refine ⟨3921350893809019976538703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5228467858412026635384937 3921350893809019976538703)
    ·
      refine ⟨5882026340713529964808055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3921350893809019976538703 5882026340713529964808055)
      ·
        refine ⟨8823039511070294947212083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5882026340713529964808055 8823039511070294947212083)
        ·
          refine ⟨13234559266605442420818125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8823039511070294947212083 13234559266605442420818125)
          ·
            refine ⟨4962959724977040907806797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13234559266605442420818125 4962959724977040907806797)
            ·
              refine ⟨1861109896866390340427549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4962959724977040907806797 1861109896866390340427549)
              ·
                refine ⟨697916211324896377660331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1861109896866390340427549 697916211324896377660331)
                ·
                  refine ⟨1046874316987344566490497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 697916211324896377660331 1046874316987344566490497)
                  ·
                    refine ⟨785155737740508424867873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046874316987344566490497 785155737740508424867873)
                    ·
                      refine ⟨588866803305381318650905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785155737740508424867873 588866803305381318650905)
                      ·
                        rfl

theorem cell23_1146814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_1146814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146814 prefixEnd_1146814 := by exact prefixLift 1146814
  have htrace : WordTrace (prefixWord ++ tailWord_1146814) baseStart_1146814 baseEnd_1146814 := by
    simpa [prefixWord, tailWord_1146814, baseEnd_1146814] using wordTrace_append hprefix tailTrace_1146814
  have hstable : (prefixWord ++ tailWord_1146814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146814).length < 2 ^ (prefixWord ++ tailWord_1146814).sum := by decide
  have hdescent : baseEnd_1146814 < baseStart_1146814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146823 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_1146823 : Nat := 118140960795 + 1146823 * 2 ^ 59
def prefixEnd_1146823 : Nat := 4983230072969 + 3 ^ 40 * 1146823 * 2
def baseEnd_1146823 : Nat := 588871424631271783438363

theorem tailTrace_1146823 : CollatzResearch.WordTrace tailWord_1146823 prefixEnd_1146823 588871424631271783438363 := by
  unfold tailWord_1146823
  simp only [CollatzResearch.WordTrace]
  refine ⟨41828071124263607620157123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27885380749509071746771415 41828071124263607620157123)
  ·
    refine ⟨62742106686395411430235685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41828071124263607620157123 62742106686395411430235685)
    ·
      refine ⟨11764145003699139643169191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62742106686395411430235685 11764145003699139643169191)
      ·
        refine ⟨17646217505548709464753787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764145003699139643169191 17646217505548709464753787)
        ·
          refine ⟨26469326258323064197130681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17646217505548709464753787 26469326258323064197130681)
          ·
            refine ⟨19851994693742298147848011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26469326258323064197130681 19851994693742298147848011)
            ·
              refine ⟨29777992040613447221772017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19851994693742298147848011 29777992040613447221772017)
              ·
                refine ⟨22333494030460085416329013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29777992040613447221772017 22333494030460085416329013)
                ·
                  refine ⟨2093765065355633007780845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22333494030460085416329013 2093765065355633007780845)
                  ·
                    refine ⟨785161899508362377917817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2093765065355633007780845 785161899508362377917817)
                    ·
                      refine ⟨588871424631271783438363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785161899508362377917817 588871424631271783438363)
                      ·
                        rfl

theorem cell23_1146823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_1146823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146823 prefixEnd_1146823 := by exact prefixLift 1146823
  have htrace : WordTrace (prefixWord ++ tailWord_1146823) baseStart_1146823 baseEnd_1146823 := by
    simpa [prefixWord, tailWord_1146823, baseEnd_1146823] using wordTrace_append hprefix tailTrace_1146823
  have hstable : (prefixWord ++ tailWord_1146823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146823).length < 2 ^ (prefixWord ++ tailWord_1146823).sum := by decide
  have hdescent : baseEnd_1146823 < baseStart_1146823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146830 : List Nat := [4, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_1146830 : Nat := 118140960795 + 1146830 * 2 ^ 59
def prefixEnd_1146830 : Nat := 4983230072969 + 3 ^ 40 * 1146830 * 2
def baseEnd_1146830 : Nat := 588875018995853256050831

theorem tailTrace_1146830 : CollatzResearch.WordTrace tailWord_1146830 prefixEnd_1146830 588875018995853256050831 := by
  unfold tailWord_1146830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228540804404780976957743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27885550956825498543774629 5228540804404780976957743)
  ·
    refine ⟨7842811206607171465436615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5228540804404780976957743 7842811206607171465436615)
    ·
      refine ⟨11764216809910757198154923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7842811206607171465436615 11764216809910757198154923)
      ·
        refine ⟨17646325214866135797232385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764216809910757198154923 17646325214866135797232385)
        ·
          refine ⟨13234743911149601847924289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17646325214866135797232385 13234743911149601847924289)
          ·
            refine ⟨9926057933362201385943217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13234743911149601847924289 9926057933362201385943217)
            ·
              refine ⟨7444543450021651039457413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9926057933362201385943217 7444543450021651039457413)
              ·
                refine ⟨1395851896879059569898265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7444543450021651039457413 1395851896879059569898265)
                ·
                  refine ⟨1046888922659294677423699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1395851896879059569898265 1046888922659294677423699)
                  ·
                    refine ⟨1570333383988942016135549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1046888922659294677423699 1570333383988942016135549)
                    ·
                      refine ⟨588875018995853256050831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1570333383988942016135549 588875018995853256050831)
                      ·
                        rfl

theorem cell23_1146830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_1146830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146830 prefixEnd_1146830 := by exact prefixLift 1146830
  have htrace : WordTrace (prefixWord ++ tailWord_1146830) baseStart_1146830 baseEnd_1146830 := by
    simpa [prefixWord, tailWord_1146830, baseEnd_1146830] using wordTrace_append hprefix tailTrace_1146830
  have hstable : (prefixWord ++ tailWord_1146830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146830).length < 2 ^ (prefixWord ++ tailWord_1146830).sum := by decide
  have hdescent : baseEnd_1146830 < baseStart_1146830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146847 : List Nat := [1, 1, 2, 3, 4, 1, 4, 1, 2, 1, 3]
def baseStart_1146847 : Nat := 118140960795 + 1146847 * 2 ^ 59
def prefixEnd_1146847 : Nat := 4983230072969 + 3 ^ 40 * 1146847 * 2
def baseEnd_1146847 : Nat := 588883748166979689538253

theorem tailTrace_1146847 : CollatzResearch.WordTrace tailWord_1146847 prefixEnd_1146847 588883748166979689538253 := by
  unfold tailWord_1146847
  simp only [CollatzResearch.WordTrace]
  refine ⟨41828946476176659719030795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27885964317451106479353863 41828946476176659719030795)
  ·
    refine ⟨62743419714264989578546193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41828946476176659719030795 62743419714264989578546193)
    ·
      refine ⟨47057564785698742183909645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62743419714264989578546193 47057564785698742183909645)
      ·
        refine ⟨17646586794637028318966117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47057564785698742183909645 17646586794637028318966117)
        ·
          refine ⟨3308735023994442809806147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17646586794637028318966117 3308735023994442809806147)
          ·
            refine ⟨4963102535991664214709221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308735023994442809806147 4963102535991664214709221)
            ·
              refine ⟨930581725498437040257979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4963102535991664214709221 930581725498437040257979)
              ·
                refine ⟨1395872588247655560386969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930581725498437040257979 1395872588247655560386969)
                ·
                  refine ⟨1046904441185741670290227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1395872588247655560386969 1046904441185741670290227)
                  ·
                    refine ⟨1570356661778612505435341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1046904441185741670290227 1570356661778612505435341)
                    ·
                      refine ⟨588883748166979689538253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1570356661778612505435341 588883748166979689538253)
                      ·
                        rfl

theorem cell23_1146847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_1146847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146847 prefixEnd_1146847 := by exact prefixLift 1146847
  have htrace : WordTrace (prefixWord ++ tailWord_1146847) baseStart_1146847 baseEnd_1146847 := by
    simpa [prefixWord, tailWord_1146847, baseEnd_1146847] using wordTrace_append hprefix tailTrace_1146847
  have hstable : (prefixWord ++ tailWord_1146847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146847).length < 2 ^ (prefixWord ++ tailWord_1146847).sum := by decide
  have hdescent : baseEnd_1146847 < baseStart_1146847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146887 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_1146887 : Nat := 118140960795 + 1146887 * 2 ^ 59
def prefixEnd_1146887 : Nat := 4983230072969 + 3 ^ 40 * 1146887 * 2
def baseEnd_1146887 : Nat := 588904287393159533038069

theorem tailTrace_1146887 : CollatzResearch.WordTrace tailWord_1146887 prefixEnd_1146887 588904287393159533038069 := by
  unfold tailWord_1146887
  simp only [CollatzResearch.WordTrace]
  refine ⟨41830405396031746550486915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27886936930687831033657943 41830405396031746550486915)
  ·
    refine ⟨62745608094047619825730373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41830405396031746550486915 62745608094047619825730373)
    ·
      refine ⟨11764801517633928717324445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62745608094047619825730373 11764801517633928717324445)
      ·
        refine ⟨4411800569112723268996667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11764801517633928717324445 4411800569112723268996667)
        ·
          refine ⟨6617700853669084903495001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4411800569112723268996667 6617700853669084903495001)
          ·
            refine ⟨4963275640251813677621251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6617700853669084903495001 4963275640251813677621251)
            ·
              refine ⟨7444913460377720516431877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4963275640251813677621251 7444913460377720516431877)
              ·
                refine ⟨1395921273820822596830977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7444913460377720516431877 1395921273820822596830977)
                ·
                  refine ⟨1046940955365616947623233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1395921273820822596830977 1046940955365616947623233)
                  ·
                    refine ⟨785205716524212710717425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1046940955365616947623233 785205716524212710717425)
                    ·
                      refine ⟨588904287393159533038069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785205716524212710717425 588904287393159533038069)
                      ·
                        rfl

theorem cell23_1146887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_1146887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146887 prefixEnd_1146887 := by exact prefixLift 1146887
  have htrace : WordTrace (prefixWord ++ tailWord_1146887) baseStart_1146887 baseEnd_1146887 := by
    simpa [prefixWord, tailWord_1146887, baseEnd_1146887] using wordTrace_append hprefix tailTrace_1146887
  have hstable : (prefixWord ++ tailWord_1146887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146887).length < 2 ^ (prefixWord ++ tailWord_1146887).sum := by decide
  have hdescent : baseEnd_1146887 < baseStart_1146887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146943 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_1146943 : Nat := 118140960795 + 1146943 * 2 ^ 59
def prefixEnd_1146943 : Nat := 4983230072969 + 3 ^ 40 * 1146943 * 2
def baseEnd_1146943 : Nat := 588933042309811313937811

theorem tailTrace_1146943 : CollatzResearch.WordTrace tailWord_1146943 prefixEnd_1146943 588933042309811313937811 := by
  unfold tailWord_1146943
  simp only [CollatzResearch.WordTrace]
  refine ⟨41832447883828868114525483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27888298589219245409683655 41832447883828868114525483)
  ·
    refine ⟨62748671825743302171788225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41832447883828868114525483 62748671825743302171788225)
    ·
      refine ⟨47061503869307476628841169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62748671825743302171788225 47061503869307476628841169)
      ·
        refine ⟨35296127901980607471630877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47061503869307476628841169 35296127901980607471630877)
        ·
          refine ⟨13236047963242727801861579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35296127901980607471630877 13236047963242727801861579)
          ·
            refine ⟨19854071944864091702792369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13236047963242727801861579 19854071944864091702792369)
            ·
              refine ⟨14890553958648068777094277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19854071944864091702792369 14890553958648068777094277)
              ·
                refine ⟨2791978867246512895705177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14890553958648068777094277 2791978867246512895705177)
                ·
                  refine ⟨2093984150434884671778883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2791978867246512895705177 2093984150434884671778883)
                  ·
                    refine ⟨3140976225652327007668325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2093984150434884671778883 3140976225652327007668325)
                    ·
                      refine ⟨588933042309811313937811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3140976225652327007668325 588933042309811313937811)
                      ·
                        rfl

theorem cell23_1146943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_1146943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146943 prefixEnd_1146943 := by exact prefixLift 1146943
  have htrace : WordTrace (prefixWord ++ tailWord_1146943) baseStart_1146943 baseEnd_1146943 := by
    simpa [prefixWord, tailWord_1146943, baseEnd_1146943] using wordTrace_append hprefix tailTrace_1146943
  have hstable : (prefixWord ++ tailWord_1146943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146943).length < 2 ^ (prefixWord ++ tailWord_1146943).sum := by decide
  have hdescent : baseEnd_1146943 < baseStart_1146943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1146950 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1146950 : Nat := 118140960795 + 1146950 * 2 ^ 59
def prefixEnd_1146950 : Nat := 4983230072969 + 3 ^ 40 * 1146950 * 2
def baseEnd_1146950 : Nat := 588936636674392786550279

theorem tailTrace_1146950 : CollatzResearch.WordTrace tailWord_1146950 prefixEnd_1146950 588936636674392786550279 := by
  unfold tailWord_1146950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1307271974837609634688447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27888468796535672206686869 1307271974837609634688447)
  ·
    refine ⟨1960907962256414452032671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1307271974837609634688447 1960907962256414452032671)
    ·
      refine ⟨2941361943384621678049007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1960907962256414452032671 2941361943384621678049007)
      ·
        refine ⟨4412042915076932517073511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2941361943384621678049007 4412042915076932517073511)
        ·
          refine ⟨6618064372615398775610267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412042915076932517073511 6618064372615398775610267)
          ·
            refine ⟨9927096558923098163415401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618064372615398775610267 9927096558923098163415401)
            ·
              refine ⟨7445322419192323622561551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9927096558923098163415401 7445322419192323622561551)
              ·
                refine ⟨11167983628788485433842327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7445322419192323622561551 11167983628788485433842327)
                ·
                  refine ⟨16751975443182728150763491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11167983628788485433842327 16751975443182728150763491)
                  ·
                    refine ⟨25127963164774092226145237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16751975443182728150763491 25127963164774092226145237)
                    ·
                      refine ⟨588936636674392786550279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25127963164774092226145237 588936636674392786550279)
                      ·
                        rfl

theorem cell23_1146950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1146950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1146950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1146950 prefixEnd_1146950 := by exact prefixLift 1146950
  have htrace : WordTrace (prefixWord ++ tailWord_1146950) baseStart_1146950 baseEnd_1146950 := by
    simpa [prefixWord, tailWord_1146950, baseEnd_1146950] using wordTrace_append hprefix tailTrace_1146950
  have hstable : (prefixWord ++ tailWord_1146950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1146950).length < 2 ^ (prefixWord ++ tailWord_1146950).sum := by decide
  have hdescent : baseEnd_1146950 < baseStart_1146950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1146950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147004 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_1147004 : Nat := 118140960795 + 1147004 * 2 ^ 59
def prefixEnd_1147004 : Nat := 4983230072969 + 3 ^ 40 * 1147004 * 2
def baseEnd_1147004 : Nat := 196321454876578525091677

theorem tailTrace_1147004 : CollatzResearch.WordTrace tailWord_1147004 prefixEnd_1147004 196321454876578525091677 := by
  unfold tailWord_1147004
  simp only [CollatzResearch.WordTrace]
  refine ⟨20917336368303937766248033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27889781824405250354997377 20917336368303937766248033)
  ·
    refine ⟨15688002276227953324686025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20917336368303937766248033 15688002276227953324686025)
    ·
      refine ⟨11766001707170964993514519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15688002276227953324686025 11766001707170964993514519)
      ·
        refine ⟨17649002560756447490271779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766001707170964993514519 17649002560756447490271779)
        ·
          refine ⟨26473503841134671235407669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17649002560756447490271779 26473503841134671235407669)
          ·
            refine ⟨2481890985106375428319469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26473503841134671235407669 2481890985106375428319469)
            ·
              refine ⟨930709119414890785619801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2481890985106375428319469 930709119414890785619801)
              ·
                refine ⟨698031839561168089214851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 930709119414890785619801 698031839561168089214851)
                ·
                  refine ⟨1047047759341752133822277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698031839561168089214851 1047047759341752133822277)
                  ·
                    refine ⟨196321454876578525091677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047047759341752133822277 196321454876578525091677)
                    ·
                      rfl

theorem cell23_1147004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_1147004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147004 prefixEnd_1147004 := by exact prefixLift 1147004
  have htrace : WordTrace (prefixWord ++ tailWord_1147004) baseStart_1147004 baseEnd_1147004 := by
    simpa [prefixWord, tailWord_1147004, baseEnd_1147004] using wordTrace_append hprefix tailTrace_1147004
  have hstable : (prefixWord ++ tailWord_1147004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147004).length < 2 ^ (prefixWord ++ tailWord_1147004).sum := by decide
  have hdescent : baseEnd_1147004 < baseStart_1147004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147037 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_1147037 : Nat := 118140960795 + 1147037 * 2 ^ 59
def prefixEnd_1147037 : Nat := 4983230072969 + 3 ^ 40 * 1147037 * 2
def baseEnd_1147037 : Nat := 588981309491333946162379

theorem tailTrace_1147037 : CollatzResearch.WordTrace tailWord_1147037 prefixEnd_1147037 588981309491333946162379 := by
  unfold tailWord_1147037
  simp only [CollatzResearch.WordTrace]
  refine ⟨41835876345488322168447365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27890584230325548112298243 41835876345488322168447365)
  ·
    refine ⟨7844226814779060406583881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41835876345488322168447365 7844226814779060406583881)
    ·
      refine ⟨5883170111084295304937911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7844226814779060406583881 5883170111084295304937911)
      ·
        refine ⟨8824755166626442957406867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883170111084295304937911 8824755166626442957406867)
        ·
          refine ⟨13237132749939664436110301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824755166626442957406867 13237132749939664436110301)
          ·
            refine ⟨4963924781227374163541363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13237132749939664436110301 4963924781227374163541363)
            ·
              refine ⟨7445887171841061245312045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4963924781227374163541363 7445887171841061245312045)
              ·
                refine ⟨2792207689440397966992017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7445887171841061245312045 2792207689440397966992017)
                ·
                  refine ⟨2094155767080298475244013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2792207689440397966992017 2094155767080298475244013)
                  ·
                    refine ⟨785308412655111928216505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2094155767080298475244013 785308412655111928216505)
                    ·
                      refine ⟨588981309491333946162379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785308412655111928216505 588981309491333946162379)
                      ·
                        rfl

theorem cell23_1147037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_1147037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147037 prefixEnd_1147037 := by exact prefixLift 1147037
  have htrace : WordTrace (prefixWord ++ tailWord_1147037) baseStart_1147037 baseEnd_1147037 := by
    simpa [prefixWord, tailWord_1147037, baseEnd_1147037] using wordTrace_append hprefix tailTrace_1147037
  have hstable : (prefixWord ++ tailWord_1147037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147037).length < 2 ^ (prefixWord ++ tailWord_1147037).sum := by decide
  have hdescent : baseEnd_1147037 < baseStart_1147037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147067 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 3, 2, 2]
def baseStart_1147067 : Nat := 118140960795 + 1147067 * 2 ^ 59
def prefixEnd_1147067 : Nat := 4983230072969 + 3 ^ 40 * 1147067 * 2
def baseEnd_1147067 : Nat := 588996713910968828787241

theorem tailTrace_1147067 : CollatzResearch.WordTrace tailWord_1147067 prefixEnd_1147067 588996713910968828787241 := by
  unfold tailWord_1147067
  simp only [CollatzResearch.WordTrace]
  refine ⟨41836970535379637292039455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27891313690253091528026303 41836970535379637292039455)
  ·
    refine ⟨62755455803069455938059183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41836970535379637292039455 62755455803069455938059183)
    ·
      refine ⟨94133183704604183907088775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62755455803069455938059183 94133183704604183907088775)
      ·
        refine ⟨141199775556906275860633163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94133183704604183907088775 141199775556906275860633163)
        ·
          refine ⟨211799663335359413790949745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141199775556906275860633163 211799663335359413790949745)
          ·
            refine ⟨158849747501519560343212309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211799663335359413790949745 158849747501519560343212309)
            ·
              refine ⟨7446081914133729391088077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158849747501519560343212309 7446081914133729391088077)
              ·
                refine ⟨2792280717800148521658029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7446081914133729391088077 2792280717800148521658029)
                ·
                  refine ⟨1047105269175055695621761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2792280717800148521658029 1047105269175055695621761)
                  ·
                    refine ⟨785328951881291771716321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1047105269175055695621761 785328951881291771716321)
                    ·
                      refine ⟨588996713910968828787241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785328951881291771716321 588996713910968828787241)
                      ·
                        rfl

theorem cell23_1147067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 3, 2, 2].length) (baseStart_1147067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147067 prefixEnd_1147067 := by exact prefixLift 1147067
  have htrace : WordTrace (prefixWord ++ tailWord_1147067) baseStart_1147067 baseEnd_1147067 := by
    simpa [prefixWord, tailWord_1147067, baseEnd_1147067] using wordTrace_append hprefix tailTrace_1147067
  have hstable : (prefixWord ++ tailWord_1147067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147067).length < 2 ^ (prefixWord ++ tailWord_1147067).sum := by decide
  have hdescent : baseEnd_1147067 < baseStart_1147067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147101 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1147101 : Nat := 118140960795 + 1147101 * 2 ^ 59
def prefixEnd_1147101 : Nat := 4983230072969 + 3 ^ 40 * 1147101 * 2
def baseEnd_1147101 : Nat := 589014172253221695762085

theorem tailTrace_1147101 : CollatzResearch.WordTrace tailWord_1147101 prefixEnd_1147101 589014172253221695762085 := by
  unfold tailWord_1147101
  simp only [CollatzResearch.WordTrace]
  refine ⟨41838210617256461098777157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27892140411504307399184771 41838210617256461098777157)
  ·
    refine ⟨7844664490735586456020717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41838210617256461098777157 7844664490735586456020717)
    ·
      refine ⟨2941749184025844921007769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7844664490735586456020717 2941749184025844921007769)
      ·
        refine ⟨2206311888019383690755827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2941749184025844921007769 2206311888019383690755827)
        ·
          refine ⟨3309467832029075536133741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206311888019383690755827 3309467832029075536133741)
          ·
            refine ⟨1241050437010903326050153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3309467832029075536133741 1241050437010903326050153)
            ·
              refine ⟨930787827758177494537615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1241050437010903326050153 930787827758177494537615)
              ·
                refine ⟨1396181741637266241806423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 930787827758177494537615 1396181741637266241806423)
                ·
                  refine ⟨2094272612455899362709635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396181741637266241806423 2094272612455899362709635)
                  ·
                    refine ⟨3141408918683849044064453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094272612455899362709635 3141408918683849044064453)
                    ·
                      refine ⟨589014172253221695762085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3141408918683849044064453 589014172253221695762085)
                      ·
                        rfl

theorem cell23_1147101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1147101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147101 prefixEnd_1147101 := by exact prefixLift 1147101
  have htrace : WordTrace (prefixWord ++ tailWord_1147101) baseStart_1147101 baseEnd_1147101 := by
    simpa [prefixWord, tailWord_1147101, baseEnd_1147101] using wordTrace_append hprefix tailTrace_1147101
  have hstable : (prefixWord ++ tailWord_1147101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147101).length < 2 ^ (prefixWord ++ tailWord_1147101).sum := by decide
  have hdescent : baseEnd_1147101 < baseStart_1147101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147113 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 5]
def baseStart_1147113 : Nat := 118140960795 + 1147113 * 2 ^ 59
def prefixEnd_1147113 : Nat := 4983230072969 + 3 ^ 40 * 1147113 * 2
def baseEnd_1147113 : Nat := 589020334021075648812029

theorem tailTrace_1147113 : CollatzResearch.WordTrace tailWord_1147113 prefixEnd_1147113 589020334021075648812029 := by
  unfold tailWord_1147113
  simp only [CollatzResearch.WordTrace]
  refine ⟨41838648293212987148213993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27892432195475324765475995 41838648293212987148213993)
  ·
    refine ⟨31378986219909740361160495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41838648293212987148213993 31378986219909740361160495)
    ·
      refine ⟨47068479329864610541740743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31378986219909740361160495 47068479329864610541740743)
      ·
        refine ⟨70602718994796915812611115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47068479329864610541740743 70602718994796915812611115)
        ·
          refine ⟨105904078492195373718916673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70602718994796915812611115 105904078492195373718916673)
          ·
            refine ⟨79428058869146530289187505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105904078492195373718916673 79428058869146530289187505)
            ·
              refine ⟨59571044151859897716890629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79428058869146530289187505 59571044151859897716890629)
              ·
                refine ⟨11169570778473730821916993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59571044151859897716890629 11169570778473730821916993)
                ·
                  refine ⟨8377178083855298116437745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11169570778473730821916993 8377178083855298116437745)
                  ·
                    refine ⟨6282883562891473587328309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8377178083855298116437745 6282883562891473587328309)
                    ·
                      refine ⟨589020334021075648812029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6282883562891473587328309 589020334021075648812029)
                      ·
                        rfl

theorem cell23_1147113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_1147113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147113 prefixEnd_1147113 := by exact prefixLift 1147113
  have htrace : WordTrace (prefixWord ++ tailWord_1147113) baseStart_1147113 baseEnd_1147113 := by
    simpa [prefixWord, tailWord_1147113, baseEnd_1147113] using wordTrace_append hprefix tailTrace_1147113
  have hstable : (prefixWord ++ tailWord_1147113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147113).length < 2 ^ (prefixWord ++ tailWord_1147113).sum := by decide
  have hdescent : baseEnd_1147113 < baseStart_1147113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147144 : List Nat := [2, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_1147144 : Nat := 118140960795 + 1147144 * 2 ^ 59
def prefixEnd_1147144 : Nat := 4983230072969 + 3 ^ 40 * 1147144 * 2
def baseEnd_1147144 : Nat := 589036251921365027524387

theorem tailTrace_1147144 : CollatzResearch.WordTrace tailWord_1147144 prefixEnd_1147144 589036251921365027524387 := by
  unfold tailWord_1147144
  simp only [CollatzResearch.WordTrace]
  refine ⟨20919889478050339721296243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27893185970733786295061657 20919889478050339721296243)
  ·
    refine ⟨31379834217075509581944365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20919889478050339721296243 31379834217075509581944365)
    ·
      refine ⟨11767437831403316093229137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31379834217075509581944365 11767437831403316093229137)
      ·
        refine ⟨8825578373552487069921853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11767437831403316093229137 8825578373552487069921853)
        ·
          refine ⟨3309591890082182651220695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8825578373552487069921853 3309591890082182651220695)
          ·
            refine ⟨4964387835123273976831043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3309591890082182651220695 4964387835123273976831043)
            ·
              refine ⟨7446581752684910965246565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964387835123273976831043 7446581752684910965246565)
              ·
                refine ⟨1396234078628420805983731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7446581752684910965246565 1396234078628420805983731)
                ·
                  refine ⟨2094351117942631208975597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396234078628420805983731 2094351117942631208975597)
                  ·
                    refine ⟨785381669228486703365849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2094351117942631208975597 785381669228486703365849)
                    ·
                      refine ⟨589036251921365027524387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785381669228486703365849 589036251921365027524387)
                      ·
                        rfl

theorem cell23_1147144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_1147144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147144 prefixEnd_1147144 := by exact prefixLift 1147144
  have htrace : WordTrace (prefixWord ++ tailWord_1147144) baseStart_1147144 baseEnd_1147144 := by
    simpa [prefixWord, tailWord_1147144, baseEnd_1147144] using wordTrace_append hprefix tailTrace_1147144
  have hstable : (prefixWord ++ tailWord_1147144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147144).length < 2 ^ (prefixWord ++ tailWord_1147144).sum := by decide
  have hdescent : baseEnd_1147144 < baseStart_1147144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147157 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_1147157 : Nat := 118140960795 + 1147157 * 2 ^ 59
def prefixEnd_1147157 : Nat := 4983230072969 + 3 ^ 40 * 1147157 * 2
def baseEnd_1147157 : Nat := 589042927169873476661827

theorem tailTrace_1147157 : CollatzResearch.WordTrace tailWord_1147157 prefixEnd_1147157 589042927169873476661827 := by
  unfold tailWord_1147157
  simp only [CollatzResearch.WordTrace]
  refine ⟨41840253105053582662815725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27893502070035721775210483 41840253105053582662815725)
  ·
    refine ⟨15690094914395093498555897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41840253105053582662815725 15690094914395093498555897)
    ·
      refine ⟨11767571185796320123916923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15690094914395093498555897 11767571185796320123916923)
      ·
        refine ⟨17651356778694480185875385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11767571185796320123916923 17651356778694480185875385)
        ·
          refine ⟨13238517584020860139406539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17651356778694480185875385 13238517584020860139406539)
          ·
            refine ⟨19857776376031290209109809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13238517584020860139406539 19857776376031290209109809)
            ·
              refine ⟨14893332282023467656832357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19857776376031290209109809 14893332282023467656832357)
              ·
                refine ⟨2792499802879400185656067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14893332282023467656832357 2792499802879400185656067)
                ·
                  refine ⟨4188749704319100278484101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792499802879400185656067 4188749704319100278484101)
                  ·
                    refine ⟨785390569559831302215769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4188749704319100278484101 785390569559831302215769)
                    ·
                      refine ⟨589042927169873476661827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785390569559831302215769 589042927169873476661827)
                      ·
                        rfl

theorem cell23_1147157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_1147157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147157 prefixEnd_1147157 := by exact prefixLift 1147157
  have htrace : WordTrace (prefixWord ++ tailWord_1147157) baseStart_1147157 baseEnd_1147157 := by
    simpa [prefixWord, tailWord_1147157, baseEnd_1147157] using wordTrace_append hprefix tailTrace_1147157
  have hstable : (prefixWord ++ tailWord_1147157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147157).length < 2 ^ (prefixWord ++ tailWord_1147157).sum := by decide
  have hdescent : baseEnd_1147157 < baseStart_1147157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147160 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_1147160 : Nat := 118140960795 + 1147160 * 2 ^ 59
def prefixEnd_1147160 : Nat := 4983230072969 + 3 ^ 40 * 1147160 * 2
def baseEnd_1147160 : Nat := 589044467611836964924313

theorem tailTrace_1147160 : CollatzResearch.WordTrace tailWord_1147160 prefixEnd_1147160 589044467611836964924313 := by
  unfold tailWord_1147160
  simp only [CollatzResearch.WordTrace]
  refine ⟨20920181262021357087587467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27893575016028476116783289 20920181262021357087587467)
  ·
    refine ⟨31380271893032035631381201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20920181262021357087587467 31380271893032035631381201)
    ·
      refine ⟨23535203919774026723535901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31380271893032035631381201 23535203919774026723535901)
      ·
        refine ⟨8825701469915260021325963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23535203919774026723535901 8825701469915260021325963)
        ·
          refine ⟨13238552204872890031988945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8825701469915260021325963 13238552204872890031988945)
          ·
            refine ⟨9928914153654667523991709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13238552204872890031988945 9928914153654667523991709)
            ·
              refine ⟨3723342807620500321496891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9928914153654667523991709 3723342807620500321496891)
              ·
                refine ⟨5585014211430750482245337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723342807620500321496891 5585014211430750482245337)
                ·
                  refine ⟨4188760658573062861684003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585014211430750482245337 4188760658573062861684003)
                  ·
                    refine ⟨6283140987859594292526005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188760658573062861684003 6283140987859594292526005)
                    ·
                      refine ⟨589044467611836964924313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6283140987859594292526005 589044467611836964924313)
                      ·
                        rfl

theorem cell23_1147160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_1147160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147160 prefixEnd_1147160 := by exact prefixLift 1147160
  have htrace : WordTrace (prefixWord ++ tailWord_1147160) baseStart_1147160 baseEnd_1147160 := by
    simpa [prefixWord, tailWord_1147160, baseEnd_1147160] using wordTrace_append hprefix tailTrace_1147160
  have hstable : (prefixWord ++ tailWord_1147160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147160).length < 2 ^ (prefixWord ++ tailWord_1147160).sum := by decide
  have hdescent : baseEnd_1147160 < baseStart_1147160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147163 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 9]
def baseStart_1147163 : Nat := 118140960795 + 1147163 * 2 ^ 59
def prefixEnd_1147163 : Nat := 4983230072969 + 3 ^ 40 * 1147163 * 2
def baseEnd_1147163 : Nat := 65449556450422272576311

theorem tailTrace_1147163 : CollatzResearch.WordTrace tailWord_1147163 prefixEnd_1147163 65449556450422272576311 := by
  unfold tailWord_1147163
  simp only [CollatzResearch.WordTrace]
  refine ⟨41840471943031845687534143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27893647962021230458356095 41840471943031845687534143)
  ·
    refine ⟨62760707914547768531301215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41840471943031845687534143 62760707914547768531301215)
    ·
      refine ⟨94141061871821652796951823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62760707914547768531301215 94141061871821652796951823)
      ·
        refine ⟨141211592807732479195427735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94141061871821652796951823 141211592807732479195427735)
        ·
          refine ⟨211817389211598718793141603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141211592807732479195427735 211817389211598718793141603)
          ·
            refine ⟨317726083817398078189712405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211817389211598718793141603 317726083817398078189712405)
            ·
              refine ⟨14893410178940534915142769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 317726083817398078189712405 14893410178940534915142769)
              ·
                refine ⟨11170057634205401186357077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14893410178940534915142769 11170057634205401186357077)
                ·
                  refine ⟨65449556450422272576311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 11170057634205401186357077 65449556450422272576311)
                  ·
                    rfl

theorem cell23_1147163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 9].length) (baseStart_1147163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147163 prefixEnd_1147163 := by exact prefixLift 1147163
  have htrace : WordTrace (prefixWord ++ tailWord_1147163) baseStart_1147163 baseEnd_1147163 := by
    simpa [prefixWord, tailWord_1147163, baseEnd_1147163] using wordTrace_append hprefix tailTrace_1147163
  have hstable : (prefixWord ++ tailWord_1147163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147163).length < 2 ^ (prefixWord ++ tailWord_1147163).sum := by decide
  have hdescent : baseEnd_1147163 < baseStart_1147163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147180 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 7]
def baseStart_1147180 : Nat := 118140960795 + 1147180 * 2 ^ 59
def prefixEnd_1147180 : Nat := 4983230072969 + 3 ^ 40 * 1147180 * 2
def baseEnd_1147180 : Nat := 65450526358325209630469

theorem tailTrace_1147180 : CollatzResearch.WordTrace tailWord_1147180 prefixEnd_1147180 65450526358325209630469 := by
  unfold tailWord_1147180
  simp only [CollatzResearch.WordTrace]
  refine ⟨20920545991985128795451497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27894061322646838393935329 20920545991985128795451497)
  ·
    refine ⟨15690409493988846596588623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20920545991985128795451497 15690409493988846596588623)
    ·
      refine ⟨23535614240983269894882935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15690409493988846596588623 23535614240983269894882935)
      ·
        refine ⟨35303421361474904842324403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23535614240983269894882935 35303421361474904842324403)
        ·
          refine ⟨52955132042212357263486605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35303421361474904842324403 52955132042212357263486605)
          ·
            refine ⟨19858174515829633973807477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52955132042212357263486605 19858174515829633973807477)
            ·
              refine ⟨1861703860859028185044451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19858174515829633973807477 1861703860859028185044451)
              ·
                refine ⟨2792555791288542277566677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861703860859028185044451 2792555791288542277566677)
                ·
                  refine ⟨65450526358325209630469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2792555791288542277566677 65450526358325209630469)
                  ·
                    rfl

theorem cell23_1147180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_1147180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147180 prefixEnd_1147180 := by exact prefixLift 1147180
  have htrace : WordTrace (prefixWord ++ tailWord_1147180) baseStart_1147180 baseEnd_1147180 := by
    simpa [prefixWord, tailWord_1147180, baseEnd_1147180] using wordTrace_append hprefix tailTrace_1147180
  have hstable : (prefixWord ++ tailWord_1147180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147180).length < 2 ^ (prefixWord ++ tailWord_1147180).sum := by decide
  have hdescent : baseEnd_1147180 < baseStart_1147180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147234 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 2, 5, 2]
def baseStart_1147234 : Nat := 118140960795 + 1147234 * 2 ^ 59
def prefixEnd_1147234 : Nat := 4983230072969 + 3 ^ 40 * 1147234 * 2
def baseEnd_1147234 : Nat := 589082465180269675398973

theorem tailTrace_1147234 : CollatzResearch.WordTrace tailWord_1147234 prefixEnd_1147234 589082465180269675398973 := by
  unfold tailWord_1147234
  simp only [CollatzResearch.WordTrace]
  refine ⟨10460765381443656203342189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27895374350516416542245837 10460765381443656203342189)
  ·
    refine ⟨3922787018041371076253321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10460765381443656203342189 3922787018041371076253321)
    ·
      refine ⟨2942090263531028307189991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3922787018041371076253321 2942090263531028307189991)
      ·
        refine ⟨4413135395296542460784987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2942090263531028307189991 4413135395296542460784987)
        ·
          refine ⟨6619703092944813691177481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413135395296542460784987 6619703092944813691177481)
          ·
            refine ⟨4964777319708610268383111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6619703092944813691177481 4964777319708610268383111)
            ·
              refine ⟨7447165979562915402574667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964777319708610268383111 7447165979562915402574667)
              ·
                refine ⟨11170748969344373103862001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7447165979562915402574667 11170748969344373103862001)
                ·
                  refine ⟨8378061727008279827896501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11170748969344373103862001 8378061727008279827896501)
                  ·
                    refine ⟨785443286907026233865297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8378061727008279827896501 785443286907026233865297)
                    ·
                      refine ⟨589082465180269675398973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785443286907026233865297 589082465180269675398973)
                      ·
                        rfl

theorem cell23_1147234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_1147234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147234 prefixEnd_1147234 := by exact prefixLift 1147234
  have htrace : WordTrace (prefixWord ++ tailWord_1147234) baseStart_1147234 baseEnd_1147234 := by
    simpa [prefixWord, tailWord_1147234, baseEnd_1147234] using wordTrace_append hprefix tailTrace_1147234
  have hstable : (prefixWord ++ tailWord_1147234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147234).length < 2 ^ (prefixWord ++ tailWord_1147234).sum := by decide
  have hdescent : baseEnd_1147234 < baseStart_1147234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147260 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_1147260 : Nat := 118140960795 + 1147260 * 2 ^ 59
def prefixEnd_1147260 : Nat := 4983230072969 + 3 ^ 40 * 1147260 * 2
def baseEnd_1147260 : Nat := 589095815677286573673853

theorem tailTrace_1147260 : CollatzResearch.WordTrace tailWord_1147260 prefixEnd_1147260 589095815677286573673853 := by
  unfold tailWord_1147260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20922004911840215626907617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27896006549120287502543489 20922004911840215626907617)
  ·
    refine ⟨15691503683880161720180713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20922004911840215626907617 15691503683880161720180713)
    ·
      refine ⟨11768627762910121290135535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15691503683880161720180713 11768627762910121290135535)
      ·
        refine ⟨17652941644365181935203303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11768627762910121290135535 17652941644365181935203303)
        ·
          refine ⟨26479412466547772902804955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17652941644365181935203303 26479412466547772902804955)
          ·
            refine ⟨39719118699821659354207433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26479412466547772902804955 39719118699821659354207433)
            ·
              refine ⟨29789339024866244515655575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39719118699821659354207433 29789339024866244515655575)
              ·
                refine ⟨44684008537299366773483363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29789339024866244515655575 44684008537299366773483363)
                ·
                  refine ⟨67026012805949050160225045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44684008537299366773483363 67026012805949050160225045)
                  ·
                    refine ⟨3141844350278861726260549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67026012805949050160225045 3141844350278861726260549)
                    ·
                      refine ⟨589095815677286573673853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3141844350278861726260549 589095815677286573673853)
                      ·
                        rfl

theorem cell23_1147260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_1147260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147260 prefixEnd_1147260 := by exact prefixLift 1147260
  have htrace : WordTrace (prefixWord ++ tailWord_1147260) baseStart_1147260 baseEnd_1147260 := by
    simpa [prefixWord, tailWord_1147260, baseEnd_1147260] using wordTrace_append hprefix tailTrace_1147260
  have hstable : (prefixWord ++ tailWord_1147260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147260).length < 2 ^ (prefixWord ++ tailWord_1147260).sum := by decide
  have hdescent : baseEnd_1147260 < baseStart_1147260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147287 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 6]
def baseStart_1147287 : Nat := 118140960795 + 1147287 * 2 ^ 59
def prefixEnd_1147287 : Nat := 4983230072969 + 3 ^ 40 * 1147287 * 2
def baseEnd_1147287 : Nat := 65456631072773107559581

theorem tailTrace_1147287 : CollatzResearch.WordTrace tailWord_1147287 prefixEnd_1147287 65456631072773107559581 := by
  unfold tailWord_1147287
  simp only [CollatzResearch.WordTrace]
  refine ⟨41844994594582614865048115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27896663063055076576698743 41844994594582614865048115)
  ·
    refine ⟨62767491891873922297572173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41844994594582614865048115 62767491891873922297572173)
    ·
      refine ⟨23537809459452720861589565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62767491891873922297572173 23537809459452720861589565)
      ·
        refine ⟨8826678547294770323096087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23537809459452720861589565 8826678547294770323096087)
        ·
          refine ⟨13240017820942155484644131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826678547294770323096087 13240017820942155484644131)
          ·
            refine ⟨19860026731413233226966197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13240017820942155484644131 19860026731413233226966197)
            ·
              refine ⟨1861877506069990615028081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19860026731413233226966197 1861877506069990615028081)
              ·
                refine ⟨1396408129552492961271061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861877506069990615028081 1396408129552492961271061)
                ·
                  refine ⟨65456631072773107559581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1396408129552492961271061 65456631072773107559581)
                  ·
                    rfl

theorem cell23_1147287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 6].length) (baseStart_1147287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147287 prefixEnd_1147287 := by exact prefixLift 1147287
  have htrace : WordTrace (prefixWord ++ tailWord_1147287) baseStart_1147287 baseEnd_1147287 := by
    simpa [prefixWord, tailWord_1147287, baseEnd_1147287] using wordTrace_append hprefix tailTrace_1147287
  have hstable : (prefixWord ++ tailWord_1147287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147287).length < 2 ^ (prefixWord ++ tailWord_1147287).sum := by decide
  have hdescent : baseEnd_1147287 < baseStart_1147287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147314 : List Nat := [3, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1147314 : Nat := 118140960795 + 1147314 * 2 ^ 59
def prefixEnd_1147314 : Nat := 4983230072969 + 3 ^ 40 * 1147314 * 2
def baseEnd_1147314 : Nat := 589123543632629362398605

theorem tailTrace_1147314 : CollatzResearch.WordTrace tailWord_1147314 prefixEnd_1147314 589123543632629362398605 := by
  unfold tailWord_1147314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461494841371199619070249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27897319576989865650853997 10461494841371199619070249)
  ·
    refine ⟨7846121131028399714302687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10461494841371199619070249 7846121131028399714302687)
    ·
      refine ⟨11769181696542599571454031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7846121131028399714302687 11769181696542599571454031)
      ·
        refine ⟨17653772544813899357181047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11769181696542599571454031 17653772544813899357181047)
        ·
          refine ⟨26480658817220849035771571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17653772544813899357181047 26480658817220849035771571)
          ·
            refine ⟨39720988225831273553657357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26480658817220849035771571 39720988225831273553657357)
            ·
              refine ⟨14895370584686727582621509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39720988225831273553657357 14895370584686727582621509)
              ·
                refine ⟨2792881984628761421741533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14895370584686727582621509 2792881984628761421741533)
                ·
                  refine ⟨1047330744235785533153075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2792881984628761421741533 1047330744235785533153075)
                  ·
                    refine ⟨1570996116353678299729613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047330744235785533153075 1570996116353678299729613)
                    ·
                      refine ⟨589123543632629362398605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1570996116353678299729613 589123543632629362398605)
                      ·
                        rfl

theorem cell23_1147314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1147314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147314 prefixEnd_1147314 := by exact prefixLift 1147314
  have htrace : WordTrace (prefixWord ++ tailWord_1147314) baseStart_1147314 baseEnd_1147314 := by
    simpa [prefixWord, tailWord_1147314, baseEnd_1147314] using wordTrace_append hprefix tailTrace_1147314
  have hstable : (prefixWord ++ tailWord_1147314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147314).length < 2 ^ (prefixWord ++ tailWord_1147314).sum := by decide
  have hdescent : baseEnd_1147314 < baseStart_1147314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147348 : List Nat := [2, 4, 1, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_1147348 : Nat := 118140960795 + 1147348 * 2 ^ 59
def prefixEnd_1147348 : Nat := 4983230072969 + 3 ^ 40 * 1147348 * 2
def baseEnd_1147348 : Nat := 589141001974882229373449

theorem tailTrace_1147348 : CollatzResearch.WordTrace tailWord_1147348 prefixEnd_1147348 589141001974882229373449 := by
  unfold tailWord_1147348
  simp only [CollatzResearch.WordTrace]
  refine ⟨20923609723680811141509349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27898146298241081522012465 20923609723680811141509349)
  ·
    refine ⟨3923176823190152089033003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20923609723680811141509349 3923176823190152089033003)
    ·
      refine ⟨5884765234785228133549505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3923176823190152089033003 5884765234785228133549505)
      ·
        refine ⟨4413573926088921100162129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5884765234785228133549505 4413573926088921100162129)
        ·
          refine ⟨3310180444566690825121597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4413573926088921100162129 3310180444566690825121597)
          ·
            refine ⟨1241317666712509059420599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3310180444566690825121597 1241317666712509059420599)
            ·
              refine ⟨1861976500068763589130899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1241317666712509059420599 1861976500068763589130899)
              ·
                refine ⟨2792964750103145383696349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861976500068763589130899 2792964750103145383696349)
                ·
                  refine ⟨1047361781288679518886131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2792964750103145383696349 1047361781288679518886131)
                  ·
                    refine ⟨1571042671933019278329197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047361781288679518886131 1571042671933019278329197)
                    ·
                      refine ⟨589141001974882229373449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1571042671933019278329197 589141001974882229373449)
                      ·
                        rfl

theorem cell23_1147348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_1147348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147348 prefixEnd_1147348 := by exact prefixLift 1147348
  have htrace : WordTrace (prefixWord ++ tailWord_1147348) baseStart_1147348 baseEnd_1147348 := by
    simpa [prefixWord, tailWord_1147348, baseEnd_1147348] using wordTrace_append hprefix tailTrace_1147348
  have hstable : (prefixWord ++ tailWord_1147348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147348).length < 2 ^ (prefixWord ++ tailWord_1147348).sum := by decide
  have hdescent : baseEnd_1147348 < baseStart_1147348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147367 : List Nat := [1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1147367 : Nat := 118140960795 + 1147367 * 2 ^ 59
def prefixEnd_1147367 : Nat := 4983230072969 + 3 ^ 40 * 1147367 * 2
def baseEnd_1147367 : Nat := 589150758107317655035861

theorem tailTrace_1147367 : CollatzResearch.WordTrace tailWord_1147367 prefixEnd_1147367 589150758107317655035861 := by
  unfold tailWord_1147367
  simp only [CollatzResearch.WordTrace]
  refine ⟨41847912434292788527960355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27898608289528525685306903 41847912434292788527960355)
  ·
    refine ⟨62771868651439182791940533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41847912434292788527960355 62771868651439182791940533)
    ·
      refine ⟨5884862686072423386744425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62771868651439182791940533 5884862686072423386744425)
      ·
        refine ⟨4413647014554317540058319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5884862686072423386744425 4413647014554317540058319)
        ·
          refine ⟨6620470521831476310087479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413647014554317540058319 6620470521831476310087479)
          ·
            refine ⟨9930705782747214465131219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6620470521831476310087479 9930705782747214465131219)
            ·
              refine ⟨14896058674120821697696829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9930705782747214465131219 14896058674120821697696829)
              ·
                refine ⟨5586022002795308136636311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14896058674120821697696829 5586022002795308136636311)
                ·
                  refine ⟨8379033004192962204954467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5586022002795308136636311 8379033004192962204954467)
                  ·
                    refine ⟨12568549506289443307431701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8379033004192962204954467 12568549506289443307431701)
                    ·
                      refine ⟨589150758107317655035861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12568549506289443307431701 589150758107317655035861)
                      ·
                        rfl

theorem cell23_1147367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1147367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147367 prefixEnd_1147367 := by exact prefixLift 1147367
  have htrace : WordTrace (prefixWord ++ tailWord_1147367) baseStart_1147367 baseEnd_1147367 := by
    simpa [prefixWord, tailWord_1147367, baseEnd_1147367] using wordTrace_append hprefix tailTrace_1147367
  have hstable : (prefixWord ++ tailWord_1147367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147367).length < 2 ^ (prefixWord ++ tailWord_1147367).sum := by decide
  have hdescent : baseEnd_1147367 < baseStart_1147367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147381 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1147381 : Nat := 118140960795 + 1147381 * 2 ^ 59
def prefixEnd_1147381 : Nat := 4983230072969 + 3 ^ 40 * 1147381 * 2
def baseEnd_1147381 : Nat := 196385982278826866753599

theorem tailTrace_1147381 : CollatzResearch.WordTrace tailWord_1147381 prefixEnd_1147381 196385982278826866753599 := by
  unfold tailWord_1147381
  simp only [CollatzResearch.WordTrace]
  refine ⟨41848423056242068918969997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27898948704161379279313331 41848423056242068918969997)
  ·
    refine ⟨15693158646090775844613749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41848423056242068918969997 15693158646090775844613749)
    ·
      refine ⟨1471233623071010235432539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15693158646090775844613749 1471233623071010235432539)
      ·
        refine ⟨2206850434606515353148809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471233623071010235432539 2206850434606515353148809)
        ·
          refine ⟨1655137825954886514861607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2206850434606515353148809 1655137825954886514861607)
          ·
            refine ⟨2482706738932329772292411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655137825954886514861607 2482706738932329772292411)
            ·
              refine ⟨3724060108398494658438617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482706738932329772292411 3724060108398494658438617)
              ·
                refine ⟨2793045081298870993828963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724060108398494658438617 2793045081298870993828963)
                ·
                  refine ⟨4189567621948306490743445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793045081298870993828963 4189567621948306490743445)
                  ·
                    refine ⟨196385982278826866753599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4189567621948306490743445 196385982278826866753599)
                    ·
                      rfl

theorem cell23_1147381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1147381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147381 prefixEnd_1147381 := by exact prefixLift 1147381
  have htrace : WordTrace (prefixWord ++ tailWord_1147381) baseStart_1147381 baseEnd_1147381 := by
    simpa [prefixWord, tailWord_1147381, baseEnd_1147381] using wordTrace_append hprefix tailTrace_1147381
  have hstable : (prefixWord ++ tailWord_1147381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147381).length < 2 ^ (prefixWord ++ tailWord_1147381).sum := by decide
  have hdescent : baseEnd_1147381 < baseStart_1147381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147388 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_1147388 : Nat := 118140960795 + 1147388 * 2 ^ 59
def prefixEnd_1147388 : Nat := 4983230072969 + 3 ^ 40 * 1147388 * 2
def baseEnd_1147388 : Nat := 589161541201062072873265

theorem tailTrace_1147388 : CollatzResearch.WordTrace tailWord_1147388 prefixEnd_1147388 589161541201062072873265 := by
  unfold tailWord_1147388
  simp only [CollatzResearch.WordTrace]
  refine ⟨20924339183608354557237409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27899118911477806076316545 20924339183608354557237409)
  ·
    refine ⟨15693254387706265917928057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20924339183608354557237409 15693254387706265917928057)
    ·
      refine ⟨11769940790779699438446043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15693254387706265917928057 11769940790779699438446043)
      ·
        refine ⟨17654911186169549157669065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11769940790779699438446043 17654911186169549157669065)
        ·
          refine ⟨13241183389627161868251799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17654911186169549157669065 13241183389627161868251799)
          ·
            refine ⟨19861775084440742802377699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13241183389627161868251799 19861775084440742802377699)
            ·
              refine ⟨29792662626661114203566549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19861775084440742802377699 29792662626661114203566549)
              ·
                refine ⟨698265530312369864146091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29792662626661114203566549 698265530312369864146091)
                ·
                  refine ⟨1047398295468554796219137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698265530312369864146091 1047398295468554796219137)
                  ·
                    refine ⟨785548721601416097164353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1047398295468554796219137 785548721601416097164353)
                    ·
                      refine ⟨589161541201062072873265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785548721601416097164353 589161541201062072873265)
                      ·
                        rfl

theorem cell23_1147388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_1147388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147388 prefixEnd_1147388 := by exact prefixLift 1147388
  have htrace : WordTrace (prefixWord ++ tailWord_1147388) baseStart_1147388 baseEnd_1147388 := by
    simpa [prefixWord, tailWord_1147388, baseEnd_1147388] using wordTrace_append hprefix tailTrace_1147388
  have hstable : (prefixWord ++ tailWord_1147388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147388).length < 2 ^ (prefixWord ++ tailWord_1147388).sum := by decide
  have hdescent : baseEnd_1147388 < baseStart_1147388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147391 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 1, 2, 3]
def baseStart_1147391 : Nat := 118140960795 + 1147391 * 2 ^ 59
def prefixEnd_1147391 : Nat := 4983230072969 + 3 ^ 40 * 1147391 * 2
def baseEnd_1147391 : Nat := 589163081643025561135751

theorem tailTrace_1147391 : CollatzResearch.WordTrace tailWord_1147391 prefixEnd_1147391 589163081643025561135751 := by
  unfold tailWord_1147391
  simp only [CollatzResearch.WordTrace]
  refine ⟨41848787786205840626834027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27899191857470560417889351 41848787786205840626834027)
  ·
    refine ⟨62773181679308760940251041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41848787786205840626834027 62773181679308760940251041)
    ·
      refine ⟨47079886259481570705188281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62773181679308760940251041 47079886259481570705188281)
      ·
        refine ⟨35309914694611178028891211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47079886259481570705188281 35309914694611178028891211)
        ·
          refine ⟨52964872041916767043336817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35309914694611178028891211 52964872041916767043336817)
          ·
            refine ⟨39723654031437575282502613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52964872041916767043336817 39723654031437575282502613)
            ·
              refine ⟨931023141361818170683655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39723654031437575282502613 931023141361818170683655)
              ·
                refine ⟨1396534712042727256025483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931023141361818170683655 1396534712042727256025483)
                ·
                  refine ⟨2094802068064090884038225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396534712042727256025483 2094802068064090884038225)
                  ·
                    refine ⟨1571101551048068163028669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2094802068064090884038225 1571101551048068163028669)
                    ·
                      refine ⟨589163081643025561135751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1571101551048068163028669 589163081643025561135751)
                      ·
                        rfl

theorem cell23_1147391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 1, 2, 3].length) (baseStart_1147391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147391 prefixEnd_1147391 := by exact prefixLift 1147391
  have htrace : WordTrace (prefixWord ++ tailWord_1147391) baseStart_1147391 baseEnd_1147391 := by
    simpa [prefixWord, tailWord_1147391, baseEnd_1147391] using wordTrace_append hprefix tailTrace_1147391
  have hstable : (prefixWord ++ tailWord_1147391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147391).length < 2 ^ (prefixWord ++ tailWord_1147391).sum := by decide
  have hdescent : baseEnd_1147391 < baseStart_1147391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147394 : List Nat := [3, 4, 1, 2, 2, 11]
def baseStart_1147394 : Nat := 118140960795 + 1147394 * 2 ^ 59
def prefixEnd_1147394 : Nat := 4983230072969 + 3 ^ 40 * 1147394 * 2
def baseEnd_1147394 : Nat := 2424545769897074277359

theorem tailTrace_1147394 : CollatzResearch.WordTrace tailWord_1147394 prefixEnd_1147394 2424545769897074277359 := by
  unfold tailWord_1147394
  simp only [CollatzResearch.WordTrace]
  refine ⟨10462224301298743034798309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27899264803463314759462157 10462224301298743034798309)
  ·
    refine ⟨1961667056493514319024683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10462224301298743034798309 1961667056493514319024683)
    ·
      refine ⟨2942500584740271478537025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1961667056493514319024683 2942500584740271478537025)
      ·
        refine ⟨2206875438555203608902769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2942500584740271478537025 2206875438555203608902769)
        ·
          refine ⟨1655156578916402706677077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2206875438555203608902769 1655156578916402706677077)
          ·
            refine ⟨2424545769897074277359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1655156578916402706677077 2424545769897074277359)
            ·
              rfl

theorem cell23_1147394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 11].length) (baseStart_1147394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147394 prefixEnd_1147394 := by exact prefixLift 1147394
  have htrace : WordTrace (prefixWord ++ tailWord_1147394) baseStart_1147394 baseEnd_1147394 := by
    simpa [prefixWord, tailWord_1147394, baseEnd_1147394] using wordTrace_append hprefix tailTrace_1147394
  have hstable : (prefixWord ++ tailWord_1147394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147394).length < 2 ^ (prefixWord ++ tailWord_1147394).sum := by decide
  have hdescent : baseEnd_1147394 < baseStart_1147394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147421 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1147421 : Nat := 118140960795 + 1147421 * 2 ^ 59
def prefixEnd_1147421 : Nat := 4983230072969 + 3 ^ 40 * 1147421 * 2
def baseEnd_1147421 : Nat := 589178486062660443760613

theorem tailTrace_1147421 : CollatzResearch.WordTrace tailWord_1147421 prefixEnd_1147421 589178486062660443760613 := by
  unfold tailWord_1147421
  simp only [CollatzResearch.WordTrace]
  refine ⟨41849881976097155750426117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27899921317398103833617411 41849881976097155750426117)
  ·
    refine ⟨7846852870518216703204897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41849881976097155750426117 7846852870518216703204897)
    ·
      refine ⟨5885139652888662527403673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7846852870518216703204897 5885139652888662527403673)
      ·
        refine ⟨4413854739666496895552755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5885139652888662527403673 4413854739666496895552755)
        ·
          refine ⟨6620782109499745343329133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413854739666496895552755 6620782109499745343329133)
          ·
            refine ⟨2482793291062404503748425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6620782109499745343329133 2482793291062404503748425)
            ·
              refine ⟨1862094968296803377811319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482793291062404503748425 1862094968296803377811319)
              ·
                refine ⟨2793142452445205066716979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862094968296803377811319 2793142452445205066716979)
                ·
                  refine ⟨4189713678667807600075469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793142452445205066716979 4189713678667807600075469)
                  ·
                    refine ⟨1571142629500427850028301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4189713678667807600075469 1571142629500427850028301)
                    ·
                      refine ⟨589178486062660443760613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1571142629500427850028301 589178486062660443760613)
                      ·
                        rfl

theorem cell23_1147421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1147421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147421 prefixEnd_1147421 := by exact prefixLift 1147421
  have htrace : WordTrace (prefixWord ++ tailWord_1147421) baseStart_1147421 baseEnd_1147421 := by
    simpa [prefixWord, tailWord_1147421, baseEnd_1147421] using wordTrace_append hprefix tailTrace_1147421
  have hstable : (prefixWord ++ tailWord_1147421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147421).length < 2 ^ (prefixWord ++ tailWord_1147421).sum := by decide
  have hdescent : baseEnd_1147421 < baseStart_1147421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147447 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_1147447 : Nat := 118140960795 + 1147447 * 2 ^ 59
def prefixEnd_1147447 : Nat := 4983230072969 + 3 ^ 40 * 1147447 * 2
def baseEnd_1147447 : Nat := 589191836559677342035493

theorem tailTrace_1147447 : CollatzResearch.WordTrace tailWord_1147447 prefixEnd_1147447 589191836559677342035493 := by
  unfold tailWord_1147447
  simp only [CollatzResearch.WordTrace]
  refine ⟨41850830274002962190872595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27900553516001974793915063 41850830274002962190872595)
  ·
    refine ⟨62776245411004443286308893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41850830274002962190872595 62776245411004443286308893)
    ·
      refine ⟨23541092029126666232365835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62776245411004443286308893 23541092029126666232365835)
      ·
        refine ⟨35311638043689999348548753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23541092029126666232365835 35311638043689999348548753)
        ·
          refine ⟨26483728532767499511411565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35311638043689999348548753 26483728532767499511411565)
          ·
            refine ⟨9931398199787812316779337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26483728532767499511411565 9931398199787812316779337)
            ·
              refine ⟨7448548649840859237584503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9931398199787812316779337 7448548649840859237584503)
              ·
                refine ⟨11172822974761288856376755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448548649840859237584503 11172822974761288856376755)
                ·
                  refine ⟨16759234462141933284565133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11172822974761288856376755 16759234462141933284565133)
                  ·
                    refine ⟨6284712923303224981711925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16759234462141933284565133 6284712923303224981711925)
                    ·
                      refine ⟨589191836559677342035493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6284712923303224981711925 589191836559677342035493)
                      ·
                        rfl

theorem cell23_1147447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_1147447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147447 prefixEnd_1147447 := by exact prefixLift 1147447
  have htrace : WordTrace (prefixWord ++ tailWord_1147447) baseStart_1147447 baseEnd_1147447 := by
    simpa [prefixWord, tailWord_1147447, baseEnd_1147447] using wordTrace_append hprefix tailTrace_1147447
  have hstable : (prefixWord ++ tailWord_1147447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147447).length < 2 ^ (prefixWord ++ tailWord_1147447).sum := by decide
  have hdescent : baseEnd_1147447 < baseStart_1147447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147467 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 7]
def baseStart_1147467 : Nat := 118140960795 + 1147467 * 2 ^ 59
def prefixEnd_1147467 : Nat := 4983230072969 + 3 ^ 40 * 1147467 * 2
def baseEnd_1147467 : Nat := 65466900685863029309489

theorem tailTrace_1147467 : CollatzResearch.WordTrace tailWord_1147467 prefixEnd_1147467 65466900685863029309489 := by
  unfold tailWord_1147467
  simp only [CollatzResearch.WordTrace]
  refine ⟨41851559733930505606600655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27901039822620337071067103 41851559733930505606600655)
  ·
    refine ⟨62777339600895758409900983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41851559733930505606600655 62777339600895758409900983)
    ·
      refine ⟨94166009401343637614851475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62777339600895758409900983 94166009401343637614851475)
      ·
        refine ⟨141249014102015456422277213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94166009401343637614851475 141249014102015456422277213)
        ·
          refine ⟨52968380288255796158353955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141249014102015456422277213 52968380288255796158353955)
          ·
            refine ⟨79452570432383694237530933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52968380288255796158353955 79452570432383694237530933)
            ·
              refine ⟨7448678478035971334768525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79452570432383694237530933 7448678478035971334768525)
              ·
                refine ⟨2793254429263489250538197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7448678478035971334768525 2793254429263489250538197)
                ·
                  refine ⟨65466900685863029309489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2793254429263489250538197 65466900685863029309489)
                  ·
                    rfl

theorem cell23_1147467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 7].length) (baseStart_1147467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147467 prefixEnd_1147467 := by exact prefixLift 1147467
  have htrace : WordTrace (prefixWord ++ tailWord_1147467) baseStart_1147467 baseEnd_1147467 := by
    simpa [prefixWord, tailWord_1147467, baseEnd_1147467] using wordTrace_append hprefix tailTrace_1147467
  have hstable : (prefixWord ++ tailWord_1147467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147467).length < 2 ^ (prefixWord ++ tailWord_1147467).sum := by decide
  have hdescent : baseEnd_1147467 < baseStart_1147467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147474 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1147474 : Nat := 118140960795 + 1147474 * 2 ^ 59
def prefixEnd_1147474 : Nat := 4983230072969 + 3 ^ 40 * 1147474 * 2
def baseEnd_1147474 : Nat := 589205700537348736397869

theorem tailTrace_1147474 : CollatzResearch.WordTrace tailWord_1147474 prefixEnd_1147474 589205700537348736397869 := by
  unfold tailWord_1147474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10462953761226286450526369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27901210029936763868070317 10462953761226286450526369)
  ·
    refine ⟨7847215320919714837894777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10462953761226286450526369 7847215320919714837894777)
    ·
      refine ⟨5885411490689786128421083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7847215320919714837894777 5885411490689786128421083)
      ·
        refine ⟨8828117236034679192631625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5885411490689786128421083 8828117236034679192631625)
        ·
          refine ⟨6621087927026009394473719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8828117236034679192631625 6621087927026009394473719)
          ·
            refine ⟨9931631890539014091710579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621087927026009394473719 9931631890539014091710579)
            ·
              refine ⟨14897447835808521137565869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9931631890539014091710579 14897447835808521137565869)
              ·
                refine ⟨5586542938428195426587201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14897447835808521137565869 5586542938428195426587201)
                ·
                  refine ⟨4189907203821146569940401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5586542938428195426587201 4189907203821146569940401)
                  ·
                    refine ⟨3142430402865859927455301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4189907203821146569940401 3142430402865859927455301)
                    ·
                      refine ⟨589205700537348736397869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3142430402865859927455301 589205700537348736397869)
                      ·
                        rfl

theorem cell23_1147474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1147474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147474 prefixEnd_1147474 := by exact prefixLift 1147474
  have htrace : WordTrace (prefixWord ++ tailWord_1147474) baseStart_1147474 baseEnd_1147474 := by
    simpa [prefixWord, tailWord_1147474, baseEnd_1147474] using wordTrace_append hprefix tailTrace_1147474
  have hstable : (prefixWord ++ tailWord_1147474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147474).length < 2 ^ (prefixWord ++ tailWord_1147474).sum := by decide
  have hdescent : baseEnd_1147474 < baseStart_1147474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147521 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_1147521 : Nat := 118140960795 + 1147521 * 2 ^ 59
def prefixEnd_1147521 : Nat := 4983230072969 + 3 ^ 40 * 1147521 * 2
def baseEnd_1147521 : Nat := 589229834128110052510153

theorem tailTrace_1147521 : CollatzResearch.WordTrace tailWord_1147521 prefixEnd_1147521 589229834128110052510153 := by
  unfold tailWord_1147521
  simp only [CollatzResearch.WordTrace]
  refine ⟨41853529275734872829066417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27902352850489915219377611 41853529275734872829066417)
  ·
    refine ⟨31390146956801154621799813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41853529275734872829066417 31390146956801154621799813)
    ·
      refine ⟨5885652554400216491587465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31390146956801154621799813 5885652554400216491587465)
      ·
        refine ⟨4414239415800162368690599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5885652554400216491587465 4414239415800162368690599)
        ·
          refine ⟨6621359123700243553035899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414239415800162368690599 6621359123700243553035899)
          ·
            refine ⟨9932038685550365329553849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621359123700243553035899 9932038685550365329553849)
            ·
              refine ⟨7449029014162773997165387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9932038685550365329553849 7449029014162773997165387)
              ·
                refine ⟨11173543521244160995748081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449029014162773997165387 11173543521244160995748081)
                ·
                  refine ⟨8380157640933120746811061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11173543521244160995748081 8380157640933120746811061)
                  ·
                    refine ⟨785639778837480070013537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8380157640933120746811061 785639778837480070013537)
                    ·
                      refine ⟨589229834128110052510153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785639778837480070013537 589229834128110052510153)
                      ·
                        rfl

theorem cell23_1147521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_1147521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147521 prefixEnd_1147521 := by exact prefixLift 1147521
  have htrace : WordTrace (prefixWord ++ tailWord_1147521) baseStart_1147521 baseEnd_1147521 := by
    simpa [prefixWord, tailWord_1147521, baseEnd_1147521] using wordTrace_append hprefix tailTrace_1147521
  have hstable : (prefixWord ++ tailWord_1147521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147521).length < 2 ^ (prefixWord ++ tailWord_1147521).sum := by decide
  have hdescent : baseEnd_1147521 < baseStart_1147521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147524 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1147524 : Nat := 118140960795 + 1147524 * 2 ^ 59
def prefixEnd_1147524 : Nat := 4983230072969 + 3 ^ 40 * 1147524 * 2
def baseEnd_1147524 : Nat := 589231374570073540772639

theorem tailTrace_1147524 : CollatzResearch.WordTrace tailWord_1147524 prefixEnd_1147524 589231374570073540772639 := by
  unfold tailWord_1147524
  simp only [CollatzResearch.WordTrace]
  refine ⟨20926819347362002170712813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27902425796482669560950417 20926819347362002170712813)
  ·
    refine ⟨7847557255260750814017305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20926819347362002170712813 7847557255260750814017305)
    ·
      refine ⟨5885667941445563110512979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7847557255260750814017305 5885667941445563110512979)
      ·
        refine ⟨8828501912168344665769469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5885667941445563110512979 8828501912168344665769469)
        ·
          refine ⟨3310688217063129249663551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8828501912168344665769469 3310688217063129249663551)
          ·
            refine ⟨4966032325594693874495327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310688217063129249663551 4966032325594693874495327)
            ·
              refine ⟨7449048488392040811742991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966032325594693874495327 7449048488392040811742991)
              ·
                refine ⟨11173572732588061217614487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7449048488392040811742991 11173572732588061217614487)
                ·
                  refine ⟨16760359098882091826421731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11173572732588061217614487 16760359098882091826421731)
                  ·
                    refine ⟨25140538648323137739632597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16760359098882091826421731 25140538648323137739632597)
                    ·
                      refine ⟨589231374570073540772639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25140538648323137739632597 589231374570073540772639)
                      ·
                        rfl

theorem cell23_1147524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1147524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147524 prefixEnd_1147524 := by exact prefixLift 1147524
  have htrace : WordTrace (prefixWord ++ tailWord_1147524) baseStart_1147524 baseEnd_1147524 := by
    simpa [prefixWord, tailWord_1147524, baseEnd_1147524] using wordTrace_append hprefix tailTrace_1147524
  have hstable : (prefixWord ++ tailWord_1147524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147524).length < 2 ^ (prefixWord ++ tailWord_1147524).sum := by decide
  have hdescent : baseEnd_1147524 < baseStart_1147524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147537 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 9]
def baseStart_1147537 : Nat := 118140960795 + 1147537 * 2 ^ 59
def prefixEnd_1147537 : Nat := 4983230072969 + 3 ^ 40 * 1147537 * 2
def baseEnd_1147537 : Nat := 589238049818581989910079

theorem tailTrace_1147537 : CollatzResearch.WordTrace tailWord_1147537 prefixEnd_1147537 589238049818581989910079 := by
  unfold tailWord_1147537
  simp only [CollatzResearch.WordTrace]
  refine ⟨41854112843676907561648865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27902741895784605041099243 41854112843676907561648865)
  ·
    refine ⟨31390584632757680671236649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41854112843676907561648865 31390584632757680671236649)
    ·
      refine ⟨23542938474568260503427487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31390584632757680671236649 23542938474568260503427487)
      ·
        refine ⟨35314407711852390755141231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23542938474568260503427487 35314407711852390755141231)
        ·
          refine ⟨52971611567778586132711847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35314407711852390755141231 52971611567778586132711847)
          ·
            refine ⟨79457417351667879199067771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52971611567778586132711847 79457417351667879199067771)
            ·
              refine ⟨119186126027501818798601657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79457417351667879199067771 119186126027501818798601657)
              ·
                refine ⟨89389594520626364098951243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119186126027501818798601657 89389594520626364098951243)
                ·
                  refine ⟨134084391780939546148426865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89389594520626364098951243 134084391780939546148426865)
                  ·
                    refine ⟨100563293835704659611320149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134084391780939546148426865 100563293835704659611320149)
                    ·
                      refine ⟨589238049818581989910079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 100563293835704659611320149 589238049818581989910079)
                      ·
                        rfl

theorem cell23_1147537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_1147537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147537 prefixEnd_1147537 := by exact prefixLift 1147537
  have htrace : WordTrace (prefixWord ++ tailWord_1147537) baseStart_1147537 baseEnd_1147537 := by
    simpa [prefixWord, tailWord_1147537, baseEnd_1147537] using wordTrace_append hprefix tailTrace_1147537
  have hstable : (prefixWord ++ tailWord_1147537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147537).length < 2 ^ (prefixWord ++ tailWord_1147537).sum := by decide
  have hdescent : baseEnd_1147537 < baseStart_1147537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147571 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3]
def baseStart_1147571 : Nat := 118140960795 + 1147571 * 2 ^ 59
def prefixEnd_1147571 : Nat := 4983230072969 + 3 ^ 40 * 1147571 * 2
def baseEnd_1147571 : Nat := 589255508160834856884923

theorem tailTrace_1147571 : CollatzResearch.WordTrace tailWord_1147571 prefixEnd_1147571 589255508160834856884923 := by
  unfold tailWord_1147571
  simp only [CollatzResearch.WordTrace]
  refine ⟨41855352925553731368386567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27903568617035820912257711 41855352925553731368386567)
  ·
    refine ⟨62783029388330597052579851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41855352925553731368386567 62783029388330597052579851)
    ·
      refine ⟨94174544082495895578869777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62783029388330597052579851 94174544082495895578869777)
      ·
        refine ⟨70630908061871921684152333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94174544082495895578869777 70630908061871921684152333)
        ·
          refine ⟨26486590523201970631557125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70630908061871921684152333 26486590523201970631557125)
          ·
            refine ⟨4966235723100369493416961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26486590523201970631557125 4966235723100369493416961)
            ·
              refine ⟨3724676792325277120062721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966235723100369493416961 3724676792325277120062721)
              ·
                refine ⟨2793507594243957840047041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724676792325277120062721 2793507594243957840047041)
                ·
                  refine ⟨2095130695682968380035281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793507594243957840047041 2095130695682968380035281)
                  ·
                    refine ⟨1571348021762226285026461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095130695682968380035281 1571348021762226285026461)
                    ·
                      refine ⟨589255508160834856884923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1571348021762226285026461 589255508160834856884923)
                      ·
                        rfl

theorem cell23_1147571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_1147571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147571 prefixEnd_1147571 := by exact prefixLift 1147571
  have htrace : WordTrace (prefixWord ++ tailWord_1147571) baseStart_1147571 baseEnd_1147571 := by
    simpa [prefixWord, tailWord_1147571, baseEnd_1147571] using wordTrace_append hprefix tailTrace_1147571
  have hstable : (prefixWord ++ tailWord_1147571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147571).length < 2 ^ (prefixWord ++ tailWord_1147571).sum := by decide
  have hdescent : baseEnd_1147571 < baseStart_1147571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147578 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 1, 4]
def baseStart_1147578 : Nat := 118140960795 + 1147578 * 2 ^ 59
def prefixEnd_1147578 : Nat := 4983230072969 + 3 ^ 40 * 1147578 * 2
def baseEnd_1147578 : Nat := 196419700841805443165797

theorem tailTrace_1147578 : CollatzResearch.WordTrace tailWord_1147578 prefixEnd_1147578 196419700841805443165797 := by
  unfold tailWord_1147578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10463902059132092890972847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27903738824352247709260925 10463902059132092890972847)
  ·
    refine ⟨15695853088698139336459271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10463902059132092890972847 15695853088698139336459271)
    ·
      refine ⟨23543779633047209004688907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15695853088698139336459271 23543779633047209004688907)
      ·
        refine ⟨35315669449570813507033361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23543779633047209004688907 35315669449570813507033361)
        ·
          refine ⟨26486752087178110130275021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35315669449570813507033361 26486752087178110130275021)
          ·
            refine ⟨9932532032691791298853133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26486752087178110130275021 9932532032691791298853133)
            ·
              refine ⟨3724699512259421737069925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9932532032691791298853133 3724699512259421737069925)
              ·
                refine ⟨698381158548641575700611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3724699512259421737069925 698381158548641575700611)
                ·
                  refine ⟨1047571737822962363550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698381158548641575700611 1047571737822962363550917)
                  ·
                    refine ⟨196419700841805443165797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047571737822962363550917 196419700841805443165797)
                    ·
                      rfl

theorem cell23_1147578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_1147578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147578 prefixEnd_1147578 := by exact prefixLift 1147578
  have htrace : WordTrace (prefixWord ++ tailWord_1147578) baseStart_1147578 baseEnd_1147578 := by
    simpa [prefixWord, tailWord_1147578, baseEnd_1147578] using wordTrace_append hprefix tailTrace_1147578
  have hstable : (prefixWord ++ tailWord_1147578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147578).length < 2 ^ (prefixWord ++ tailWord_1147578).sum := by decide
  have hdescent : baseEnd_1147578 < baseStart_1147578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147611 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 8, 3, 2]
def baseStart_1147611 : Nat := 118140960795 + 1147611 * 2 ^ 59
def prefixEnd_1147611 : Nat := 4983230072969 + 3 ^ 40 * 1147611 * 2
def baseEnd_1147611 : Nat := 589276047387014700384739

theorem tailTrace_1147611 : CollatzResearch.WordTrace tailWord_1147611 prefixEnd_1147611 589276047387014700384739 := by
  unfold tailWord_1147611
  simp only [CollatzResearch.WordTrace]
  refine ⟨41856811845408818199842687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27904541230272545466561791 41856811845408818199842687)
  ·
    refine ⟨62785217768113227299764031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41856811845408818199842687 62785217768113227299764031)
    ·
      refine ⟨94177826652169840949646047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62785217768113227299764031 94177826652169840949646047)
      ·
        refine ⟨141266739978254761424469071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94177826652169840949646047 141266739978254761424469071)
        ·
          refine ⟨211900109967382142136703607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141266739978254761424469071 211900109967382142136703607)
          ·
            refine ⟨317850164951073213205055411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211900109967382142136703607 317850164951073213205055411)
            ·
              refine ⟨476775247426609819807583117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317850164951073213205055411 476775247426609819807583117)
              ·
                refine ⟨178790717784978682427843669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 476775247426609819807583117 178790717784978682427843669)
                ·
                  refine ⟨2095203724042718934701293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 178790717784978682427843669 2095203724042718934701293)
                  ·
                    refine ⟨785701396516019600512985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2095203724042718934701293 785701396516019600512985)
                    ·
                      refine ⟨589276047387014700384739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785701396516019600512985 589276047387014700384739)
                      ·
                        rfl

theorem cell23_1147611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 3, 2].length) (baseStart_1147611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147611 prefixEnd_1147611 := by exact prefixLift 1147611
  have htrace : WordTrace (prefixWord ++ tailWord_1147611) baseStart_1147611 baseEnd_1147611 := by
    simpa [prefixWord, tailWord_1147611, baseEnd_1147611] using wordTrace_append hprefix tailTrace_1147611
  have hstable : (prefixWord ++ tailWord_1147611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147611).length < 2 ^ (prefixWord ++ tailWord_1147611).sum := by decide
  have hdescent : baseEnd_1147611 < baseStart_1147611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147612 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_1147612 : Nat := 118140960795 + 1147612 * 2 ^ 59
def prefixEnd_1147612 : Nat := 4983230072969 + 3 ^ 40 * 1147612 * 2
def baseEnd_1147612 : Nat := 196425520289223065490745

theorem tailTrace_1147612 : CollatzResearch.WordTrace tailWord_1147612 prefixEnd_1147612 196425520289223065490745 := by
  unfold tailWord_1147612
  simp only [CollatzResearch.WordTrace]
  refine ⟨20928424159202597685314545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27904565545603463580419393 20928424159202597685314545)
  ·
    refine ⟨15696318119401948263985909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20928424159202597685314545 15696318119401948263985909)
    ·
      refine ⟨1471529823693932649748679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15696318119401948263985909 1471529823693932649748679)
      ·
        refine ⟨2207294735540898974623019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471529823693932649748679 2207294735540898974623019)
        ·
          refine ⟨3310942103311348461934529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207294735540898974623019 3310942103311348461934529)
          ·
            refine ⟨2483206577483511346450897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3310942103311348461934529 2483206577483511346450897)
            ·
              refine ⟨1862404933112633509838173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2483206577483511346450897 1862404933112633509838173)
              ·
                refine ⟨698401849917237566189315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1862404933112633509838173 698401849917237566189315)
                ·
                  refine ⟨1047602774875856349283973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698401849917237566189315 1047602774875856349283973)
                  ·
                    refine ⟨196425520289223065490745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047602774875856349283973 196425520289223065490745)
                    ·
                      rfl

theorem cell23_1147612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_1147612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147612 prefixEnd_1147612 := by exact prefixLift 1147612
  have htrace : WordTrace (prefixWord ++ tailWord_1147612) baseStart_1147612 baseEnd_1147612 := by
    simpa [prefixWord, tailWord_1147612, baseEnd_1147612] using wordTrace_append hprefix tailTrace_1147612
  have hstable : (prefixWord ++ tailWord_1147612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147612).length < 2 ^ (prefixWord ++ tailWord_1147612).sum := by decide
  have hdescent : baseEnd_1147612 < baseStart_1147612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147658 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1147658 : Nat := 118140960795 + 1147658 * 2 ^ 59
def prefixEnd_1147658 : Nat := 4983230072969 + 3 ^ 40 * 1147658 * 2
def baseEnd_1147658 : Nat := 589300180977776016497023

theorem tailTrace_1147658 : CollatzResearch.WordTrace tailWord_1147658 prefixEnd_1147658 589300180977776016497023 := by
  unfold tailWord_1147658
  simp only [CollatzResearch.WordTrace]
  refine ⟨10464631519059636306700907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27905684050825696817869085 10464631519059636306700907)
  ·
    refine ⟨15696947278589454460051361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10464631519059636306700907 15696947278589454460051361)
    ·
      refine ⟨11772710458942090845038521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15696947278589454460051361 11772710458942090845038521)
      ·
        refine ⟨8829532844206568133778891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11772710458942090845038521 8829532844206568133778891)
        ·
          refine ⟨13244299266309852200668337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8829532844206568133778891 13244299266309852200668337)
          ·
            refine ⟨9933224449732389150501253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13244299266309852200668337 9933224449732389150501253)
            ·
              refine ⟨1862479584324822965718985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9933224449732389150501253 1862479584324822965718985)
              ·
                refine ⟨1396859688243617224289239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862479584324822965718985 1396859688243617224289239)
                ·
                  refine ⟨2095289532365425836433859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396859688243617224289239 2095289532365425836433859)
                  ·
                    refine ⟨3142934298548138754650789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095289532365425836433859 3142934298548138754650789)
                    ·
                      refine ⟨589300180977776016497023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3142934298548138754650789 589300180977776016497023)
                      ·
                        rfl

theorem cell23_1147658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1147658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147658 prefixEnd_1147658 := by exact prefixLift 1147658
  have htrace : WordTrace (prefixWord ++ tailWord_1147658) baseStart_1147658 baseEnd_1147658 := by
    simpa [prefixWord, tailWord_1147658, baseEnd_1147658] using wordTrace_append hprefix tailTrace_1147658
  have hstable : (prefixWord ++ tailWord_1147658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147658).length < 2 ^ (prefixWord ++ tailWord_1147658).sum := by decide
  have hdescent : baseEnd_1147658 < baseStart_1147658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147702 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1147702 : Nat := 118140960795 + 1147702 * 2 ^ 59
def prefixEnd_1147702 : Nat := 4983230072969 + 3 ^ 40 * 1147702 * 2
def baseEnd_1147702 : Nat := 196440924708857948115607

theorem tailTrace_1147702 : CollatzResearch.WordTrace tailWord_1147702 prefixEnd_1147702 196440924708857948115607 := by
  unfold tailWord_1147702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2616258180504946296337835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27906753925386093827603573 2616258180504946296337835)
  ·
    refine ⟨3924387270757419444506753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2616258180504946296337835 3924387270757419444506753)
    ·
      refine ⟨2943290453068064583380065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924387270757419444506753 2943290453068064583380065)
      ·
        refine ⟨2207467839801048437535049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2943290453068064583380065 2207467839801048437535049)
        ·
          refine ⟨1655600879850786328151287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2207467839801048437535049 1655600879850786328151287)
          ·
            refine ⟨2483401319776179492226931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1655600879850786328151287 2483401319776179492226931)
            ·
              refine ⟨3725101979664269238340397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483401319776179492226931 3725101979664269238340397)
              ·
                refine ⟨1396913242374100964377649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3725101979664269238340397 1396913242374100964377649)
                ·
                  refine ⟨1047684931780575723283237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1396913242374100964377649 1047684931780575723283237)
                  ·
                    refine ⟨196440924708857948115607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047684931780575723283237 196440924708857948115607)
                    ·
                      rfl

theorem cell23_1147702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1147702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147702 prefixEnd_1147702 := by exact prefixLift 1147702
  have htrace : WordTrace (prefixWord ++ tailWord_1147702) baseStart_1147702 baseEnd_1147702 := by
    simpa [prefixWord, tailWord_1147702, baseEnd_1147702] using wordTrace_append hprefix tailTrace_1147702
  have hstable : (prefixWord ++ tailWord_1147702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147702).length < 2 ^ (prefixWord ++ tailWord_1147702).sum := by decide
  have hdescent : baseEnd_1147702 < baseStart_1147702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147761 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 4]
def baseStart_1147761 : Nat := 118140960795 + 1147761 * 2 ^ 59
def prefixEnd_1147761 : Nat := 4983230072969 + 3 ^ 40 * 1147761 * 2
def baseEnd_1147761 : Nat := 589353069485189113509049

theorem tailTrace_1147761 : CollatzResearch.WordTrace tailWord_1147761 prefixEnd_1147761 589353069485189113509049 := by
  unfold tailWord_1147761
  simp only [CollatzResearch.WordTrace]
  refine ⟨41862282794865393817803137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27908188529910262545202091 41862282794865393817803137)
  ·
    refine ⟨31396712096149045363352353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41862282794865393817803137 31396712096149045363352353)
    ·
      refine ⟨23547534072111784022514265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31396712096149045363352353 23547534072111784022514265)
      ·
        refine ⟨17660650554083838016885699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23547534072111784022514265 17660650554083838016885699)
        ·
          refine ⟨26490975831125757025328549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17660650554083838016885699 26490975831125757025328549)
          ·
            refine ⟨4967057968336079442249103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26490975831125757025328549 4967057968336079442249103)
            ·
              refine ⟨7450586952504119163373655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967057968336079442249103 7450586952504119163373655)
              ·
                refine ⟨11175880428756178745060483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7450586952504119163373655 11175880428756178745060483)
                ·
                  refine ⟨16763820643134268117590725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11175880428756178745060483 16763820643134268117590725)
                  ·
                    refine ⟨3143216370587675272048261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16763820643134268117590725 3143216370587675272048261)
                    ·
                      refine ⟨589353069485189113509049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3143216370587675272048261 589353069485189113509049)
                      ·
                        rfl

theorem cell23_1147761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_1147761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147761 prefixEnd_1147761 := by exact prefixLift 1147761
  have htrace : WordTrace (prefixWord ++ tailWord_1147761) baseStart_1147761 baseEnd_1147761 := by
    simpa [prefixWord, tailWord_1147761, baseEnd_1147761] using wordTrace_append hprefix tailTrace_1147761
  have hstable : (prefixWord ++ tailWord_1147761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147761).length < 2 ^ (prefixWord ++ tailWord_1147761).sum := by decide
  have hdescent : baseEnd_1147761 < baseStart_1147761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147765 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1147765 : Nat := 118140960795 + 1147765 * 2 ^ 59
def prefixEnd_1147765 : Nat := 4983230072969 + 3 ^ 40 * 1147765 * 2
def baseEnd_1147765 : Nat := 589355123407807097859031

theorem tailTrace_1147765 : CollatzResearch.WordTrace tailWord_1147765 prefixEnd_1147765 589355123407807097859031 := by
  unfold tailWord_1147765
  simp only [CollatzResearch.WordTrace]
  refine ⟨41862428686850902500948749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27908285791233935000632499 41862428686850902500948749)
  ·
    refine ⟨15698410757569088437855781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41862428686850902500948749 15698410757569088437855781)
    ·
      refine ⟨2943452017044204082097959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15698410757569088437855781 2943452017044204082097959)
      ·
        refine ⟨4415178025566306123146939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2943452017044204082097959 4415178025566306123146939)
        ·
          refine ⟨6622767038349459184720409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4415178025566306123146939 6622767038349459184720409)
          ·
            refine ⟨4967075278762094388540307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622767038349459184720409 4967075278762094388540307)
            ·
              refine ⟨7450612918143141582810461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967075278762094388540307 7450612918143141582810461)
              ·
                refine ⟨2793979844303678093553923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7450612918143141582810461 2793979844303678093553923)
                ·
                  refine ⟨4190969766455517140330885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793979844303678093553923 4190969766455517140330885)
                  ·
                    refine ⟨785806831210409463812041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4190969766455517140330885 785806831210409463812041)
                    ·
                      refine ⟨589355123407807097859031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785806831210409463812041 589355123407807097859031)
                      ·
                        rfl

theorem cell23_1147765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1147765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147765 prefixEnd_1147765 := by exact prefixLift 1147765
  have htrace : WordTrace (prefixWord ++ tailWord_1147765) baseStart_1147765 baseEnd_1147765 := by
    simpa [prefixWord, tailWord_1147765, baseEnd_1147765] using wordTrace_append hprefix tailTrace_1147765
  have hstable : (prefixWord ++ tailWord_1147765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147765).length < 2 ^ (prefixWord ++ tailWord_1147765).sum := by decide
  have hdescent : baseEnd_1147765 < baseStart_1147765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147788 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 5]
def baseStart_1147788 : Nat := 118140960795 + 1147788 * 2 ^ 59
def prefixEnd_1147788 : Nat := 4983230072969 + 3 ^ 40 * 1147788 * 2
def baseEnd_1147788 : Nat := 65485214829206723096825

theorem tailTrace_1147788 : CollatzResearch.WordTrace tailWord_1147788 prefixEnd_1147788 65485214829206723096825 := by
  unfold tailWord_1147788
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931633782883788714518009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27908845043845051619357345 20931633782883788714518009)
  ·
    refine ⟨15698725337162841535888507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20931633782883788714518009 15698725337162841535888507)
    ·
      refine ⟨23548088005744262303832761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15698725337162841535888507 23548088005744262303832761)
      ·
        refine ⟨17661066004308196727874571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23548088005744262303832761 17661066004308196727874571)
        ·
          refine ⟨26491599006462295091811857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17661066004308196727874571 26491599006462295091811857)
          ·
            refine ⟨19868699254846721318858893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26491599006462295091811857 19868699254846721318858893)
            ·
              refine ⟨7450762220567520494572085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19868699254846721318858893 7450762220567520494572085)
              ·
                refine ⟨698508958178205046366133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7450762220567520494572085 698508958178205046366133)
                ·
                  refine ⟨65485214829206723096825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 698508958178205046366133 65485214829206723096825)
                  ·
                    rfl

theorem cell23_1147788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_1147788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147788 prefixEnd_1147788 := by exact prefixLift 1147788
  have htrace : WordTrace (prefixWord ++ tailWord_1147788) baseStart_1147788 baseEnd_1147788 := by
    simpa [prefixWord, tailWord_1147788, baseEnd_1147788] using wordTrace_append hprefix tailTrace_1147788
  have hstable : (prefixWord ++ tailWord_1147788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147788).length < 2 ^ (prefixWord ++ tailWord_1147788).sum := by decide
  have hdescent : baseEnd_1147788 < baseStart_1147788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147801 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_1147801 : Nat := 118140960795 + 1147801 * 2 ^ 59
def prefixEnd_1147801 : Nat := 4983230072969 + 3 ^ 40 * 1147801 * 2
def baseEnd_1147801 : Nat := 196457869570456319002955

theorem tailTrace_1147801 : CollatzResearch.WordTrace tailWord_1147801 prefixEnd_1147801 196457869570456319002955 := by
  unfold tailWord_1147801
  simp only [CollatzResearch.WordTrace]
  refine ⟨41863741714720480649259257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27909161143146987099506171 41863741714720480649259257)
  ·
    refine ⟨31397806286040360486944443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41863741714720480649259257 31397806286040360486944443)
    ·
      refine ⟨47096709429060540730416665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31397806286040360486944443 47096709429060540730416665)
      ·
        refine ⟨35322532071795405547812499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47096709429060540730416665 35322532071795405547812499)
        ·
          refine ⟨52983798107693108321718749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35322532071795405547812499 52983798107693108321718749)
          ·
            refine ⟨19868924290384915620644531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52983798107693108321718749 19868924290384915620644531)
            ·
              refine ⟨29803386435577373430966797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19868924290384915620644531 29803386435577373430966797)
              ·
                refine ⟨11176269913341515036612549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29803386435577373430966797 11176269913341515036612549)
                ·
                  refine ⟨2095550608751534069364853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11176269913341515036612549 2095550608751534069364853)
                  ·
                    refine ⟨196457869570456319002955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2095550608751534069364853 196457869570456319002955)
                    ·
                      rfl

theorem cell23_1147801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_1147801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147801 prefixEnd_1147801 := by exact prefixLift 1147801
  have htrace : WordTrace (prefixWord ++ tailWord_1147801) baseStart_1147801 baseEnd_1147801 := by
    simpa [prefixWord, tailWord_1147801, baseEnd_1147801] using wordTrace_append hprefix tailTrace_1147801
  have hstable : (prefixWord ++ tailWord_1147801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147801).length < 2 ^ (prefixWord ++ tailWord_1147801).sum := by decide
  have hdescent : baseEnd_1147801 < baseStart_1147801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147808 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2]
def baseStart_1147808 : Nat := 118140960795 + 1147808 * 2 ^ 59
def prefixEnd_1147808 : Nat := 4983230072969 + 3 ^ 40 * 1147808 * 2
def baseEnd_1147808 : Nat := 589377203075950429621333

theorem tailTrace_1147808 : CollatzResearch.WordTrace tailWord_1147808 prefixEnd_1147808 589377203075950429621333 := by
  unfold tailWord_1147808
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931998512847560422382039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27909331350463413896509385 20931998512847560422382039)
  ·
    refine ⟨31397997769271340633573059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20931998512847560422382039 31397997769271340633573059)
    ·
      refine ⟨47096996653907010950359589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31397997769271340633573059 47096996653907010950359589)
      ·
        refine ⟨8830686872607564553192423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47096996653907010950359589 8830686872607564553192423)
        ·
          refine ⟨13246030308911346829788635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8830686872607564553192423 13246030308911346829788635)
          ·
            refine ⟨19869045463367020244682953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13246030308911346829788635 19869045463367020244682953)
            ·
              refine ⟨14901784097525265183512215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19869045463367020244682953 14901784097525265183512215)
              ·
                refine ⟨22352676146287897775268323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14901784097525265183512215 22352676146287897775268323)
                ·
                  refine ⟨33529014219431846662902485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22352676146287897775268323 33529014219431846662902485)
                  ·
                    refine ⟨785836270767933906161777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33529014219431846662902485 785836270767933906161777)
                    ·
                      refine ⟨589377203075950429621333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785836270767933906161777 589377203075950429621333)
                      ·
                        rfl

theorem cell23_1147808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_1147808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147808 prefixEnd_1147808 := by exact prefixLift 1147808
  have htrace : WordTrace (prefixWord ++ tailWord_1147808) baseStart_1147808 baseEnd_1147808 := by
    simpa [prefixWord, tailWord_1147808, baseEnd_1147808] using wordTrace_append hprefix tailTrace_1147808
  have hstable : (prefixWord ++ tailWord_1147808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147808).length < 2 ^ (prefixWord ++ tailWord_1147808).sum := by decide
  have hdescent : baseEnd_1147808 < baseStart_1147808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147811 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1147811 : Nat := 118140960795 + 1147811 * 2 ^ 59
def prefixEnd_1147811 : Nat := 4983230072969 + 3 ^ 40 * 1147811 * 2
def baseEnd_1147811 : Nat := 589378743517913917883819

theorem tailTrace_1147811 : CollatzResearch.WordTrace tailWord_1147811 prefixEnd_1147811 589378743517913917883819 := by
  unfold tailWord_1147811
  simp only [CollatzResearch.WordTrace]
  refine ⟨41864106444684252357123287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27909404296456168238082191 41864106444684252357123287)
  ·
    refine ⟨62796159667026378535684931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41864106444684252357123287 62796159667026378535684931)
    ·
      refine ⟨94194239500539567803527397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62796159667026378535684931 94194239500539567803527397)
      ·
        refine ⟨17661419906351168963161387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94194239500539567803527397 17661419906351168963161387)
        ·
          refine ⟨26492129859526753444742081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17661419906351168963161387 26492129859526753444742081)
          ·
            refine ⟨19869097394645065083556561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26492129859526753444742081 19869097394645065083556561)
            ·
              refine ⟨14901823045983798812667421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19869097394645065083556561 14901823045983798812667421)
              ·
                refine ⟨5588183642243924554750283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14901823045983798812667421 5588183642243924554750283)
                ·
                  refine ⟨8382275463365886832125425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588183642243924554750283 8382275463365886832125425)
                  ·
                    refine ⟨6286706597524415124094069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8382275463365886832125425 6286706597524415124094069)
                    ·
                      refine ⟨589378743517913917883819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6286706597524415124094069 589378743517913917883819)
                      ·
                        rfl

theorem cell23_1147811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1147811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147811 prefixEnd_1147811 := by exact prefixLift 1147811
  have htrace : WordTrace (prefixWord ++ tailWord_1147811) baseStart_1147811 baseEnd_1147811 := by
    simpa [prefixWord, tailWord_1147811, baseEnd_1147811] using wordTrace_append hprefix tailTrace_1147811
  have hstable : (prefixWord ++ tailWord_1147811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147811).length < 2 ^ (prefixWord ++ tailWord_1147811).sum := by decide
  have hdescent : baseEnd_1147811 < baseStart_1147811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147838 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1147838 : Nat := 118140960795 + 1147838 * 2 ^ 59
def prefixEnd_1147838 : Nat := 4983230072969 + 3 ^ 40 * 1147838 * 2
def baseEnd_1147838 : Nat := 589392607495585312246195

theorem tailTrace_1147838 : CollatzResearch.WordTrace tailWord_1147838 prefixEnd_1147838 589392607495585312246195 := by
  unfold tailWord_1147838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233136401948304496044521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27910060810390957312237445 5233136401948304496044521)
  ·
    refine ⟨3924852301461228372033391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5233136401948304496044521 3924852301461228372033391)
    ·
      refine ⟨5887278452191842558050087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3924852301461228372033391 5887278452191842558050087)
      ·
        refine ⟨8830917678287763837075131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887278452191842558050087 8830917678287763837075131)
        ·
          refine ⟨13246376517431645755612697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8830917678287763837075131 13246376517431645755612697)
          ·
            refine ⟨9934782388073734316709523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13246376517431645755612697 9934782388073734316709523)
            ·
              refine ⟨14902173582110601475064285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9934782388073734316709523 14902173582110601475064285)
              ·
                refine ⟨5588315093291475553149107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14902173582110601475064285 5588315093291475553149107)
                ·
                  refine ⟨8382472639937213329723661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588315093291475553149107 8382472639937213329723661)
                  ·
                    refine ⟨3143427239976454998646373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8382472639937213329723661 3143427239976454998646373)
                    ·
                      refine ⟨589392607495585312246195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3143427239976454998646373 589392607495585312246195)
                      ·
                        rfl

theorem cell23_1147838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1147838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147838 prefixEnd_1147838 := by exact prefixLift 1147838
  have htrace : WordTrace (prefixWord ++ tailWord_1147838) baseStart_1147838 baseEnd_1147838 := by
    simpa [prefixWord, tailWord_1147838, baseEnd_1147838] using wordTrace_append hprefix tailTrace_1147838
  have hstable : (prefixWord ++ tailWord_1147838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147838).length < 2 ^ (prefixWord ++ tailWord_1147838).sum := by decide
  have hdescent : baseEnd_1147838 < baseStart_1147838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147865 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_1147865 : Nat := 118140960795 + 1147865 * 2 ^ 59
def prefixEnd_1147865 : Nat := 4983230072969 + 3 ^ 40 * 1147865 * 2
def baseEnd_1147865 : Nat := 196468823824418902202857

theorem tailTrace_1147865 : CollatzResearch.WordTrace tailWord_1147865 prefixEnd_1147865 196468823824418902202857 := by
  unfold tailWord_1147865
  simp only [CollatzResearch.WordTrace]
  refine ⟨41866075986488619579589049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27910717324325746386392699 41866075986488619579589049)
  ·
    refine ⟨31399556989866464684691787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41866075986488619579589049 31399556989866464684691787)
    ·
      refine ⟨47099335484799697027037681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31399556989866464684691787 47099335484799697027037681)
      ·
        refine ⟨35324501613599772770278261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47099335484799697027037681 35324501613599772770278261)
        ·
          refine ⟨3311672026274978697213587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35324501613599772770278261 3311672026274978697213587)
          ·
            refine ⟨4967508039412468045820381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311672026274978697213587 4967508039412468045820381)
            ·
              refine ⟨1862815514779675517182643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4967508039412468045820381 1862815514779675517182643)
              ·
                refine ⟨2794223272169513275773965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862815514779675517182643 2794223272169513275773965)
                ·
                  refine ⟨1047833727063567478415237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2794223272169513275773965 1047833727063567478415237)
                  ·
                    refine ⟨196468823824418902202857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1047833727063567478415237 196468823824418902202857)
                    ·
                      rfl

theorem cell23_1147865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_1147865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147865 prefixEnd_1147865 := by exact prefixLift 1147865
  have htrace : WordTrace (prefixWord ++ tailWord_1147865) baseStart_1147865 baseEnd_1147865 := by
    simpa [prefixWord, tailWord_1147865, baseEnd_1147865] using wordTrace_append hprefix tailTrace_1147865
  have hstable : (prefixWord ++ tailWord_1147865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147865).length < 2 ^ (prefixWord ++ tailWord_1147865).sum := by decide
  have hdescent : baseEnd_1147865 < baseStart_1147865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147956 : List Nat := [2, 5, 1, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_1147956 : Nat := 118140960795 + 1147956 * 2 ^ 59
def prefixEnd_1147956 : Nat := 4983230072969 + 3 ^ 40 * 1147956 * 2
def baseEnd_1147956 : Nat := 589453198212815850570653

theorem tailTrace_1147956 : CollatzResearch.WordTrace tailWord_1147956 prefixEnd_1147956 589453198212815850570653 := by
  unfold tailWord_1147956
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934697514579471060575861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27912930019439294747434481 20934697514579471060575861)
  ·
    refine ⟨1962627891991825411928987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20934697514579471060575861 1962627891991825411928987)
    ·
      refine ⟨2943941837987738117893481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1962627891991825411928987 2943941837987738117893481)
      ·
        refine ⟨2207956378490803588420111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2943941837987738117893481 2207956378490803588420111)
        ·
          refine ⟨3311934567736205382630167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207956378490803588420111 3311934567736205382630167)
          ·
            refine ⟨4967901851604308073945251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311934567736205382630167 4967901851604308073945251)
            ·
              refine ⟨7451852777406462110917877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967901851604308073945251 7451852777406462110917877)
              ·
                refine ⟨698611197881855822898551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7451852777406462110917877 698611197881855822898551)
                ·
                  refine ⟨1047916796822783734347827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698611197881855822898551 1047916796822783734347827)
                  ·
                    refine ⟨1571875195234175601521741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047916796822783734347827 1571875195234175601521741)
                    ·
                      refine ⟨589453198212815850570653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1571875195234175601521741 589453198212815850570653)
                      ·
                        rfl

theorem cell23_1147956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_1147956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147956 prefixEnd_1147956 := by exact prefixLift 1147956
  have htrace : WordTrace (prefixWord ++ tailWord_1147956) baseStart_1147956 baseEnd_1147956 := by
    simpa [prefixWord, tailWord_1147956, baseEnd_1147956] using wordTrace_append hprefix tailTrace_1147956
  have hstable : (prefixWord ++ tailWord_1147956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147956).length < 2 ^ (prefixWord ++ tailWord_1147956).sum := by decide
  have hdescent : baseEnd_1147956 < baseStart_1147956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1147962 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4]
def baseStart_1147962 : Nat := 118140960795 + 1147962 * 2 ^ 59
def prefixEnd_1147962 : Nat := 4983230072969 + 3 ^ 40 * 1147962 * 2
def baseEnd_1147962 : Nat := 589456279096742827095625

theorem tailTrace_1147962 : CollatzResearch.WordTrace tailWord_1147962 prefixEnd_1147962 589456279096742827095625 := by
  unfold tailWord_1147962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467403466784301286467535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27913075911424803430580093 10467403466784301286467535)
  ·
    refine ⟨15701105200176451929701303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10467403466784301286467535 15701105200176451929701303)
    ·
      refine ⟨23551657800264677894551955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15701105200176451929701303 23551657800264677894551955)
      ·
        refine ⟨35327486700397016841827933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23551657800264677894551955 35327486700397016841827933)
        ·
          refine ⟨13247807512648881315685475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35327486700397016841827933 13247807512648881315685475)
          ·
            refine ⟨19871711268973321973528213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247807512648881315685475 19871711268973321973528213)
            ·
              refine ⟨931486465733124467509135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19871711268973321973528213 931486465733124467509135)
              ·
                refine ⟨1397229698599686701263703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931486465733124467509135 1397229698599686701263703)
                ·
                  refine ⟨2095844547899530051895555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397229698599686701263703 2095844547899530051895555)
                  ·
                    refine ⟨3143766821849295077843333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095844547899530051895555 3143766821849295077843333)
                    ·
                      refine ⟨589456279096742827095625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3143766821849295077843333 589456279096742827095625)
                      ·
                        rfl

theorem cell23_1147962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_1147962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1147962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1147962 prefixEnd_1147962 := by exact prefixLift 1147962
  have htrace : WordTrace (prefixWord ++ tailWord_1147962) baseStart_1147962 baseEnd_1147962 := by
    simpa [prefixWord, tailWord_1147962, baseEnd_1147962] using wordTrace_append hprefix tailTrace_1147962
  have hstable : (prefixWord ++ tailWord_1147962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1147962).length < 2 ^ (prefixWord ++ tailWord_1147962).sum := by decide
  have hdescent : baseEnd_1147962 < baseStart_1147962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1147962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148002 : List Nat := [3, 3, 2, 2, 1, 1, 4, 7]
def baseStart_1148002 : Nat := 118140960795 + 1148002 * 2 ^ 59
def prefixEnd_1148002 : Nat := 4983230072969 + 3 ^ 40 * 1148002 * 2
def baseEnd_1148002 : Nat := 21832474752700839651683

theorem tailTrace_1148002 : CollatzResearch.WordTrace tailWord_1148002 prefixEnd_1148002 21832474752700839651683 := by
  unfold tailWord_1148002
  simp only [CollatzResearch.WordTrace]
  refine ⟨10467768196748072994331565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27914048524661527984884173 10467768196748072994331565)
  ·
    refine ⟨3925413073780527372874337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10467768196748072994331565 3925413073780527372874337)
    ·
      refine ⟨2944059805335395529655753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3925413073780527372874337 2944059805335395529655753)
      ·
        refine ⟨2208044854001546647241815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2944059805335395529655753 2208044854001546647241815)
        ·
          refine ⟨3312067281002319970862723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208044854001546647241815 3312067281002319970862723)
          ·
            refine ⟨4968100921503479956294085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312067281002319970862723 4968100921503479956294085)
            ·
              refine ⟨931518922781902491805141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4968100921503479956294085 931518922781902491805141)
              ·
                refine ⟨21832474752700839651683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 931518922781902491805141 21832474752700839651683)
                ·
                  rfl

theorem cell23_1148002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 7].length) (baseStart_1148002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148002 prefixEnd_1148002 := by exact prefixLift 1148002
  have htrace : WordTrace (prefixWord ++ tailWord_1148002) baseStart_1148002 baseEnd_1148002 := by
    simpa [prefixWord, tailWord_1148002, baseEnd_1148002] using wordTrace_append hprefix tailTrace_1148002
  have hstable : (prefixWord ++ tailWord_1148002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148002).length < 2 ^ (prefixWord ++ tailWord_1148002).sum := by decide
  have hdescent : baseEnd_1148002 < baseStart_1148002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148013 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_1148013 : Nat := 118140960795 + 1148013 * 2 ^ 59
def prefixEnd_1148013 : Nat := 4983230072969 + 3 ^ 40 * 1148013 * 2
def baseEnd_1148013 : Nat := 589482466610122127557891

theorem tailTrace_1148013 : CollatzResearch.WordTrace tailWord_1148013 prefixEnd_1148013 589482466610122127557891 := by
  unfold tailWord_1148013
  simp only [CollatzResearch.WordTrace]
  refine ⟨41871473989952440855976693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27914315993301627237317795 41871473989952440855976693)
  ·
    refine ⟨3925450686558041330247815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41871473989952440855976693 3925450686558041330247815)
    ·
      refine ⟨5888176029837061995371723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925450686558041330247815 5888176029837061995371723)
      ·
        refine ⟨8832264044755592993057585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888176029837061995371723 8832264044755592993057585)
        ·
          refine ⟨6624198033566694744793189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8832264044755592993057585 6624198033566694744793189)
          ·
            refine ⟨1242037131293755264648723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6624198033566694744793189 1242037131293755264648723)
            ·
              refine ⟨1863055696940632896973085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242037131293755264648723 1863055696940632896973085)
              ·
                refine ⟨698645886352737336364907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863055696940632896973085 698645886352737336364907)
                ·
                  refine ⟨1047968829529106004547361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698645886352737336364907 1047968829529106004547361)
                  ·
                    refine ⟨785976622146829503410521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1047968829529106004547361 785976622146829503410521)
                    ·
                      refine ⟨589482466610122127557891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 785976622146829503410521 589482466610122127557891)
                      ·
                        rfl

theorem cell23_1148013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_1148013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148013 prefixEnd_1148013 := by exact prefixLift 1148013
  have htrace : WordTrace (prefixWord ++ tailWord_1148013) baseStart_1148013 baseEnd_1148013 := by
    simpa [prefixWord, tailWord_1148013, baseEnd_1148013] using wordTrace_append hprefix tailTrace_1148013
  have hstable : (prefixWord ++ tailWord_1148013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148013).length < 2 ^ (prefixWord ++ tailWord_1148013).sum := by decide
  have hdescent : baseEnd_1148013 < baseStart_1148013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148046 : List Nat := [4, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1148046 : Nat := 118140960795 + 1148046 * 2 ^ 59
def prefixEnd_1148046 : Nat := 4983230072969 + 3 ^ 40 * 1148046 * 2
def baseEnd_1148046 : Nat := 589499411471720498445239

theorem tailTrace_1148046 : CollatzResearch.WordTrace tailWord_1148046 prefixEnd_1148046 589499411471720498445239 := by
  unfold tailWord_1148046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234084699854110936490999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27915118399221924994618661 5234084699854110936490999)
  ·
    refine ⟨7851127049781166404736499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5234084699854110936490999 7851127049781166404736499)
    ·
      refine ⟨11776690574671749607104749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7851127049781166404736499 11776690574671749607104749)
      ·
        refine ⟨4416258965501906102664281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11776690574671749607104749 4416258965501906102664281)
        ·
          refine ⟨3312194224126429576998211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4416258965501906102664281 3312194224126429576998211)
          ·
            refine ⟨4968291336189644365497317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312194224126429576998211 4968291336189644365497317)
            ·
              refine ⟨931554625535558318530747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4968291336189644365497317 931554625535558318530747)
              ·
                refine ⟨1397331938303337477796121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931554625535558318530747 1397331938303337477796121)
                ·
                  refine ⟨1047998953727503108347091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1397331938303337477796121 1047998953727503108347091)
                  ·
                    refine ⟨1571998430591254662520637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1047998953727503108347091 1571998430591254662520637)
                    ·
                      refine ⟨589499411471720498445239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1571998430591254662520637 589499411471720498445239)
                      ·
                        rfl

theorem cell23_1148046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1148046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148046 prefixEnd_1148046 := by exact prefixLift 1148046
  have htrace : WordTrace (prefixWord ++ tailWord_1148046) baseStart_1148046 baseEnd_1148046 := by
    simpa [prefixWord, tailWord_1148046, baseEnd_1148046] using wordTrace_append hprefix tailTrace_1148046
  have hstable : (prefixWord ++ tailWord_1148046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148046).length < 2 ^ (prefixWord ++ tailWord_1148046).sum := by decide
  have hdescent : baseEnd_1148046 < baseStart_1148046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148055 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1148055 : Nat := 118140960795 + 1148055 * 2 ^ 59
def prefixEnd_1148055 : Nat := 4983230072969 + 3 ^ 40 * 1148055 * 2
def baseEnd_1148055 : Nat := 589504032797610963232697

theorem tailTrace_1148055 : CollatzResearch.WordTrace tailWord_1148055 prefixEnd_1148055 589504032797610963232697 := by
  unfold tailWord_1148055
  simp only [CollatzResearch.WordTrace]
  refine ⟨41873005855800282029005619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27915337237200188019337079 41873005855800282029005619)
  ·
    refine ⟨62809508783700423043508429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41873005855800282029005619 62809508783700423043508429)
    ·
      refine ⟨23553565793887658641315661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62809508783700423043508429 23553565793887658641315661)
      ·
        refine ⟨8832587172707871990493373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23553565793887658641315661 8832587172707871990493373)
        ·
          refine ⟨3312220189765451996435015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8832587172707871990493373 3312220189765451996435015)
          ·
            refine ⟨4968330284648177994652523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312220189765451996435015 4968330284648177994652523)
            ·
              refine ⟨7452495426972266991978785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4968330284648177994652523 7452495426972266991978785)
              ·
                refine ⟨5589371570229200243984089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7452495426972266991978785 5589371570229200243984089)
                ·
                  refine ⟨4192028677671900182988067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589371570229200243984089 4192028677671900182988067)
                  ·
                    refine ⟨6288043016507850274482101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192028677671900182988067 6288043016507850274482101)
                    ·
                      refine ⟨589504032797610963232697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6288043016507850274482101 589504032797610963232697)
                      ·
                        rfl

theorem cell23_1148055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1148055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148055 prefixEnd_1148055 := by exact prefixLift 1148055
  have htrace : WordTrace (prefixWord ++ tailWord_1148055) baseStart_1148055 baseEnd_1148055 := by
    simpa [prefixWord, tailWord_1148055, baseEnd_1148055] using wordTrace_append hprefix tailTrace_1148055
  have hstable : (prefixWord ++ tailWord_1148055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148055).length < 2 ^ (prefixWord ++ tailWord_1148055).sum := by decide
  have hdescent : baseEnd_1148055 < baseStart_1148055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148056 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_1148056 : Nat := 118140960795 + 1148056 * 2 ^ 59
def prefixEnd_1148056 : Nat := 4983230072969 + 3 ^ 40 * 1148056 * 2
def baseEnd_1148056 : Nat := 589504546278265459320193

theorem tailTrace_1148056 : CollatzResearch.WordTrace tailWord_1148056 prefixEnd_1148056 589504546278265459320193 := by
  unfold tailWord_1148056
  simp only [CollatzResearch.WordTrace]
  refine ⟨20936521164398329599896011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27915361552531106133194681 20936521164398329599896011)
  ·
    refine ⟨31404781746597494399844017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20936521164398329599896011 31404781746597494399844017)
    ·
      refine ⟨23553586309948120799883013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31404781746597494399844017 23553586309948120799883013)
      ·
        refine ⟨4416297433115272649978065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23553586309948120799883013 4416297433115272649978065)
        ·
          refine ⟨3312223074836454487483549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4416297433115272649978065 3312223074836454487483549)
          ·
            refine ⟨1242083653063670432806331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3312223074836454487483549 1242083653063670432806331)
            ·
              refine ⟨1863125479595505649209497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242083653063670432806331 1863125479595505649209497)
              ·
                refine ⟨1397344109696629236907123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863125479595505649209497 1397344109696629236907123)
                ·
                  refine ⟨2096016164544943855360685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397344109696629236907123 2096016164544943855360685)
                  ·
                    refine ⟨786006061704353945760257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096016164544943855360685 786006061704353945760257)
                    ·
                      refine ⟨589504546278265459320193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786006061704353945760257 589504546278265459320193)
                      ·
                        rfl

theorem cell23_1148056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_1148056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148056 prefixEnd_1148056 := by exact prefixLift 1148056
  have htrace : WordTrace (prefixWord ++ tailWord_1148056) baseStart_1148056 baseEnd_1148056 := by
    simpa [prefixWord, tailWord_1148056, baseEnd_1148056] using wordTrace_append hprefix tailTrace_1148056
  have hstable : (prefixWord ++ tailWord_1148056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148056).length < 2 ^ (prefixWord ++ tailWord_1148056).sum := by decide
  have hdescent : baseEnd_1148056 < baseStart_1148056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148142 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_1148142 : Nat := 118140960795 + 1148142 * 2 ^ 59
def prefixEnd_1148142 : Nat := 4983230072969 + 3 ^ 40 * 1148142 * 2
def baseEnd_1148142 : Nat := 589548705614552122844797

theorem tailTrace_1148142 : CollatzResearch.WordTrace tailWord_1148142 prefixEnd_1148142 589548705614552122844797 := by
  unfold tailWord_1148142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5234522375810636985927835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27917452670990063924948453 5234522375810636985927835)
  ·
    refine ⟨7851783563715955478891753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5234522375810636985927835 7851783563715955478891753)
    ·
      refine ⟨5888837672786966609168815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7851783563715955478891753 5888837672786966609168815)
      ·
        refine ⟨8833256509180449913753223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888837672786966609168815 8833256509180449913753223)
        ·
          refine ⟨13249884763770674870629835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833256509180449913753223 13249884763770674870629835)
          ·
            refine ⟨19874827145656012305944753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13249884763770674870629835 19874827145656012305944753)
            ·
              refine ⟨14906120359242009229458565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19874827145656012305944753 14906120359242009229458565)
              ·
                refine ⟨2794897567357876730523481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14906120359242009229458565 2794897567357876730523481)
                ·
                  refine ⟨2096173175518407547892611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2794897567357876730523481 2096173175518407547892611)
                  ·
                    refine ⟨3144259763277611321838917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2096173175518407547892611 3144259763277611321838917)
                    ·
                      refine ⟨589548705614552122844797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3144259763277611321838917 589548705614552122844797)
                      ·
                        rfl

theorem cell23_1148142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_1148142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148142 prefixEnd_1148142 := by exact prefixLift 1148142
  have htrace : WordTrace (prefixWord ++ tailWord_1148142) baseStart_1148142 baseEnd_1148142 := by
    simpa [prefixWord, tailWord_1148142, baseEnd_1148142] using wordTrace_append hprefix tailTrace_1148142
  have hstable : (prefixWord ++ tailWord_1148142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148142).length < 2 ^ (prefixWord ++ tailWord_1148142).sum := by decide
  have hdescent : baseEnd_1148142 < baseStart_1148142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148186 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 1, 4]
def baseStart_1148186 : Nat := 118140960795 + 1148186 * 2 ^ 59
def prefixEnd_1148186 : Nat := 4983230072969 + 3 ^ 40 * 1148186 * 2
def baseEnd_1148186 : Nat := 196523766254449983564865

theorem tailTrace_1148186 : CollatzResearch.WordTrace tailWord_1148186 prefixEnd_1148186 196523766254449983564865 := by
  unfold tailWord_1148186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10469445954581422850506103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27918522545550460934682941 10469445954581422850506103)
  ·
    refine ⟨15704168931872134275759155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10469445954581422850506103 15704168931872134275759155)
    ·
      refine ⟨23556253397808201413638733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15704168931872134275759155 23556253397808201413638733)
      ·
        refine ⟨8833595024178075530114525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23556253397808201413638733 8833595024178075530114525)
        ·
          refine ⟨3312598134066778323792947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8833595024178075530114525 3312598134066778323792947)
          ·
            refine ⟨4968897201100167485689421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312598134066778323792947 4968897201100167485689421)
            ·
              refine ⟨1863336450412562807133533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4968897201100167485689421 1863336450412562807133533)
              ·
                refine ⟨698751168904711052675075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1863336450412562807133533 698751168904711052675075)
                ·
                  refine ⟨1048126753357066579012613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698751168904711052675075 1048126753357066579012613)
                  ·
                    refine ⟨196523766254449983564865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1048126753357066579012613 196523766254449983564865)
                    ·
                      rfl

theorem cell23_1148186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 4].length) (baseStart_1148186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148186 prefixEnd_1148186 := by exact prefixLift 1148186
  have htrace : WordTrace (prefixWord ++ tailWord_1148186) baseStart_1148186 baseEnd_1148186 := by
    simpa [prefixWord, tailWord_1148186, baseEnd_1148186] using wordTrace_append hprefix tailTrace_1148186
  have hstable : (prefixWord ++ tailWord_1148186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148186).length < 2 ^ (prefixWord ++ tailWord_1148186).sum := by decide
  have hdescent : baseEnd_1148186 < baseStart_1148186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148215 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_1148215 : Nat := 118140960795 + 1148215 * 2 ^ 59
def prefixEnd_1148215 : Nat := 4983230072969 + 3 ^ 40 * 1148215 * 2
def baseEnd_1148215 : Nat := 589586189702330337231961

theorem tailTrace_1148215 : CollatzResearch.WordTrace tailWord_1148215 prefixEnd_1148215 589586189702330337231961 := by
  unfold tailWord_1148215
  simp only [CollatzResearch.WordTrace]
  refine ⟨41878841535220629354830099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27919227690147086236553399 41878841535220629354830099)
  ·
    refine ⟨62818262302830944032245149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41878841535220629354830099 62818262302830944032245149)
    ·
      refine ⟨23556848363561604012091931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62818262302830944032245149 23556848363561604012091931)
      ·
        refine ⟨35335272545342406018137897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23556848363561604012091931 35335272545342406018137897)
        ·
          refine ⟨26501454409006804513603423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35335272545342406018137897 26501454409006804513603423)
          ·
            refine ⟨39752181613510206770405135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26501454409006804513603423 39752181613510206770405135)
            ·
              refine ⟨59628272420265310155607703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39752181613510206770405135 59628272420265310155607703)
              ·
                refine ⟨89442408630397965233411555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59628272420265310155607703 89442408630397965233411555)
                ·
                  refine ⟨134163612945596947850117333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89442408630397965233411555 134163612945596947850117333)
                  ·
                    refine ⟨3144459678412428465237125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134163612945596947850117333 3144459678412428465237125)
                    ·
                      refine ⟨589586189702330337231961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3144459678412428465237125 589586189702330337231961)
                      ·
                        rfl

theorem cell23_1148215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_1148215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148215 prefixEnd_1148215 := by exact prefixLift 1148215
  have htrace : WordTrace (prefixWord ++ tailWord_1148215) baseStart_1148215 baseEnd_1148215 := by
    simpa [prefixWord, tailWord_1148215, baseEnd_1148215] using wordTrace_append hprefix tailTrace_1148215
  have hstable : (prefixWord ++ tailWord_1148215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148215).length < 2 ^ (prefixWord ++ tailWord_1148215).sum := by decide
  have hdescent : baseEnd_1148215 < baseStart_1148215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148230 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_1148230 : Nat := 118140960795 + 1148230 * 2 ^ 59
def prefixEnd_1148230 : Nat := 4983230072969 + 3 ^ 40 * 1148230 * 2
def baseEnd_1148230 : Nat := 589593891912147778544393

theorem tailTrace_1148230 : CollatzResearch.WordTrace tailWord_1148230 prefixEnd_1148230 589593891912147778544393 := by
  unfold tailWord_1148230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1308730894692696466144567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27919592420110857944417429 1308730894692696466144567)
  ·
    refine ⟨1963096342039044699216851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1308730894692696466144567 1963096342039044699216851)
    ·
      refine ⟨2944644513058567048825277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1963096342039044699216851 2944644513058567048825277)
      ·
        refine ⟨1104241692396962643309479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2944644513058567048825277 1104241692396962643309479)
        ·
          refine ⟨1656362538595443964964219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104241692396962643309479 1656362538595443964964219)
          ·
            refine ⟨2484543807893165947446329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656362538595443964964219 2484543807893165947446329)
            ·
              refine ⟨1863407855919874460584747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484543807893165947446329 1863407855919874460584747)
              ·
                refine ⟨2795111783879811690877121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863407855919874460584747 2795111783879811690877121)
                ·
                  refine ⟨2096333837909858768157841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795111783879811690877121 2096333837909858768157841)
                  ·
                    refine ⟨1572250378432394076118381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2096333837909858768157841 1572250378432394076118381)
                    ·
                      refine ⟨589593891912147778544393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572250378432394076118381 589593891912147778544393)
                      ·
                        rfl

theorem cell23_1148230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_1148230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148230 prefixEnd_1148230 := by exact prefixLift 1148230
  have htrace : WordTrace (prefixWord ++ tailWord_1148230) baseStart_1148230 baseEnd_1148230 := by
    simpa [prefixWord, tailWord_1148230, baseEnd_1148230] using wordTrace_append hprefix tailTrace_1148230
  have hstable : (prefixWord ++ tailWord_1148230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148230).length < 2 ^ (prefixWord ++ tailWord_1148230).sum := by decide
  have hdescent : baseEnd_1148230 < baseStart_1148230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148236 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_1148236 : Nat := 118140960795 + 1148236 * 2 ^ 59
def prefixEnd_1148236 : Nat := 4983230072969 + 3 ^ 40 * 1148236 * 2
def baseEnd_1148236 : Nat := 589596972796074755069365

theorem tailTrace_1148236 : CollatzResearch.WordTrace tailWord_1148236 prefixEnd_1148236 589596972796074755069365 := by
  unfold tailWord_1148236
  simp only [CollatzResearch.WordTrace]
  refine ⟨20939803734072274970672281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27919738312096366627563041 20939803734072274970672281)
  ·
    refine ⟨15704852800554206228004211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20939803734072274970672281 15704852800554206228004211)
    ·
      refine ⟨23557279200831309342006317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15704852800554206228004211 23557279200831309342006317)
      ·
        refine ⟨8833979700311741003252369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23557279200831309342006317 8833979700311741003252369)
        ·
          refine ⟨6625484775233805752439277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8833979700311741003252369 6625484775233805752439277)
          ·
            refine ⟨2484556790712677157164729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6625484775233805752439277 2484556790712677157164729)
            ·
              refine ⟨1863417593034507867873547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2484556790712677157164729 1863417593034507867873547)
              ·
                refine ⟨2795126389551761801810321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863417593034507867873547 2795126389551761801810321)
                ·
                  refine ⟨2096344792163821351357741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795126389551761801810321 2096344792163821351357741)
                  ·
                    refine ⟨786129297061433006759153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2096344792163821351357741 786129297061433006759153)
                    ·
                      refine ⟨589596972796074755069365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786129297061433006759153 589596972796074755069365)
                      ·
                        rfl

theorem cell23_1148236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_1148236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148236 prefixEnd_1148236 := by exact prefixLift 1148236
  have htrace : WordTrace (prefixWord ++ tailWord_1148236) baseStart_1148236 baseEnd_1148236 := by
    simpa [prefixWord, tailWord_1148236, baseEnd_1148236] using wordTrace_append hprefix tailTrace_1148236
  have hstable : (prefixWord ++ tailWord_1148236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148236).length < 2 ^ (prefixWord ++ tailWord_1148236).sum := by decide
  have hdescent : baseEnd_1148236 < baseStart_1148236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148259 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 2, 4]
def baseStart_1148259 : Nat := 118140960795 + 1148259 * 2 ^ 59
def prefixEnd_1148259 : Nat := 4983230072969 + 3 ^ 40 * 1148259 * 2
def baseEnd_1148259 : Nat := 196536260950376055027253

theorem tailTrace_1148259 : CollatzResearch.WordTrace tailWord_1148259 prefixEnd_1148259 196536260950376055027253 := by
  unfold tailWord_1148259
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880446347061224869431831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27920297564707483246287887 41880446347061224869431831)
  ·
    refine ⟨62820669520591837304147747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41880446347061224869431831 62820669520591837304147747)
    ·
      refine ⟨94231004280887755956221621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62820669520591837304147747 94231004280887755956221621)
      ·
        refine ⟨8834156651333227120895777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94231004280887755956221621 8834156651333227120895777)
        ·
          refine ⟨6625617488499920340671833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8834156651333227120895777 6625617488499920340671833)
          ·
            refine ⟨4969213116374940255503875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6625617488499920340671833 4969213116374940255503875)
            ·
              refine ⟨7453819674562410383255813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969213116374940255503875 7453819674562410383255813)
              ·
                refine ⟨1397591188980451946860465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7453819674562410383255813 1397591188980451946860465)
                ·
                  refine ⟨1048193391735338960145349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1397591188980451946860465 1048193391735338960145349)
                  ·
                    refine ⟨196536260950376055027253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1048193391735338960145349 196536260950376055027253)
                    ·
                      rfl

theorem cell23_1148259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 4].length) (baseStart_1148259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148259 prefixEnd_1148259 := by exact prefixLift 1148259
  have htrace : WordTrace (prefixWord ++ tailWord_1148259) baseStart_1148259 baseEnd_1148259 := by
    simpa [prefixWord, tailWord_1148259, baseEnd_1148259] using wordTrace_append hprefix tailTrace_1148259
  have hstable : (prefixWord ++ tailWord_1148259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148259).length < 2 ^ (prefixWord ++ tailWord_1148259).sum := by decide
  have hdescent : baseEnd_1148259 < baseStart_1148259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148260 : List Nat := [2, 3, 1, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_1148260 : Nat := 118140960795 + 1148260 * 2 ^ 59
def prefixEnd_1148260 : Nat := 4983230072969 + 3 ^ 40 * 1148260 * 2
def baseEnd_1148260 : Nat := 589609296331782661169255

theorem tailTrace_1148260 : CollatzResearch.WordTrace tailWord_1148260 prefixEnd_1148260 589609296331782661169255 := by
  unfold tailWord_1148260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940241410028801020109117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27920321880038401360145489 20940241410028801020109117)
  ·
    refine ⟨7852590528760800382540919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20940241410028801020109117 7852590528760800382540919)
    ·
      refine ⟨11778885793141200573811379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7852590528760800382540919 11778885793141200573811379)
      ·
        refine ⟨17668328689711800860717069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11778885793141200573811379 17668328689711800860717069)
        ·
          refine ⟨6625623258641925322768901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17668328689711800860717069 6625623258641925322768901)
          ·
            refine ⟨1242304360995360998019169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6625623258641925322768901 1242304360995360998019169)
            ·
              refine ⟨931728270746520748514377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242304360995360998019169 931728270746520748514377)
              ·
                refine ⟨698796203059890561385783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931728270746520748514377 698796203059890561385783)
                ·
                  refine ⟨1048194304589835842078675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698796203059890561385783 1048194304589835842078675)
                  ·
                    refine ⟨1572291456884753763118013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1048194304589835842078675 1572291456884753763118013)
                    ·
                      refine ⟨589609296331782661169255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572291456884753763118013 589609296331782661169255)
                      ·
                        rfl

theorem cell23_1148260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_1148260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148260 prefixEnd_1148260 := by exact prefixLift 1148260
  have htrace : WordTrace (prefixWord ++ tailWord_1148260) baseStart_1148260 baseEnd_1148260 := by
    simpa [prefixWord, tailWord_1148260, baseEnd_1148260] using wordTrace_append hprefix tailTrace_1148260
  have hstable : (prefixWord ++ tailWord_1148260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148260).length < 2 ^ (prefixWord ++ tailWord_1148260).sum := by decide
  have hdescent : baseEnd_1148260 < baseStart_1148260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148265 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 7]
def baseStart_1148265 : Nat := 118140960795 + 1148265 * 2 ^ 59
def prefixEnd_1148265 : Nat := 4983230072969 + 3 ^ 40 * 1148265 * 2
def baseEnd_1148265 : Nat := 589611863735055141606731

theorem tailTrace_1148265 : CollatzResearch.WordTrace tailWord_1148265 prefixEnd_1148265 589611863735055141606731 := by
  unfold tailWord_1148265
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880665185039487894150249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27920443456692991929433499 41880665185039487894150249)
  ·
    refine ⟨31410498888779615920612687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41880665185039487894150249 31410498888779615920612687)
    ·
      refine ⟨47115748333169423880919031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31410498888779615920612687 47115748333169423880919031)
      ·
        refine ⟨70673622499754135821378547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47115748333169423880919031 70673622499754135821378547)
        ·
          refine ⟨106010433749631203732067821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70673622499754135821378547 106010433749631203732067821)
          ·
            refine ⟨39753912656111701399525433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106010433749631203732067821 39753912656111701399525433)
            ·
              refine ⟨29815434492083776049644075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39753912656111701399525433 29815434492083776049644075)
              ·
                refine ⟨44723151738125664074466113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29815434492083776049644075 44723151738125664074466113)
                ·
                  refine ⟨33542363803594248055849585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44723151738125664074466113 33542363803594248055849585)
                  ·
                    refine ⟨25156772852695686041887189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33542363803594248055849585 25156772852695686041887189)
                    ·
                      refine ⟨589611863735055141606731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 25156772852695686041887189 589611863735055141606731)
                      ·
                        rfl

theorem cell23_1148265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_1148265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148265 prefixEnd_1148265 := by exact prefixLift 1148265
  have htrace : WordTrace (prefixWord ++ tailWord_1148265) baseStart_1148265 baseEnd_1148265 := by
    simpa [prefixWord, tailWord_1148265, baseEnd_1148265] using wordTrace_append hprefix tailTrace_1148265
  have hstable : (prefixWord ++ tailWord_1148265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148265).length < 2 ^ (prefixWord ++ tailWord_1148265).sum := by decide
  have hdescent : baseEnd_1148265 < baseStart_1148265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148269 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1148269 : Nat := 118140960795 + 1148269 * 2 ^ 59
def prefixEnd_1148269 : Nat := 4983230072969 + 3 ^ 40 * 1148269 * 2
def baseEnd_1148269 : Nat := 589613917657673125956713

theorem tailTrace_1148269 : CollatzResearch.WordTrace tailWord_1148269 prefixEnd_1148269 589613917657673125956713 := by
  unfold tailWord_1148269
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880811077024996577295861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27920540718016664384863907 41880811077024996577295861)
  ·
    refine ⟨3926326038471093429121487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41880811077024996577295861 3926326038471093429121487)
    ·
      refine ⟨5889489057706640143682231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3926326038471093429121487 5889489057706640143682231)
      ·
        refine ⟨8834233586559960215523347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5889489057706640143682231 8834233586559960215523347)
        ·
          refine ⟨13251350379839940323285021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8834233586559960215523347 13251350379839940323285021)
          ·
            refine ⟨4969256392439977621231883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13251350379839940323285021 4969256392439977621231883)
            ·
              refine ⟨7453884588659966431847825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969256392439977621231883 7453884588659966431847825)
              ·
                refine ⟨5590413441494974823885869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7453884588659966431847825 5590413441494974823885869)
                ·
                  refine ⟨2096405040560615558957201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5590413441494974823885869 2096405040560615558957201)
                  ·
                    refine ⟨1572303780420461669217901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2096405040560615558957201 1572303780420461669217901)
                    ·
                      refine ⟨589613917657673125956713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572303780420461669217901 589613917657673125956713)
                      ·
                        rfl

theorem cell23_1148269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1148269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148269 prefixEnd_1148269 := by exact prefixLift 1148269
  have htrace : WordTrace (prefixWord ++ tailWord_1148269) baseStart_1148269 baseEnd_1148269 := by
    simpa [prefixWord, tailWord_1148269, baseEnd_1148269] using wordTrace_append hprefix tailTrace_1148269
  have hstable : (prefixWord ++ tailWord_1148269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148269).length < 2 ^ (prefixWord ++ tailWord_1148269).sum := by decide
  have hdescent : baseEnd_1148269 < baseStart_1148269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148282 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3]
def baseStart_1148282 : Nat := 118140960795 + 1148282 * 2 ^ 59
def prefixEnd_1148282 : Nat := 4983230072969 + 3 ^ 40 * 1148282 * 2
def baseEnd_1148282 : Nat := 589620592906181575094153

theorem tailTrace_1148282 : CollatzResearch.WordTrace tailWord_1148282 prefixEnd_1148282 589620592906181575094153 := by
  unfold tailWord_1148282
  simp only [CollatzResearch.WordTrace]
  refine ⟨10470321306494474949379775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27920856817318599865012733 10470321306494474949379775)
  ·
    refine ⟨15705481959741712424069663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10470321306494474949379775 15705481959741712424069663)
    ·
      refine ⟨23558222939612568636104495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15705481959741712424069663 23558222939612568636104495)
      ·
        refine ⟨35337334409418852954156743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23558222939612568636104495 35337334409418852954156743)
        ·
          refine ⟨53006001614128279431235115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35337334409418852954156743 53006001614128279431235115)
          ·
            refine ⟨79509002421192419146852673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53006001614128279431235115 79509002421192419146852673)
            ·
              refine ⟨59631751815894314360139505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79509002421192419146852673 59631751815894314360139505)
              ·
                refine ⟨44723813861920735770104629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59631751815894314360139505 44723813861920735770104629)
                ·
                  refine ⟨4192857549555068978447309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44723813861920735770104629 4192857549555068978447309)
                  ·
                    refine ⟨1572321581083150866917741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4192857549555068978447309 1572321581083150866917741)
                    ·
                      refine ⟨589620592906181575094153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572321581083150866917741 589620592906181575094153)
                      ·
                        rfl

theorem cell23_1148282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_1148282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148282 prefixEnd_1148282 := by exact prefixLift 1148282
  have htrace : WordTrace (prefixWord ++ tailWord_1148282) baseStart_1148282 baseEnd_1148282 := by
    simpa [prefixWord, tailWord_1148282, baseEnd_1148282] using wordTrace_append hprefix tailTrace_1148282
  have hstable : (prefixWord ++ tailWord_1148282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148282).length < 2 ^ (prefixWord ++ tailWord_1148282).sum := by decide
  have hdescent : baseEnd_1148282 < baseStart_1148282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148299 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 3]
def baseStart_1148299 : Nat := 118140960795 + 1148299 * 2 ^ 59
def prefixEnd_1148299 : Nat := 4983230072969 + 3 ^ 40 * 1148299 * 2
def baseEnd_1148299 : Nat := 589629322077308008581575

theorem tailTrace_1148299 : CollatzResearch.WordTrace tailWord_1148299 prefixEnd_1148299 589629322077308008581575 := by
  unfold tailWord_1148299
  simp only [CollatzResearch.WordTrace]
  refine ⟨41881905266916311700887951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27921270177944207800591967 41881905266916311700887951)
  ·
    refine ⟨62822857900374467551331927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41881905266916311700887951 62822857900374467551331927)
    ·
      refine ⟨94234286850561701326997891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62822857900374467551331927 94234286850561701326997891)
      ·
        refine ⟨141351430275842551990496837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94234286850561701326997891 141351430275842551990496837)
        ·
          refine ⟨26503393176720478498218157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141351430275842551990496837 26503393176720478498218157)
          ·
            refine ⟨9938772441270179436831809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26503393176720478498218157 9938772441270179436831809)
            ·
              refine ⟨7454079330952634577623857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9938772441270179436831809 7454079330952634577623857)
              ·
                refine ⟨5590559498214475933217893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7454079330952634577623857 5590559498214475933217893)
                ·
                  refine ⟨1048229905915214237478355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5590559498214475933217893 1048229905915214237478355)
                  ·
                    refine ⟨1572344858872821356217533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1048229905915214237478355 1572344858872821356217533)
                    ·
                      refine ⟨589629322077308008581575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572344858872821356217533 589629322077308008581575)
                      ·
                        rfl

theorem cell23_1148299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 4, 1, 3].length) (baseStart_1148299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148299 prefixEnd_1148299 := by exact prefixLift 1148299
  have htrace : WordTrace (prefixWord ++ tailWord_1148299) baseStart_1148299 baseEnd_1148299 := by
    simpa [prefixWord, tailWord_1148299, baseEnd_1148299] using wordTrace_append hprefix tailTrace_1148299
  have hstable : (prefixWord ++ tailWord_1148299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148299).length < 2 ^ (prefixWord ++ tailWord_1148299).sum := by decide
  have hdescent : baseEnd_1148299 < baseStart_1148299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148332 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_1148332 : Nat := 118140960795 + 1148332 * 2 ^ 59
def prefixEnd_1148332 : Nat := 4983230072969 + 3 ^ 40 * 1148332 * 2
def baseEnd_1148332 : Nat := 196548755646302126489641

theorem tailTrace_1148332 : CollatzResearch.WordTrace tailWord_1148332 prefixEnd_1148332 196548755646302126489641 := by
  unfold tailWord_1148332
  simp only [CollatzResearch.WordTrace]
  refine ⟨20941554437898379168419625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27922072583864505557892833 20941554437898379168419625)
  ·
    refine ⟨15706165828423784376314719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20941554437898379168419625 15706165828423784376314719)
    ·
      refine ⟨23559248742635676564472079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15706165828423784376314719 23559248742635676564472079)
      ·
        refine ⟨35338873113953514846708119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23559248742635676564472079 35338873113953514846708119)
        ·
          refine ⟨53008309670930272270062179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35338873113953514846708119 53008309670930272270062179)
          ·
            refine ⟨79512464506395408405093269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53008309670930272270062179 79512464506395408405093269)
            ·
              refine ⟨3727146773737284768988747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79512464506395408405093269 3727146773737284768988747)
              ·
                refine ⟨5590720160605927153483121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727146773737284768988747 5590720160605927153483121)
                ·
                  refine ⟨4193040120454445365112341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5590720160605927153483121 4193040120454445365112341)
                  ·
                    refine ⟨196548755646302126489641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4193040120454445365112341 196548755646302126489641)
                    ·
                      rfl

theorem cell23_1148332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_1148332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148332 prefixEnd_1148332 := by exact prefixLift 1148332
  have htrace : WordTrace (prefixWord ++ tailWord_1148332) baseStart_1148332 baseEnd_1148332 := by
    simpa [prefixWord, tailWord_1148332, baseEnd_1148332] using wordTrace_append hprefix tailTrace_1148332
  have hstable : (prefixWord ++ tailWord_1148332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148332).length < 2 ^ (prefixWord ++ tailWord_1148332).sum := by decide
  have hdescent : baseEnd_1148332 < baseStart_1148332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148333 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1148333 : Nat := 118140960795 + 1148333 * 2 ^ 59
def prefixEnd_1148333 : Nat := 4983230072969 + 3 ^ 40 * 1148333 * 2
def baseEnd_1148333 : Nat := 589646780419560875556419

theorem tailTrace_1148333 : CollatzResearch.WordTrace tailWord_1148333 prefixEnd_1148333 589646780419560875556419 := by
  unfold tailWord_1148333
  simp only [CollatzResearch.WordTrace]
  refine ⟨41883145348793135507625653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27922096899195423671750435 41883145348793135507625653)
  ·
    refine ⟨3926544876449356453839905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41883145348793135507625653 3926544876449356453839905)
    ·
      refine ⟨2944908657337017340379929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3926544876449356453839905 2944908657337017340379929)
      ·
        refine ⟨2208681493002763005284947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2944908657337017340379929 2208681493002763005284947)
        ·
          refine ⟨3313022239504144507927421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208681493002763005284947 3313022239504144507927421)
          ·
            refine ⟨1242383339814054190472783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3313022239504144507927421 1242383339814054190472783)
            ·
              refine ⟨1863575009721081285709175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1242383339814054190472783 1863575009721081285709175)
              ·
                refine ⟨2795362514581621928563763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863575009721081285709175 2795362514581621928563763)
                ·
                  refine ⟨4193043771872432892845645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795362514581621928563763 4193043771872432892845645)
                  ·
                    refine ⟨1572391414452162334817117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4193043771872432892845645 1572391414452162334817117)
                    ·
                      refine ⟨589646780419560875556419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572391414452162334817117 589646780419560875556419)
                      ·
                        rfl

theorem cell23_1148333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1148333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148333 prefixEnd_1148333 := by exact prefixLift 1148333
  have htrace : WordTrace (prefixWord ++ tailWord_1148333) baseStart_1148333 baseEnd_1148333 := by
    simpa [prefixWord, tailWord_1148333, baseEnd_1148333] using wordTrace_append hprefix tailTrace_1148333
  have hstable : (prefixWord ++ tailWord_1148333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148333).length < 2 ^ (prefixWord ++ tailWord_1148333).sum := by decide
  have hdescent : baseEnd_1148333 < baseStart_1148333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148352 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_1148352 : Nat := 118140960795 + 1148352 * 2 ^ 59
def prefixEnd_1148352 : Nat := 4983230072969 + 3 ^ 40 * 1148352 * 2
def baseEnd_1148352 : Nat := 589656536551996301218831

theorem tailTrace_1148352 : CollatzResearch.WordTrace tailWord_1148352 prefixEnd_1148352 589656536551996301218831 := by
  unfold tailWord_1148352
  simp only [CollatzResearch.WordTrace]
  refine ⟨20941919167862150876283655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27922558890482867835044873 20941919167862150876283655)
  ·
    refine ⟨31412878751793226314425483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20941919167862150876283655 31412878751793226314425483)
    ·
      refine ⟨47119318127689839471638225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31412878751793226314425483 47119318127689839471638225)
      ·
        refine ⟨35339488595767379603728669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47119318127689839471638225 35339488595767379603728669)
        ·
          refine ⟨13252308223412767351398251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35339488595767379603728669 13252308223412767351398251)
          ·
            refine ⟨19878462335119151027097377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13252308223412767351398251 19878462335119151027097377)
            ·
              refine ⟨14908846751339363270323033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19878462335119151027097377 14908846751339363270323033)
              ·
                refine ⟨11181635063504522452742275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14908846751339363270323033 11181635063504522452742275)
                ·
                  refine ⟨16772452595256783679113413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11181635063504522452742275 16772452595256783679113413)
                  ·
                    refine ⟨3144834861610646939833765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16772452595256783679113413 3144834861610646939833765)
                    ·
                      refine ⟨589656536551996301218831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3144834861610646939833765 589656536551996301218831)
                      ·
                        rfl

theorem cell23_1148352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_1148352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148352 prefixEnd_1148352 := by exact prefixLift 1148352
  have htrace : WordTrace (prefixWord ++ tailWord_1148352) baseStart_1148352 baseEnd_1148352 := by
    simpa [prefixWord, tailWord_1148352, baseEnd_1148352] using wordTrace_append hprefix tailTrace_1148352
  have hstable : (prefixWord ++ tailWord_1148352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148352).length < 2 ^ (prefixWord ++ tailWord_1148352).sum := by decide
  have hdescent : baseEnd_1148352 < baseStart_1148352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148373 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1148373 : Nat := 118140960795 + 1148373 * 2 ^ 59
def prefixEnd_1148373 : Nat := 4983230072969 + 3 ^ 40 * 1148373 * 2
def baseEnd_1148373 : Nat := 589667319645740719056235

theorem tailTrace_1148373 : CollatzResearch.WordTrace tailWord_1148373 prefixEnd_1148373 589667319645740719056235 := by
  unfold tailWord_1148373
  simp only [CollatzResearch.WordTrace]
  refine ⟨41884604268648222339081773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27923069512432148226054515 41884604268648222339081773)
  ·
    refine ⟨15706726600743083377155665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41884604268648222339081773 15706726600743083377155665)
    ·
      refine ⟨11780044950557312532866749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15706726600743083377155665 11780044950557312532866749)
      ·
        refine ⟨4417516856458992199825031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11780044950557312532866749 4417516856458992199825031)
        ·
          refine ⟨6626275284688488299737547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4417516856458992199825031 6626275284688488299737547)
          ·
            refine ⟨9939412927032732449606321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6626275284688488299737547 9939412927032732449606321)
            ·
              refine ⟨7454559695274549337204741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9939412927032732449606321 7454559695274549337204741)
              ·
                refine ⟨1397729942863978000725889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7454559695274549337204741 1397729942863978000725889)
                ·
                  refine ⟨1048297457147983500544417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1397729942863978000725889 1048297457147983500544417)
                  ·
                    refine ⟨786223092860987625408313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1048297457147983500544417 786223092860987625408313)
                    ·
                      refine ⟨589667319645740719056235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786223092860987625408313 589667319645740719056235)
                      ·
                        rfl

theorem cell23_1148373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1148373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148373 prefixEnd_1148373 := by exact prefixLift 1148373
  have htrace : WordTrace (prefixWord ++ tailWord_1148373) baseStart_1148373 baseEnd_1148373 := by
    simpa [prefixWord, tailWord_1148373, baseEnd_1148373] using wordTrace_append hprefix tailTrace_1148373
  have hstable : (prefixWord ++ tailWord_1148373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148373).length < 2 ^ (prefixWord ++ tailWord_1148373).sum := by decide
  have hdescent : baseEnd_1148373 < baseStart_1148373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148430 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_1148430 : Nat := 118140960795 + 1148430 * 2 ^ 59
def prefixEnd_1148430 : Nat := 4983230072969 + 3 ^ 40 * 1148430 * 2
def baseEnd_1148430 : Nat := 65521843115894110671497

theorem tailTrace_1148430 : CollatzResearch.WordTrace tailWord_1148430 prefixEnd_1148430 65521843115894110671497 := by
  unfold tailWord_1148430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5235835403680215134238343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27924455486294480715937829 5235835403680215134238343)
  ·
    refine ⟨7853753105520322701357515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5235835403680215134238343 7853753105520322701357515)
    ·
      refine ⟨11780629658280484052036273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7853753105520322701357515 11780629658280484052036273)
      ·
        refine ⟨8835472243710363039027205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11780629658280484052036273 8835472243710363039027205)
        ·
          refine ⟨1656651045695693069817601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8835472243710363039027205 1656651045695693069817601)
          ·
            refine ⟨1242488284271769802363201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1656651045695693069817601 1242488284271769802363201)
            ·
              refine ⟨931866213203827351772401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1242488284271769802363201 931866213203827351772401)
              ·
                refine ⟨698899659902870513829301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 931866213203827351772401 698899659902870513829301)
                ·
                  refine ⟨65521843115894110671497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 698899659902870513829301 65521843115894110671497)
                  ·
                    rfl

theorem cell23_1148430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_1148430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148430 prefixEnd_1148430 := by exact prefixLift 1148430
  have htrace : WordTrace (prefixWord ++ tailWord_1148430) baseStart_1148430 baseEnd_1148430 := by
    simpa [prefixWord, tailWord_1148430, baseEnd_1148430] using wordTrace_append hprefix tailTrace_1148430
  have hstable : (prefixWord ++ tailWord_1148430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148430).length < 2 ^ (prefixWord ++ tailWord_1148430).sum := by decide
  have hdescent : baseEnd_1148430 < baseStart_1148430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148473 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 1, 4]
def baseStart_1148473 : Nat := 118140960795 + 1148473 * 2 ^ 59
def prefixEnd_1148473 : Nat := 4983230072969 + 3 ^ 40 * 1148473 * 2
def baseEnd_1148473 : Nat := 196572889237063442601925

theorem tailTrace_1148473 : CollatzResearch.WordTrace tailWord_1148473 prefixEnd_1148473 196572889237063442601925 := by
  unfold tailWord_1148473
  simp only [CollatzResearch.WordTrace]
  refine ⟨41888251568285939417722073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27925501045523959611814715 41888251568285939417722073)
  ·
    refine ⟨31416188676214454563291555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41888251568285939417722073 31416188676214454563291555)
    ·
      refine ⟨47124283014321681844937333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31416188676214454563291555 47124283014321681844937333)
      ·
        refine ⟨4417901532592657672962875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47124283014321681844937333 4417901532592657672962875)
        ·
          refine ⟨6626852298888986509444313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4417901532592657672962875 6626852298888986509444313)
          ·
            refine ⟨4970139224166739882083235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6626852298888986509444313 4970139224166739882083235)
            ·
              refine ⟨7455208836250109823124853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970139224166739882083235 7455208836250109823124853)
              ·
                refine ⟨698925828398447795917955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7455208836250109823124853 698925828398447795917955)
                ·
                  refine ⟨1048388742597671693876933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 698925828398447795917955 1048388742597671693876933)
                  ·
                    refine ⟨196572889237063442601925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1048388742597671693876933 196572889237063442601925)
                    ·
                      rfl

theorem cell23_1148473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 4].length) (baseStart_1148473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148473 prefixEnd_1148473 := by exact prefixLift 1148473
  have htrace : WordTrace (prefixWord ++ tailWord_1148473) baseStart_1148473 baseEnd_1148473 := by
    simpa [prefixWord, tailWord_1148473, baseEnd_1148473] using wordTrace_append hprefix tailTrace_1148473
  have hstable : (prefixWord ++ tailWord_1148473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148473).length < 2 ^ (prefixWord ++ tailWord_1148473).sum := by decide
  have hdescent : baseEnd_1148473 < baseStart_1148473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148516 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_1148516 : Nat := 118140960795 + 1148516 * 2 ^ 59
def prefixEnd_1148516 : Nat := 4983230072969 + 3 ^ 40 * 1148516 * 2
def baseEnd_1148516 : Nat := 196580249126444553189359

theorem tailTrace_1148516 : CollatzResearch.WordTrace tailWord_1148516 prefixEnd_1148516 196580249126444553189359 := by
  unfold tailWord_1148516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20944909953565078880768701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27926546604753438507691601 20944909953565078880768701)
  ·
    refine ⟨7854341232586904580288263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20944909953565078880768701 7854341232586904580288263)
    ·
      refine ⟨11781511848880356870432395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7854341232586904580288263 11781511848880356870432395)
      ·
        refine ⟨17672267773320535305648593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11781511848880356870432395 17672267773320535305648593)
        ·
          refine ⟨13254200829990401479236445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17672267773320535305648593 13254200829990401479236445)
          ·
            refine ⟨4970325311246400554713667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13254200829990401479236445 4970325311246400554713667)
            ·
              refine ⟨7455487966869600832070501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970325311246400554713667 7455487966869600832070501)
              ·
                refine ⟨1397903993788050156013219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7455487966869600832070501 1397903993788050156013219)
                ·
                  refine ⟨2096855990682075234019829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397903993788050156013219 2096855990682075234019829)
                  ·
                    refine ⟨196580249126444553189359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2096855990682075234019829 196580249126444553189359)
                    ·
                      rfl

theorem cell23_1148516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_1148516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148516 prefixEnd_1148516 := by exact prefixLift 1148516
  have htrace : WordTrace (prefixWord ++ tailWord_1148516) baseStart_1148516 baseEnd_1148516 := by
    simpa [prefixWord, tailWord_1148516, baseEnd_1148516] using wordTrace_append hprefix tailTrace_1148516
  have hstable : (prefixWord ++ tailWord_1148516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148516).length < 2 ^ (prefixWord ++ tailWord_1148516).sum := by decide
  have hdescent : baseEnd_1148516 < baseStart_1148516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148529 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_1148529 : Nat := 118140960795 + 1148529 * 2 ^ 59
def prefixEnd_1148529 : Nat := 4983230072969 + 3 ^ 40 * 1148529 * 2
def baseEnd_1148529 : Nat := 196582474209280702901839

theorem tailTrace_1148529 : CollatzResearch.WordTrace tailWord_1148529 prefixEnd_1148529 196582474209280702901839 := by
  unfold tailWord_1148529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41890294056083060981760641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27926862704055373987840427 41890294056083060981760641)
  ·
    refine ⟨31417720542062295736320481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41890294056083060981760641 31417720542062295736320481)
    ·
      refine ⟨23563290406546721802240361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31417720542062295736320481 23563290406546721802240361)
      ·
        refine ⟨17672467804910041351680271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23563290406546721802240361 17672467804910041351680271)
        ·
          refine ⟨26508701707365062027520407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17672467804910041351680271 26508701707365062027520407)
          ·
            refine ⟨39763052561047593041280611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26508701707365062027520407 39763052561047593041280611)
            ·
              refine ⟨59644578841571389561920917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39763052561047593041280611 59644578841571389561920917)
              ·
                refine ⟨2795839633198658885715043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59644578841571389561920917 2795839633198658885715043)
                ·
                  refine ⟨4193759449797988328572565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795839633198658885715043 4193759449797988328572565)
                  ·
                    refine ⟨196582474209280702901839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4193759449797988328572565 196582474209280702901839)
                    ·
                      rfl

theorem cell23_1148529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_1148529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148529 prefixEnd_1148529 := by exact prefixLift 1148529
  have htrace : WordTrace (prefixWord ++ tailWord_1148529) baseStart_1148529 baseEnd_1148529 := by
    simpa [prefixWord, tailWord_1148529, baseEnd_1148529] using wordTrace_append hprefix tailTrace_1148529
  have hstable : (prefixWord ++ tailWord_1148529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148529).length < 2 ^ (prefixWord ++ tailWord_1148529).sum := by decide
  have hdescent : baseEnd_1148529 < baseStart_1148529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148533 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1148533 : Nat := 118140960795 + 1148533 * 2 ^ 59
def prefixEnd_1148533 : Nat := 4983230072969 + 3 ^ 40 * 1148533 * 2
def baseEnd_1148533 : Nat := 196583158850153364351833

theorem tailTrace_1148533 : CollatzResearch.WordTrace tailWord_1148533 prefixEnd_1148533 196583158850153364351833 := by
  unfold tailWord_1148533
  simp only [CollatzResearch.WordTrace]
  refine ⟨41890439948068569664906253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27926959965379046443270835 41890439948068569664906253)
  ·
    refine ⟨15708914980525713624339845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41890439948068569664906253 15708914980525713624339845)
    ·
      refine ⟨2945421558848571304563721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15708914980525713624339845 2945421558848571304563721)
      ·
        refine ⟨2209066169136428478422791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2945421558848571304563721 2209066169136428478422791)
        ·
          refine ⟨3313599253704642717634187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2209066169136428478422791 3313599253704642717634187)
          ·
            refine ⟨4970398880556964076451281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313599253704642717634187 4970398880556964076451281)
            ·
              refine ⟨3727799160417723057338461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4970398880556964076451281 3727799160417723057338461)
              ·
                refine ⟨1397924685156646146501923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3727799160417723057338461 1397924685156646146501923)
                ·
                  refine ⟨2096887027734969219752885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397924685156646146501923 2096887027734969219752885)
                  ·
                    refine ⟨196583158850153364351833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2096887027734969219752885 196583158850153364351833)
                    ·
                      rfl

theorem cell23_1148533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1148533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148533 prefixEnd_1148533 := by exact prefixLift 1148533
  have htrace : WordTrace (prefixWord ++ tailWord_1148533) baseStart_1148533 baseEnd_1148533 := by
    simpa [prefixWord, tailWord_1148533, baseEnd_1148533] using wordTrace_append hprefix tailTrace_1148533
  have hstable : (prefixWord ++ tailWord_1148533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148533).length < 2 ^ (prefixWord ++ tailWord_1148533).sum := by decide
  have hdescent : baseEnd_1148533 < baseStart_1148533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148549 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_1148549 : Nat := 118140960795 + 1148549 * 2 ^ 59
def prefixEnd_1148549 : Nat := 4983230072969 + 3 ^ 40 * 1148549 * 2
def baseEnd_1148549 : Nat := 589757692240932030455425

theorem tailTrace_1148549 : CollatzResearch.WordTrace tailWord_1148549 prefixEnd_1148549 589757692240932030455425 := by
  unfold tailWord_1148549
  simp only [CollatzResearch.WordTrace]
  refine ⟨41891023516010604397488701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27927349010673736264992467 41891023516010604397488701)
  ·
    refine ⟨15709133818503976649058263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41891023516010604397488701 15709133818503976649058263)
    ·
      refine ⟨23563700727755964973587395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15709133818503976649058263 23563700727755964973587395)
      ·
        refine ⟨35345551091633947460381093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23563700727755964973587395 35345551091633947460381093)
        ·
          refine ⟨6627290829681365148821455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35345551091633947460381093 6627290829681365148821455)
          ·
            refine ⟨9940936244522047723232183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6627290829681365148821455 9940936244522047723232183)
            ·
              refine ⟨14911404366783071584848275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9940936244522047723232183 14911404366783071584848275)
              ·
                refine ⟨22367106550174607377272413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14911404366783071584848275 22367106550174607377272413)
                ·
                  refine ⟨8387664956315477766477155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22367106550174607377272413 8387664956315477766477155)
                  ·
                    refine ⟨12581497434473216649715733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8387664956315477766477155 12581497434473216649715733)
                    ·
                      refine ⟨589757692240932030455425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12581497434473216649715733 589757692240932030455425)
                      ·
                        rfl

theorem cell23_1148549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_1148549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148549 prefixEnd_1148549 := by exact prefixLift 1148549
  have htrace : WordTrace (prefixWord ++ tailWord_1148549) baseStart_1148549 baseEnd_1148549 := by
    simpa [prefixWord, tailWord_1148549, baseEnd_1148549] using wordTrace_append hprefix tailTrace_1148549
  have hstable : (prefixWord ++ tailWord_1148549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148549).length < 2 ^ (prefixWord ++ tailWord_1148549).sum := by decide
  have hdescent : baseEnd_1148549 < baseStart_1148549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148556 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1148556 : Nat := 118140960795 + 1148556 * 2 ^ 59
def prefixEnd_1148556 : Nat := 4983230072969 + 3 ^ 40 * 1148556 * 2
def baseEnd_1148556 : Nat := 589761286605513503067893

theorem tailTrace_1148556 : CollatzResearch.WordTrace tailWord_1148556 prefixEnd_1148556 589761286605513503067893 := by
  unfold tailWord_1148556
  simp only [CollatzResearch.WordTrace]
  refine ⟨20945639413492622296496761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27927519217990163061995681 20945639413492622296496761)
  ·
    refine ⟨15709229560119466722372571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20945639413492622296496761 15709229560119466722372571)
    ·
      refine ⟨23563844340179200083558857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15709229560119466722372571 23563844340179200083558857)
      ·
        refine ⟨17672883255134400062669143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23563844340179200083558857 17672883255134400062669143)
        ·
          refine ⟨26509324882701600094003715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17672883255134400062669143 26509324882701600094003715)
          ·
            refine ⟨39763987324052400141005573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26509324882701600094003715 39763987324052400141005573)
            ·
              refine ⟨7455747623259825026438545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39763987324052400141005573 7455747623259825026438545)
              ·
                refine ⟨5591810717444868769828909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7455747623259825026438545 5591810717444868769828909)
                ·
                  refine ⟨2096929019041825788685841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5591810717444868769828909 2096929019041825788685841)
                  ·
                    refine ⟨1572696764281369341514381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2096929019041825788685841 1572696764281369341514381)
                    ·
                      refine ⟨589761286605513503067893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572696764281369341514381 589761286605513503067893)
                      ·
                        rfl

theorem cell23_1148556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1148556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148556 prefixEnd_1148556 := by exact prefixLift 1148556
  have htrace : WordTrace (prefixWord ++ tailWord_1148556) baseStart_1148556 baseEnd_1148556 := by
    simpa [prefixWord, tailWord_1148556, baseEnd_1148556] using wordTrace_append hprefix tailTrace_1148556
  have hstable : (prefixWord ++ tailWord_1148556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148556).length < 2 ^ (prefixWord ++ tailWord_1148556).sum := by decide
  have hdescent : baseEnd_1148556 < baseStart_1148556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148584 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 1, 5]
def baseStart_1148584 : Nat := 118140960795 + 1148584 * 2 ^ 59
def prefixEnd_1148584 : Nat := 4983230072969 + 3 ^ 40 * 1148584 * 2
def baseEnd_1148584 : Nat := 196591888021279797839255

theorem tailTrace_1148584 : CollatzResearch.WordTrace tailWord_1148584 prefixEnd_1148584 196591888021279797839255 := by
  unfold tailWord_1148584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946150035441902687506403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27928200047255870250008537 20946150035441902687506403)
  ·
    refine ⟨31419225053162854031259605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20946150035441902687506403 31419225053162854031259605)
    ·
      refine ⟨736388087183504391357647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 31419225053162854031259605 736388087183504391357647)
      ·
        refine ⟨1104582130775256587036471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 736388087183504391357647 1104582130775256587036471)
        ·
          refine ⟨1656873196162884880554707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1104582130775256587036471 1656873196162884880554707)
          ·
            refine ⟨2485309794244327320832061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656873196162884880554707 2485309794244327320832061)
            ·
              refine ⟨931991172841622745312023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2485309794244327320832061 931991172841622745312023)
              ·
                refine ⟨1397986759262434117968035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 931991172841622745312023 1397986759262434117968035)
                ·
                  refine ⟨2096980138893651176952053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397986759262434117968035 2096980138893651176952053)
                  ·
                    refine ⟨196591888021279797839255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2096980138893651176952053 196591888021279797839255)
                    ·
                      rfl

theorem cell23_1148584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_1148584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148584 prefixEnd_1148584 := by exact prefixLift 1148584
  have htrace : WordTrace (prefixWord ++ tailWord_1148584) baseStart_1148584 baseEnd_1148584 := by
    simpa [prefixWord, tailWord_1148584, baseEnd_1148584] using wordTrace_append hprefix tailTrace_1148584
  have hstable : (prefixWord ++ tailWord_1148584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148584).length < 2 ^ (prefixWord ++ tailWord_1148584).sum := by decide
  have hdescent : baseEnd_1148584 < baseStart_1148584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148604 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_1148604 : Nat := 118140960795 + 1148604 * 2 ^ 59
def prefixEnd_1148604 : Nat := 4983230072969 + 3 ^ 40 * 1148604 * 2
def baseEnd_1148604 : Nat := 589785933676929315267673

theorem tailTrace_1148604 : CollatzResearch.WordTrace tailWord_1148604 prefixEnd_1148604 589785933676929315267673 := by
  unfold tailWord_1148604
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946514765405674395370433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27928686353874232527160577 20946514765405674395370433)
  ·
    refine ⟨15709886074054255796527825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20946514765405674395370433 15709886074054255796527825)
    ·
      refine ⟨11782414555540691847395869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15709886074054255796527825 11782414555540691847395869)
      ·
        refine ⟨4418405458327759442773451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11782414555540691847395869 4418405458327759442773451)
        ·
          refine ⟨6627608187491639164160177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4418405458327759442773451 6627608187491639164160177)
          ·
            refine ⟨4970706140618729373120133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6627608187491639164160177 4970706140618729373120133)
            ·
              refine ⟨932007401366011757460025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4970706140618729373120133 932007401366011757460025)
              ·
                refine ⟨699005551024508818095019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 932007401366011757460025 699005551024508818095019)
                ·
                  refine ⟨1048508326536763227142529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 699005551024508818095019 1048508326536763227142529)
                  ·
                    refine ⟨786381244902572420356897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1048508326536763227142529 786381244902572420356897)
                    ·
                      refine ⟨589785933676929315267673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 786381244902572420356897 589785933676929315267673)
                      ·
                        rfl

theorem cell23_1148604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_1148604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148604 prefixEnd_1148604 := by exact prefixLift 1148604
  have htrace : WordTrace (prefixWord ++ tailWord_1148604) baseStart_1148604 baseEnd_1148604 := by
    simpa [prefixWord, tailWord_1148604, baseEnd_1148604] using wordTrace_append hprefix tailTrace_1148604
  have hstable : (prefixWord ++ tailWord_1148604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148604).length < 2 ^ (prefixWord ++ tailWord_1148604).sum := by decide
  have hdescent : baseEnd_1148604 < baseStart_1148604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148606 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1148606 : Nat := 118140960795 + 1148606 * 2 ^ 59
def prefixEnd_1148606 : Nat := 4983230072969 + 3 ^ 40 * 1148606 * 2
def baseEnd_1148606 : Nat := 196595653546079435814221

theorem tailTrace_1148606 : CollatzResearch.WordTrace tailWord_1148606 prefixEnd_1148606 196595653546079435814221 := by
  unfold tailWord_1148606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236637809600512891539209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27928734984536068754875781 5236637809600512891539209)
  ·
    refine ⟨3927478357200384668654407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5236637809600512891539209 3927478357200384668654407)
    ·
      refine ⟨5891217535800577002981611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3927478357200384668654407 5891217535800577002981611)
      ·
        refine ⟨8836826303700865504472417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5891217535800577002981611 8836826303700865504472417)
        ·
          refine ⟨6627619727775649128354313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8836826303700865504472417 6627619727775649128354313)
          ·
            refine ⟨4970714795831736846265735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6627619727775649128354313 4970714795831736846265735)
            ·
              refine ⟨7456072193747605269398603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970714795831736846265735 7456072193747605269398603)
              ·
                refine ⟨11184108290621407904097905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7456072193747605269398603 11184108290621407904097905)
                ·
                  refine ⟨8388081217966055928073429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11184108290621407904097905 8388081217966055928073429)
                  ·
                    refine ⟨196595653546079435814221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8388081217966055928073429 196595653546079435814221)
                    ·
                      rfl

theorem cell23_1148606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1148606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148606 prefixEnd_1148606 := by exact prefixLift 1148606
  have htrace : WordTrace (prefixWord ++ tailWord_1148606) baseStart_1148606 baseEnd_1148606 := by
    simpa [prefixWord, tailWord_1148606, baseEnd_1148606] using wordTrace_append hprefix tailTrace_1148606
  have hstable : (prefixWord ++ tailWord_1148606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148606).length < 2 ^ (prefixWord ++ tailWord_1148606).sum := by decide
  have hdescent : baseEnd_1148606 < baseStart_1148606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148620 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1148620 : Nat := 118140960795 + 1148620 * 2 ^ 59
def prefixEnd_1148620 : Nat := 4983230072969 + 3 ^ 40 * 1148620 * 2
def baseEnd_1148620 : Nat := 589794149367401252667599

theorem tailTrace_1148620 : CollatzResearch.WordTrace tailWord_1148620 prefixEnd_1148620 589794149367401252667599 := by
  unfold tailWord_1148620
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946806549376691761661657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27929075399168922348882209 20946806549376691761661657)
  ·
    refine ⟨15710104912032518821246243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20946806549376691761661657 15710104912032518821246243)
    ·
      refine ⟨23565157368048778231869365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15710104912032518821246243 23565157368048778231869365)
      ·
        refine ⟨2209233503254572959237753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23565157368048778231869365 2209233503254572959237753)
        ·
          refine ⟨1656925127440929719428315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2209233503254572959237753 1656925127440929719428315)
          ·
            refine ⟨2485387691161394579142473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656925127440929719428315 2485387691161394579142473)
            ·
              refine ⟨1864040768371045934356855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485387691161394579142473 1864040768371045934356855)
              ·
                refine ⟨2796061152556568901535283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864040768371045934356855 2796061152556568901535283)
                ·
                  refine ⟨4194091728834853352302925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2796061152556568901535283 4194091728834853352302925)
                  ·
                    refine ⟨1572784398313070007113597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4194091728834853352302925 1572784398313070007113597)
                    ·
                      refine ⟨589794149367401252667599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1572784398313070007113597 589794149367401252667599)
                      ·
                        rfl

theorem cell23_1148620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1148620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148620 prefixEnd_1148620 := by exact prefixLift 1148620
  have htrace : WordTrace (prefixWord ++ tailWord_1148620) baseStart_1148620 baseEnd_1148620 := by
    simpa [prefixWord, tailWord_1148620, baseEnd_1148620] using wordTrace_append hprefix tailTrace_1148620
  have hstable : (prefixWord ++ tailWord_1148620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148620).length < 2 ^ (prefixWord ++ tailWord_1148620).sum := by decide
  have hdescent : baseEnd_1148620 < baseStart_1148620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1148649 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 11]
def baseStart_1148649 : Nat := 118140960795 + 1148649 * 2 ^ 59
def prefixEnd_1148649 : Nat := 4983230072969 + 3 ^ 40 * 1148649 * 2
def baseEnd_1148649 : Nat := 65534337811820182133885

theorem tailTrace_1148649 : CollatzResearch.WordTrace tailWord_1148649 prefixEnd_1148649 65534337811820182133885 := by
  unfold tailWord_1148649
  simp only [CollatzResearch.WordTrace]
  refine ⟨41894670815648321476129001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27929780543765547650752667 41894670815648321476129001)
  ·
    refine ⟨31421003111736241107096751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41894670815648321476129001 31421003111736241107096751)
    ·
      refine ⟨47131504667604361660645127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31421003111736241107096751 47131504667604361660645127)
      ·
        refine ⟨70697257001406542490967691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47131504667604361660645127 70697257001406542490967691)
        ·
          refine ⟨106045885502109813736451537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70697257001406542490967691 106045885502109813736451537)
          ·
            refine ⟨79534414126582360302338653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106045885502109813736451537 79534414126582360302338653)
            ·
              refine ⟨29825405297468385113376995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79534414126582360302338653 29825405297468385113376995)
              ·
                refine ⟨44738107946202577670065493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29825405297468385113376995 44738107946202577670065493)
                ·
                  refine ⟨65534337811820182133885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 44738107946202577670065493 65534337811820182133885)
                  ·
                    rfl

theorem cell23_1148649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_1148649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1148649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1148649 prefixEnd_1148649 := by exact prefixLift 1148649
  have htrace : WordTrace (prefixWord ++ tailWord_1148649) baseStart_1148649 baseEnd_1148649 := by
    simpa [prefixWord, tailWord_1148649, baseEnd_1148649] using wordTrace_append hprefix tailTrace_1148649
  have hstable : (prefixWord ++ tailWord_1148649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1148649).length < 2 ^ (prefixWord ++ tailWord_1148649).sum := by decide
  have hdescent : baseEnd_1148649 < baseStart_1148649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1148649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
