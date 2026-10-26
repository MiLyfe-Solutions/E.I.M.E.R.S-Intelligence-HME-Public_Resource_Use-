import V185TrunkScan22Chunk378

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3380024 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 3, 3]
def baseStart_3380024 : Nat := 118140960795 + 3380024 * 2 ^ 59
def prefixEnd_3380024 : Nat := 4983230072969 + 3 ^ 40 * 3380024 * 2
def baseEnd_3380024 : Nat := 1157051290488392582837039

theorem tailTrace_3380024 : CollatzResearch.WordTrace tailWord_3380024 prefixEnd_3380024 1157051290488392582837039 := by
  unfold tailWord_3380024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61639801553378892493061563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82186402071171856657415417 61639801553378892493061563)
  ·
    refine ⟨92459702330068338739592345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61639801553378892493061563 92459702330068338739592345)
    ·
      refine ⟨69344776747551254054694259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92459702330068338739592345 69344776747551254054694259)
      ·
        refine ⟨104017165121326881082041389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69344776747551254054694259 104017165121326881082041389)
        ·
          refine ⟨39006436920497580405765521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104017165121326881082041389 39006436920497580405765521)
          ·
            refine ⟨29254827690373185304324141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39006436920497580405765521 29254827690373185304324141)
            ·
              refine ⟨10970560383889944489121553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29254827690373185304324141 10970560383889944489121553)
              ·
                refine ⟨8227920287917458366841165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10970560383889944489121553 8227920287917458366841165)
                ·
                  refine ⟨3085470107969046887565437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8227920287917458366841165 3085470107969046887565437)
                  ·
                    refine ⟨1157051290488392582837039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085470107969046887565437 1157051290488392582837039)
                    ·
                      rfl

theorem cell22_3380024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 3, 3].length) (baseStart_3380024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380024 prefixEnd_3380024 := by exact prefixLift 3380024
  have htrace : WordTrace (prefixWord ++ tailWord_3380024) baseStart_3380024 baseEnd_3380024 := by
    simpa [prefixWord, tailWord_3380024, baseEnd_3380024] using wordTrace_append hprefix tailTrace_3380024
  have hstable : (prefixWord ++ tailWord_3380024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380024).length < 2 ^ (prefixWord ++ tailWord_3380024).sum := by decide
  have hdescent : baseEnd_3380024 < baseStart_3380024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380041 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 1, 3]
def baseStart_3380041 : Nat := 118140960795 + 3380041 * 2 ^ 59
def prefixEnd_3380041 : Nat := 4983230072969 + 3 ^ 40 * 3380041 * 2
def baseEnd_3380041 : Nat := 1157057109935810205161987

theorem tailTrace_3380041 : CollatzResearch.WordTrace tailWord_3380041 prefixEnd_3380041 1157057109935810205161987 := by
  unfold tailWord_3380041
  simp only [CollatzResearch.WordTrace]
  refine ⟨123280223147696196889491977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82186815431797464592994651 123280223147696196889491977)
  ·
    refine ⟨92460167360772147667118983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123280223147696196889491977 92460167360772147667118983)
    ·
      refine ⟨138690251041158221500678475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92460167360772147667118983 138690251041158221500678475)
      ·
        refine ⟨208035376561737332251017713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138690251041158221500678475 208035376561737332251017713)
        ·
          refine ⟨156026532421302999188263285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208035376561737332251017713 156026532421302999188263285)
          ·
            refine ⟨14627487414497156173899683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156026532421302999188263285 14627487414497156173899683)
            ·
              refine ⟨21941231121745734260849525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14627487414497156173899683 21941231121745734260849525)
              ·
                refine ⟨2056990417663662586954643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21941231121745734260849525 2056990417663662586954643)
                ·
                  refine ⟨3085485626495493880431965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056990417663662586954643 3085485626495493880431965)
                  ·
                    refine ⟨1157057109935810205161987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085485626495493880431965 1157057109935810205161987)
                    ·
                      rfl

theorem cell22_3380041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_3380041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380041 prefixEnd_3380041 := by exact prefixLift 3380041
  have htrace : WordTrace (prefixWord ++ tailWord_3380041) baseStart_3380041 baseEnd_3380041 := by
    simpa [prefixWord, tailWord_3380041, baseEnd_3380041] using wordTrace_append hprefix tailTrace_3380041
  have hstable : (prefixWord ++ tailWord_3380041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380041).length < 2 ^ (prefixWord ++ tailWord_3380041).sum := by decide
  have hdescent : baseEnd_3380041 < baseStart_3380041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380071 : List Nat := [1, 1, 5, 1, 2, 3, 3, 1, 5]
def baseStart_3380071 : Nat := 118140960795 + 3380071 * 2 ^ 59
def prefixEnd_3380071 : Nat := 4983230072969 + 3 ^ 40 * 3380071 * 2
def baseEnd_3380071 : Nat := 385689126516300042303965

theorem tailTrace_3380071 : CollatzResearch.WordTrace tailWord_3380071 prefixEnd_3380071 385689126516300042303965 := by
  unfold tailWord_3380071
  simp only [CollatzResearch.WordTrace]
  refine ⟨123281317337587512013084067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82187544891725008008722711 123281317337587512013084067)
  ·
    refine ⟨184921976006381268019626101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123281317337587512013084067 184921976006381268019626101)
    ·
      refine ⟨17336435250598243876839947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184921976006381268019626101 17336435250598243876839947)
      ·
        refine ⟨26004652875897365815259921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17336435250598243876839947 26004652875897365815259921)
        ·
          refine ⟨19503489656923024361444941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26004652875897365815259921 19503489656923024361444941)
          ·
            refine ⟨7313808621346134135541853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19503489656923024361444941 7313808621346134135541853)
            ·
              refine ⟨2742678233004800300828195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7313808621346134135541853 2742678233004800300828195)
              ·
                refine ⟨4114017349507200451242293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742678233004800300828195 4114017349507200451242293)
                ·
                  refine ⟨385689126516300042303965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4114017349507200451242293 385689126516300042303965)
                  ·
                    rfl

theorem cell22_3380071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 5].length) (baseStart_3380071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380071 prefixEnd_3380071 := by exact prefixLift 3380071
  have htrace : WordTrace (prefixWord ++ tailWord_3380071) baseStart_3380071 baseEnd_3380071 := by
    simpa [prefixWord, tailWord_3380071, baseEnd_3380071] using wordTrace_append hprefix tailTrace_3380071
  have hstable : (prefixWord ++ tailWord_3380071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380071).length < 2 ^ (prefixWord ++ tailWord_3380071).sum := by decide
  have hdescent : baseEnd_3380071 < baseStart_3380071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380135 : List Nat := [1, 1, 6, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3380135 : Nat := 118140960795 + 3380135 * 2 ^ 59
def prefixEnd_3380135 : Nat := 4983230072969 + 3 ^ 40 * 3380135 * 2
def baseEnd_3380135 : Nat := 1157089288056825293311699

theorem tailTrace_3380135 : CollatzResearch.WordTrace tailWord_3380135 prefixEnd_3380135 1157089288056825293311699 := by
  unfold tailWord_3380135
  simp only [CollatzResearch.WordTrace]
  refine ⟨123283651609355650943413859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82189101072903767295609239 123283651609355650943413859)
  ·
    refine ⟨184925477414033476415120789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123283651609355650943413859 184925477414033476415120789)
    ·
      refine ⟨8668381753782819206958787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184925477414033476415120789 8668381753782819206958787)
      ·
        refine ⟨13002572630674228810438181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8668381753782819206958787 13002572630674228810438181)
        ·
          refine ⟨2437982368251417901957159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13002572630674228810438181 2437982368251417901957159)
          ·
            refine ⟨3656973552377126852935739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437982368251417901957159 3656973552377126852935739)
            ·
              refine ⟨5485460328565690279403609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656973552377126852935739 5485460328565690279403609)
              ·
                refine ⟨4114095246424267709552707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485460328565690279403609 4114095246424267709552707)
                ·
                  refine ⟨6171142869636401564329061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114095246424267709552707 6171142869636401564329061)
                  ·
                    refine ⟨1157089288056825293311699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171142869636401564329061 1157089288056825293311699)
                    ·
                      rfl

theorem cell22_3380135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3380135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380135 prefixEnd_3380135 := by exact prefixLift 3380135
  have htrace : WordTrace (prefixWord ++ tailWord_3380135) baseStart_3380135 baseEnd_3380135 := by
    simpa [prefixWord, tailWord_3380135, baseEnd_3380135] using wordTrace_append hprefix tailTrace_3380135
  have hstable : (prefixWord ++ tailWord_3380135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380135).length < 2 ^ (prefixWord ++ tailWord_3380135).sum := by decide
  have hdescent : baseEnd_3380135 < baseStart_3380135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380148 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3380148 : Nat := 118140960795 + 3380148 * 2 ^ 59
def prefixEnd_3380148 : Nat := 4983230072969 + 3 ^ 40 * 3380148 * 2
def baseEnd_3380148 : Nat := 1157093738222497592736659

theorem tailTrace_3380148 : CollatzResearch.WordTrace tailWord_3380148 prefixEnd_3380148 1157093738222497592736659 := by
  unfold tailWord_3380148
  simp only [CollatzResearch.WordTrace]
  refine ⟨61642062879154277081818549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82189417172205702775758065 61642062879154277081818549)
  ·
    refine ⟨5778943394920713476420489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61642062879154277081818549 5778943394920713476420489)
    ·
      refine ⟨4334207546190535107315367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5778943394920713476420489 4334207546190535107315367)
      ·
        refine ⟨6501311319285802660973051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334207546190535107315367 6501311319285802660973051)
        ·
          refine ⟨9751966978928703991459577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501311319285802660973051 9751966978928703991459577)
          ·
            refine ⟨7313975234196527993594683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9751966978928703991459577 7313975234196527993594683)
            ·
              refine ⟨10970962851294791990392025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7313975234196527993594683 10970962851294791990392025)
              ·
                refine ⟨8228222138471093992794019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10970962851294791990392025 8228222138471093992794019)
                ·
                  refine ⟨12342333207706640989191029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8228222138471093992794019 12342333207706640989191029)
                  ·
                    refine ⟨1157093738222497592736659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12342333207706640989191029 1157093738222497592736659)
                    ·
                      rfl

theorem cell22_3380148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3380148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380148 prefixEnd_3380148 := by exact prefixLift 3380148
  have htrace : WordTrace (prefixWord ++ tailWord_3380148) baseStart_3380148 baseEnd_3380148 := by
    simpa [prefixWord, tailWord_3380148, baseEnd_3380148] using wordTrace_append hprefix tailTrace_3380148
  have hstable : (prefixWord ++ tailWord_3380148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380148).length < 2 ^ (prefixWord ++ tailWord_3380148).sum := by decide
  have hdescent : baseEnd_3380148 < baseStart_3380148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380159 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 7, 3]
def baseStart_3380159 : Nat := 118140960795 + 3380159 * 2 ^ 59
def prefixEnd_3380159 : Nat := 4983230072969 + 3 ^ 40 * 3380159 * 2
def baseEnd_3380159 : Nat := 1157097503747297230711625

theorem tailTrace_3380159 : CollatzResearch.WordTrace tailWord_3380159 prefixEnd_3380159 1157097503747297230711625 := by
  unfold tailWord_3380159
  simp only [CollatzResearch.WordTrace]
  refine ⟨123284526961268703042287531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82189684640845802028191687 123284526961268703042287531)
  ·
    refine ⟨184926790441903054563431297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123284526961268703042287531 184926790441903054563431297)
    ·
      refine ⟨138695092831427290922573473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184926790441903054563431297 138695092831427290922573473)
      ·
        refine ⟨104021319623570468191930105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138695092831427290922573473 104021319623570468191930105)
        ·
          refine ⟨78015989717677851143947579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104021319623570468191930105 78015989717677851143947579)
          ·
            refine ⟨117023984576516776715921369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78015989717677851143947579 117023984576516776715921369)
            ·
              refine ⟨87767988432387582536941027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117023984576516776715921369 87767988432387582536941027)
              ·
                refine ⟨131651982648581373805411541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87767988432387582536941027 131651982648581373805411541)
                ·
                  refine ⟨3085593343326125948564333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 131651982648581373805411541 3085593343326125948564333)
                  ·
                    refine ⟨1157097503747297230711625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085593343326125948564333 1157097503747297230711625)
                    ·
                      rfl

theorem cell22_3380159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_3380159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380159 prefixEnd_3380159 := by exact prefixLift 3380159
  have htrace : WordTrace (prefixWord ++ tailWord_3380159) baseStart_3380159 baseEnd_3380159 := by
    simpa [prefixWord, tailWord_3380159, baseEnd_3380159] using wordTrace_append hprefix tailTrace_3380159
  have hstable : (prefixWord ++ tailWord_3380159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380159).length < 2 ^ (prefixWord ++ tailWord_3380159).sum := by decide
  have hdescent : baseEnd_3380159 < baseStart_3380159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380174 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3380174 : Nat := 118140960795 + 3380174 * 2 ^ 59
def prefixEnd_3380174 : Nat := 4983230072969 + 3 ^ 40 * 3380174 * 2
def baseEnd_3380174 : Nat := 1157102638553842191586579

theorem tailTrace_3380174 : CollatzResearch.WordTrace tailWord_3380174 prefixEnd_3380174 1157102638553842191586579 := by
  unfold tailWord_3380174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15410634257026795075510447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82190049370809573736055717 15410634257026795075510447)
  ·
    refine ⟨23115951385540192613265671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15410634257026795075510447 23115951385540192613265671)
    ·
      refine ⟨34673927078310288919898507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23115951385540192613265671 34673927078310288919898507)
      ·
        refine ⟨52010890617465433379847761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34673927078310288919898507 52010890617465433379847761)
        ·
          refine ⟨39008167963099075034885821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52010890617465433379847761 39008167963099075034885821)
          ·
            refine ⟨14628062986162153138082183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39008167963099075034885821 14628062986162153138082183)
            ·
              refine ⟨21942094479243229707123275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628062986162153138082183 21942094479243229707123275)
              ·
                refine ⟨32913141718864844560684913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21942094479243229707123275 32913141718864844560684913)
                ·
                  refine ⟨24684856289148633420513685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32913141718864844560684913 24684856289148633420513685)
                  ·
                    refine ⟨1157102638553842191586579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24684856289148633420513685 1157102638553842191586579)
                    ·
                      rfl

theorem cell22_3380174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3380174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380174 prefixEnd_3380174 := by exact prefixLift 3380174
  have htrace : WordTrace (prefixWord ++ tailWord_3380174) baseStart_3380174 baseEnd_3380174 := by
    simpa [prefixWord, tailWord_3380174, baseEnd_3380174] using wordTrace_append hprefix tailTrace_3380174
  have hstable : (prefixWord ++ tailWord_3380174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380174).length < 2 ^ (prefixWord ++ tailWord_3380174).sum := by decide
  have hdescent : baseEnd_3380174 < baseStart_3380174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380281 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 4, 4]
def baseStart_3380281 : Nat := 118140960795 + 3380281 * 2 ^ 59
def prefixEnd_3380281 : Nat := 4983230072969 + 3 ^ 40 * 3380281 * 2
def baseEnd_3380281 : Nat := 1157139266840529579161251

theorem tailTrace_3380281 : CollatzResearch.WordTrace tailWord_3380281 prefixEnd_3380281 1157139266840529579161251 := by
  unfold tailWord_3380281
  simp only [CollatzResearch.WordTrace]
  refine ⟨123288976666826717878228697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82192651111217811918819131 123288976666826717878228697)
  ·
    refine ⟨92466732500120038408671523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123288976666826717878228697 92466732500120038408671523)
    ·
      refine ⟨138700098750180057613007285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92466732500120038408671523 138700098750180057613007285)
      ·
        refine ⟨13003134257829380401219433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138700098750180057613007285 13003134257829380401219433)
        ·
          refine ⟨9752350693372035300914575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13003134257829380401219433 9752350693372035300914575)
          ·
            refine ⟨14628526040058052951371863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752350693372035300914575 14628526040058052951371863)
            ·
              refine ⟨21942789060087079427057795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628526040058052951371863 21942789060087079427057795)
              ·
                refine ⟨32914183590130619140586693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21942789060087079427057795 32914183590130619140586693)
                ·
                  refine ⟨6171409423149491088860005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32914183590130619140586693 6171409423149491088860005)
                  ·
                    refine ⟨1157139266840529579161251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171409423149491088860005 1157139266840529579161251)
                    ·
                      rfl

theorem cell22_3380281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_3380281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380281 prefixEnd_3380281 := by exact prefixLift 3380281
  have htrace : WordTrace (prefixWord ++ tailWord_3380281) baseStart_3380281 baseEnd_3380281 := by
    simpa [prefixWord, tailWord_3380281, baseEnd_3380281] using wordTrace_append hprefix tailTrace_3380281
  have hstable : (prefixWord ++ tailWord_3380281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380281).length < 2 ^ (prefixWord ++ tailWord_3380281).sum := by decide
  have hdescent : baseEnd_3380281 < baseStart_3380281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380285 : List Nat := [1, 4, 1, 3, 1, 3, 3, 2, 4]
def baseStart_3380285 : Nat := 118140960795 + 3380285 * 2 ^ 59
def prefixEnd_3380285 : Nat := 4983230072969 + 3 ^ 40 * 3380285 * 2
def baseEnd_3380285 : Nat := 385713545374091634020413

theorem tailTrace_3380285 : CollatzResearch.WordTrace tailWord_3380285 prefixEnd_3380285 385713545374091634020413 := by
  unfold tailWord_3380285
  simp only [CollatzResearch.WordTrace]
  refine ⟨123289122558812226561374309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82192748372541484374249539 123289122558812226561374309)
  ·
    refine ⟨23116710479777292480257683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123289122558812226561374309 23116710479777292480257683)
    ·
      refine ⟨34675065719665938720386525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23116710479777292480257683 34675065719665938720386525)
      ·
        refine ⟨13003149644874727020144947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34675065719665938720386525 13003149644874727020144947)
        ·
          refine ⟨19504724467312090530217421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13003149644874727020144947 19504724467312090530217421)
          ·
            refine ⟨7314271675242033948831533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19504724467312090530217421 7314271675242033948831533)
            ·
              refine ⟨2742851878215762730811825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7314271675242033948831533 2742851878215762730811825)
              ·
                refine ⟨2057138908661822048108869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742851878215762730811825 2057138908661822048108869)
                ·
                  refine ⟨385713545374091634020413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057138908661822048108869 385713545374091634020413)
                  ·
                    rfl

theorem cell22_3380285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_3380285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380285 prefixEnd_3380285 := by exact prefixLift 3380285
  have htrace : WordTrace (prefixWord ++ tailWord_3380285) baseStart_3380285 baseEnd_3380285 := by
    simpa [prefixWord, tailWord_3380285, baseEnd_3380285] using wordTrace_append hprefix tailTrace_3380285
  have hstable : (prefixWord ++ tailWord_3380285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380285).length < 2 ^ (prefixWord ++ tailWord_3380285).sum := by decide
  have hdescent : baseEnd_3380285 < baseStart_3380285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380311 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 5, 3]
def baseStart_3380311 : Nat := 118140960795 + 3380311 * 2 ^ 59
def prefixEnd_3380311 : Nat := 4983230072969 + 3 ^ 40 * 3380311 * 2
def baseEnd_3380311 : Nat := 1157149536453619500911159

theorem tailTrace_3380311 : CollatzResearch.WordTrace tailWord_3380311 prefixEnd_3380311 1157149536453619500911159 := by
  unfold tailWord_3380311
  simp only [CollatzResearch.WordTrace]
  refine ⟨123290070856718033001820787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82193380571145355334547191 123290070856718033001820787)
  ·
    refine ⟨184935106285077049502731181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123290070856718033001820787 184935106285077049502731181)
    ·
      refine ⟨69350664856903893563524193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184935106285077049502731181 69350664856903893563524193)
      ·
        refine ⟨52012998642677920172643145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69350664856903893563524193 52012998642677920172643145)
        ·
          refine ⟨39009748982008440129482359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52012998642677920172643145 39009748982008440129482359)
          ·
            refine ⟨58514623473012660194223539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39009748982008440129482359 58514623473012660194223539)
            ·
              refine ⟨87771935209518990291335309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58514623473012660194223539 87771935209518990291335309)
              ·
                refine ⟨32914475703569621359250741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87771935209518990291335309 32914475703569621359250741)
                ·
                  refine ⟨3085732097209652002429757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32914475703569621359250741 3085732097209652002429757)
                  ·
                    refine ⟨1157149536453619500911159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085732097209652002429757 1157149536453619500911159)
                    ·
                      rfl

theorem cell22_3380311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_3380311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380311 prefixEnd_3380311 := by exact prefixLift 3380311
  have htrace : WordTrace (prefixWord ++ tailWord_3380311) baseStart_3380311 baseEnd_3380311 := by
    simpa [prefixWord, tailWord_3380311, baseEnd_3380311] using wordTrace_append hprefix tailTrace_3380311
  have hstable : (prefixWord ++ tailWord_3380311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380311).length < 2 ^ (prefixWord ++ tailWord_3380311).sum := by decide
  have hdescent : baseEnd_3380311 < baseStart_3380311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380339 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 7]
def baseStart_3380339 : Nat := 118140960795 + 3380339 * 2 ^ 59
def prefixEnd_3380339 : Nat := 4983230072969 + 3 ^ 40 * 3380339 * 2
def baseEnd_3380339 : Nat := 1157159121425836761211073

theorem tailTrace_3380339 : CollatzResearch.WordTrace tailWord_3380339 prefixEnd_3380339 1157159121425836761211073 := by
  unfold tailWord_3380339
  simp only [CollatzResearch.WordTrace]
  refine ⟨123291092100616593783840071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82194061400411062522560047 123291092100616593783840071)
  ·
    refine ⟨184936638150924890675760107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123291092100616593783840071 184936638150924890675760107)
    ·
      refine ⟨277404957226387336013640161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184936638150924890675760107 277404957226387336013640161)
      ·
        refine ⟨208053717919790502010230121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277404957226387336013640161 208053717919790502010230121)
        ·
          refine ⟨156040288439842876507672591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208053717919790502010230121 156040288439842876507672591)
          ·
            refine ⟨234060432659764314761508887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156040288439842876507672591 234060432659764314761508887)
            ·
              refine ⟨351090648989646472142263331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234060432659764314761508887 351090648989646472142263331)
              ·
                refine ⟨526635973484469708213394997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351090648989646472142263331 526635973484469708213394997)
                ·
                  refine ⟨49372122514169035145005781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 526635973484469708213394997 49372122514169035145005781)
                  ·
                    refine ⟨1157159121425836761211073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49372122514169035145005781 1157159121425836761211073)
                    ·
                      rfl

theorem cell22_3380339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_3380339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380339 prefixEnd_3380339 := by exact prefixLift 3380339
  have htrace : WordTrace (prefixWord ++ tailWord_3380339) baseStart_3380339 baseEnd_3380339 := by
    simpa [prefixWord, tailWord_3380339, baseEnd_3380339] using wordTrace_append hprefix tailTrace_3380339
  have hstable : (prefixWord ++ tailWord_3380339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380339).length < 2 ^ (prefixWord ++ tailWord_3380339).sum := by decide
  have hdescent : baseEnd_3380339 < baseStart_3380339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380356 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3380356 : Nat := 118140960795 + 3380356 * 2 ^ 59
def prefixEnd_3380356 : Nat := 4983230072969 + 3 ^ 40 * 3380356 * 2
def baseEnd_3380356 : Nat := 1157164940873254383536021

theorem tailTrace_3380356 : CollatzResearch.WordTrace tailWord_3380356 prefixEnd_3380356 1157164940873254383536021 := by
  unfold tailWord_3380356
  simp only [CollatzResearch.WordTrace]
  refine ⟨61645856070777502843604461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82194474761036670458139281 61645856070777502843604461)
  ·
    refine ⟨23117196026541563566351673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61645856070777502843604461 23117196026541563566351673)
    ·
      refine ⟨17337897019906172674763755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23117196026541563566351673 17337897019906172674763755)
      ·
        refine ⟨26006845529859259012145633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17337897019906172674763755 26006845529859259012145633)
        ·
          refine ⟨19505134147394444259109225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26006845529859259012145633 19505134147394444259109225)
          ·
            refine ⟨14628850610545833194331919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19505134147394444259109225 14628850610545833194331919)
            ·
              refine ⟨21943275915818749791497879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14628850610545833194331919 21943275915818749791497879)
              ·
                refine ⟨32914913873728124687246819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21943275915818749791497879 32914913873728124687246819)
                ·
                  refine ⟨49372370810592187030870229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32914913873728124687246819 49372370810592187030870229)
                  ·
                    refine ⟨1157164940873254383536021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49372370810592187030870229 1157164940873254383536021)
                    ·
                      rfl

theorem cell22_3380356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3380356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380356 prefixEnd_3380356 := by exact prefixLift 3380356
  have htrace : WordTrace (prefixWord ++ tailWord_3380356) baseStart_3380356 baseEnd_3380356 := by
    simpa [prefixWord, tailWord_3380356, baseEnd_3380356] using wordTrace_append hprefix tailTrace_3380356
  have hstable : (prefixWord ++ tailWord_3380356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380356).length < 2 ^ (prefixWord ++ tailWord_3380356).sum := by decide
  have hdescent : baseEnd_3380356 < baseStart_3380356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380371 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 3, 4]
def baseStart_3380371 : Nat := 118140960795 + 3380371 * 2 ^ 59
def prefixEnd_3380371 : Nat := 4983230072969 + 3 ^ 40 * 3380371 * 2
def baseEnd_3380371 : Nat := 1157170075679799344410975

theorem tailTrace_3380371 : CollatzResearch.WordTrace tailWord_3380371 prefixEnd_3380371 1157170075679799344410975 := by
  unfold tailWord_3380371
  simp only [CollatzResearch.WordTrace]
  refine ⟨123292259236500663249004967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82194839491000442166003311 123292259236500663249004967)
  ·
    refine ⟨184938388854750994873507451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123292259236500663249004967 184938388854750994873507451)
    ·
      refine ⟨277407583282126492310261177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184938388854750994873507451 277407583282126492310261177)
      ·
        refine ⟨208055687461594869232695883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277407583282126492310261177 208055687461594869232695883)
        ·
          refine ⟨312083531192392303849043825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208055687461594869232695883 312083531192392303849043825)
          ·
            refine ⟨234062648394294227886782869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312083531192392303849043825 234062648394294227886782869)
            ·
              refine ⟨10971686643482541932192947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234062648394294227886782869 10971686643482541932192947)
              ·
                refine ⟨16457529965223812898289421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10971686643482541932192947 16457529965223812898289421)
                ·
                  refine ⟨6171573736958929836858533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16457529965223812898289421 6171573736958929836858533)
                  ·
                    refine ⟨1157170075679799344410975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171573736958929836858533 1157170075679799344410975)
                    ·
                      rfl

theorem cell22_3380371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 3, 4].length) (baseStart_3380371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380371 prefixEnd_3380371 := by exact prefixLift 3380371
  have htrace : WordTrace (prefixWord ++ tailWord_3380371) baseStart_3380371 baseEnd_3380371 := by
    simpa [prefixWord, tailWord_3380371, baseEnd_3380371] using wordTrace_append hprefix tailTrace_3380371
  have hstable : (prefixWord ++ tailWord_3380371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380371).length < 2 ^ (prefixWord ++ tailWord_3380371).sum := by decide
  have hdescent : baseEnd_3380371 < baseStart_3380371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380403 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 4]
def baseStart_3380403 : Nat := 118140960795 + 3380403 * 2 ^ 59
def prefixEnd_3380403 : Nat := 4983230072969 + 3 ^ 40 * 3380403 * 2
def baseEnd_3380403 : Nat := 385727009977920642536959

theorem tailTrace_3380403 : CollatzResearch.WordTrace tailWord_3380403 prefixEnd_3380403 385727009977920642536959 := by
  unfold tailWord_3380403
  simp only [CollatzResearch.WordTrace]
  refine ⟨123293426372384732714169863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82195617581589821809446575 123293426372384732714169863)
  ·
    refine ⟨184940139558577099071254795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123293426372384732714169863 184940139558577099071254795)
    ·
      refine ⟨277410209337865648606882193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184940139558577099071254795 277410209337865648606882193)
      ·
        refine ⟨208057657003399236455161645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277410209337865648606882193 208057657003399236455161645)
        ·
          refine ⟨78021621376274713670685617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208057657003399236455161645 78021621376274713670685617)
          ·
            refine ⟨58516216032206035253014213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78021621376274713670685617 58516216032206035253014213)
            ·
              refine ⟨10971790506038631609940165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58516216032206035253014213 10971790506038631609940165)
              ·
                refine ⟨2057210719882243426863781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10971790506038631609940165 2057210719882243426863781)
                ·
                  refine ⟨385727009977920642536959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057210719882243426863781 385727009977920642536959)
                  ·
                    rfl

theorem cell22_3380403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 4].length) (baseStart_3380403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380403 prefixEnd_3380403 := by exact prefixLift 3380403
  have htrace : WordTrace (prefixWord ++ tailWord_3380403) baseStart_3380403 baseEnd_3380403 := by
    simpa [prefixWord, tailWord_3380403, baseEnd_3380403] using wordTrace_append hprefix tailTrace_3380403
  have hstable : (prefixWord ++ tailWord_3380403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380403).length < 2 ^ (prefixWord ++ tailWord_3380403).sum := by decide
  have hdescent : baseEnd_3380403 < baseStart_3380403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380437 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 4]
def baseStart_3380437 : Nat := 118140960795 + 3380437 * 2 ^ 59
def prefixEnd_3380437 : Nat := 4983230072969 + 3 ^ 40 * 3380437 * 2
def baseEnd_3380437 : Nat := 385730889609532390753591

theorem tailTrace_3380437 : CollatzResearch.WordTrace tailWord_3380437 prefixEnd_3380437 385730889609532390753591 := by
  unfold tailWord_3380437
  simp only [CollatzResearch.WordTrace]
  refine ⟨123294666454261556520907565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82196444302841037680605043 123294666454261556520907565)
  ·
    refine ⟨46235499920348083695340337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123294666454261556520907565 46235499920348083695340337)
    ·
      refine ⟨34676624940261062771505253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46235499920348083695340337 34676624940261062771505253)
      ·
        refine ⟨6501867176298949269657235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34676624940261062771505253 6501867176298949269657235)
        ·
          refine ⟨9752800764448423904485853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501867176298949269657235 9752800764448423904485853)
          ·
            refine ⟨3657300286668158964182195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9752800764448423904485853 3657300286668158964182195)
            ·
              refine ⟨5485950430002238446273293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657300286668158964182195 5485950430002238446273293)
              ·
                refine ⟨2057231411250839417352485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5485950430002238446273293 2057231411250839417352485)
                ·
                  refine ⟨385730889609532390753591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057231411250839417352485 385730889609532390753591)
                  ·
                    rfl

theorem cell22_3380437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 4].length) (baseStart_3380437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380437 prefixEnd_3380437 := by exact prefixLift 3380437
  have htrace : WordTrace (prefixWord ++ tailWord_3380437) baseStart_3380437 baseEnd_3380437 := by
    simpa [prefixWord, tailWord_3380437, baseEnd_3380437] using wordTrace_append hprefix tailTrace_3380437
  have hstable : (prefixWord ++ tailWord_3380437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380437).length < 2 ^ (prefixWord ++ tailWord_3380437).sum := by decide
  have hdescent : baseEnd_3380437 < baseStart_3380437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380514 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3380514 : Nat := 118140960795 + 3380514 * 2 ^ 59
def prefixEnd_3380514 : Nat := 4983230072969 + 3 ^ 40 * 3380514 * 2
def baseEnd_3380514 : Nat := 1157219027502194638085537

theorem tailTrace_3380514 : CollatzResearch.WordTrace tailWord_3380514 prefixEnd_3380514 1157219027502194638085537 := by
  unfold tailWord_3380514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824368718745649667865149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82198316583321732447640397 30824368718745649667865149)
  ·
    refine ⟨11559138269529618625449431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30824368718745649667865149 11559138269529618625449431)
    ·
      refine ⟨17338707404294427938174147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559138269529618625449431 17338707404294427938174147)
      ·
        refine ⟨26008061106441641907261221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17338707404294427938174147 26008061106441641907261221)
        ·
          refine ⟨4876511457457807857611479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26008061106441641907261221 4876511457457807857611479)
          ·
            refine ⟨7314767186186711786417219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876511457457807857611479 7314767186186711786417219)
            ·
              refine ⟨10972150779280067679625829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314767186186711786417219 10972150779280067679625829)
              ·
                refine ⟨2057278271115012689929843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10972150779280067679625829 2057278271115012689929843)
                ·
                  refine ⟨3085917406672519034894765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057278271115012689929843 3085917406672519034894765)
                  ·
                    refine ⟨1157219027502194638085537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085917406672519034894765 1157219027502194638085537)
                    ·
                      rfl

theorem cell22_3380514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3380514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380514 prefixEnd_3380514 := by exact prefixLift 3380514
  have htrace : WordTrace (prefixWord ++ tailWord_3380514) baseStart_3380514 baseEnd_3380514 := by
    simpa [prefixWord, tailWord_3380514, baseEnd_3380514] using wordTrace_append hprefix tailTrace_3380514
  have hstable : (prefixWord ++ tailWord_3380514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380514).length < 2 ^ (prefixWord ++ tailWord_3380514).sum := by decide
  have hdescent : baseEnd_3380514 < baseStart_3380514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380525 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3380525 : Nat := 118140960795 + 3380525 * 2 ^ 59
def prefixEnd_3380525 : Nat := 4983230072969 + 3 ^ 40 * 3380525 * 2
def baseEnd_3380525 : Nat := 1157222793026994276060503

theorem tailTrace_3380525 : CollatzResearch.WordTrace tailWord_3380525 prefixEnd_3380525 1157222793026994276060503 := by
  unfold tailWord_3380525
  simp only [CollatzResearch.WordTrace]
  refine ⟨123297876077942747550111029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82198584051961831700074019 123297876077942747550111029)
  ·
    refine ⟨11559175882307132582822909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123297876077942747550111029 11559175882307132582822909)
    ·
      refine ⟨4334690955865174718558591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11559175882307132582822909 4334690955865174718558591)
      ·
        refine ⟨6502036433797762077837887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334690955865174718558591 6502036433797762077837887)
        ·
          refine ⟨9753054650696643116756831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502036433797762077837887 9753054650696643116756831)
          ·
            refine ⟨14629581976044964675135247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753054650696643116756831 14629581976044964675135247)
            ·
              refine ⟨21944372964067447012702871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14629581976044964675135247 21944372964067447012702871)
              ·
                refine ⟨32916559446101170519054307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21944372964067447012702871 32916559446101170519054307)
                ·
                  refine ⟨49374839169151755778581461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32916559446101170519054307 49374839169151755778581461)
                  ·
                    refine ⟨1157222793026994276060503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49374839169151755778581461 1157222793026994276060503)
                    ·
                      rfl

theorem cell22_3380525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3380525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380525 prefixEnd_3380525 := by exact prefixLift 3380525
  have htrace : WordTrace (prefixWord ++ tailWord_3380525) baseStart_3380525 baseEnd_3380525 := by
    simpa [prefixWord, tailWord_3380525, baseEnd_3380525] using wordTrace_append hprefix tailTrace_3380525
  have hstable : (prefixWord ++ tailWord_3380525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380525).length < 2 ^ (prefixWord ++ tailWord_3380525).sum := by decide
  have hdescent : baseEnd_3380525 < baseStart_3380525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380538 : List Nat := [3, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_3380538 : Nat := 118140960795 + 3380538 * 2 ^ 59
def prefixEnd_3380538 : Nat := 4983230072969 + 3 ^ 40 * 3380538 * 2
def baseEnd_3380538 : Nat := 385742414397555525161821

theorem tailTrace_3380538 : CollatzResearch.WordTrace tailWord_3380538 prefixEnd_3380538 385742414397555525161821 := by
  unfold tailWord_3380538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30824587556723912692583567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82198900151263767180222845 30824587556723912692583567)
  ·
    refine ⟨46236881335085869038875351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30824587556723912692583567 46236881335085869038875351)
    ·
      refine ⟨69355322002628803558313027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46236881335085869038875351 69355322002628803558313027)
      ·
        refine ⟨104032983003943205337469541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69355322002628803558313027 104032983003943205337469541)
        ·
          refine ⟨19506184313239351000775539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104032983003943205337469541 19506184313239351000775539)
          ·
            refine ⟨29259276469859026501163309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19506184313239351000775539 29259276469859026501163309)
            ·
              refine ⟨10972228676197134937936241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29259276469859026501163309 10972228676197134937936241)
              ·
                refine ⟨8229171507147851203452181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972228676197134937936241 8229171507147851203452181)
                ·
                  refine ⟨385742414397555525161821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8229171507147851203452181 385742414397555525161821)
                  ·
                    rfl

theorem cell22_3380538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_3380538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380538 prefixEnd_3380538 := by exact prefixLift 3380538
  have htrace : WordTrace (prefixWord ++ tailWord_3380538) baseStart_3380538 baseEnd_3380538 := by
    simpa [prefixWord, tailWord_3380538, baseEnd_3380538] using wordTrace_append hprefix tailTrace_3380538
  have hstable : (prefixWord ++ tailWord_3380538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380538).length < 2 ^ (prefixWord ++ tailWord_3380538).sum := by decide
  have hdescent : baseEnd_3380538 < baseStart_3380538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380553 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_3380553 : Nat := 118140960795 + 3380553 * 2 ^ 59
def prefixEnd_3380553 : Nat := 4983230072969 + 3 ^ 40 * 3380553 * 2
def baseEnd_3380553 : Nat := 1157232377999211536360417

theorem tailTrace_3380553 : CollatzResearch.WordTrace tailWord_3380553 prefixEnd_3380553 1157232377999211536360417 := by
  unfold tailWord_3380553
  simp only [CollatzResearch.WordTrace]
  refine ⟨123298897321841308332130313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82199264881227538888086875 123298897321841308332130313)
  ·
    refine ⟨92474172991380981249097735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123298897321841308332130313 92474172991380981249097735)
    ·
      refine ⟨138711259487071471873646603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92474172991380981249097735 138711259487071471873646603)
      ·
        refine ⟨208066889230607207810469905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138711259487071471873646603 208066889230607207810469905)
        ·
          refine ⟨156050166922955405857852429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208066889230607207810469905 156050166922955405857852429)
          ·
            refine ⟨58518812596108277196694661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156050166922955405857852429 58518812596108277196694661)
            ·
              refine ⟨10972277361770301974380249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58518812596108277196694661 10972277361770301974380249)
              ·
                refine ⟨8229208021327726480785187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972277361770301974380249 8229208021327726480785187)
                ·
                  refine ⟨12343812031991589721177781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229208021327726480785187 12343812031991589721177781)
                  ·
                    refine ⟨1157232377999211536360417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12343812031991589721177781 1157232377999211536360417)
                    ·
                      rfl

theorem cell22_3380553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_3380553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380553 prefixEnd_3380553 := by exact prefixLift 3380553
  have htrace : WordTrace (prefixWord ++ tailWord_3380553) baseStart_3380553 baseEnd_3380553 := by
    simpa [prefixWord, tailWord_3380553, baseEnd_3380553] using wordTrace_append hprefix tailTrace_3380553
  have hstable : (prefixWord ++ tailWord_3380553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380553).length < 2 ^ (prefixWord ++ tailWord_3380553).sum := by decide
  have hdescent : baseEnd_3380553 < baseStart_3380553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380568 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 4, 4]
def baseStart_3380568 : Nat := 118140960795 + 3380568 * 2 ^ 59
def prefixEnd_3380568 : Nat := 4983230072969 + 3 ^ 40 * 3380568 * 2
def baseEnd_3380568 : Nat := 1157237512805756497235371

theorem tailTrace_3380568 : CollatzResearch.WordTrace tailWord_3380568 prefixEnd_3380568 1157237512805756497235371 := by
  unfold tailWord_3380568
  simp only [CollatzResearch.WordTrace]
  refine ⟨61649722208393482946963179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82199629611191310595950905 61649722208393482946963179)
  ·
    refine ⟨92474583312590224420444769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61649722208393482946963179 92474583312590224420444769)
    ·
      refine ⟨69355937484442668315333577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92474583312590224420444769 69355937484442668315333577)
      ·
        refine ⟨52016953113332001236500183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69355937484442668315333577 52016953113332001236500183)
        ·
          refine ⟨78025429669998001854750275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52016953113332001236500183 78025429669998001854750275)
          ·
            refine ⟨117038144504997002782125413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78025429669998001854750275 117038144504997002782125413)
            ·
              refine ⟨21944652094686938021648515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117038144504997002782125413 21944652094686938021648515)
              ·
                refine ⟨32916978142030407032472773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21944652094686938021648515 32916978142030407032472773)
                ·
                  refine ⟨6171933401630701318588645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32916978142030407032472773 6171933401630701318588645)
                  ·
                    refine ⟨1157237512805756497235371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171933401630701318588645 1157237512805756497235371)
                    ·
                      rfl

theorem cell22_3380568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_3380568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380568 prefixEnd_3380568 := by exact prefixLift 3380568
  have htrace : WordTrace (prefixWord ++ tailWord_3380568) baseStart_3380568 baseEnd_3380568 := by
    simpa [prefixWord, tailWord_3380568, baseEnd_3380568] using wordTrace_append hprefix tailTrace_3380568
  have hstable : (prefixWord ++ tailWord_3380568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380568).length < 2 ^ (prefixWord ++ tailWord_3380568).sum := by decide
  have hdescent : baseEnd_3380568 < baseStart_3380568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380638 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3380638 : Nat := 118140960795 + 3380638 * 2 ^ 59
def prefixEnd_3380638 : Nat := 4983230072969 + 3 ^ 40 * 3380638 * 2
def baseEnd_3380638 : Nat := 1157261475236299647985157

theorem tailTrace_3380638 : CollatzResearch.WordTrace tailWord_3380638 prefixEnd_3380638 1157261475236299647985157 := by
  unfold tailWord_3380638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412749690816670981121821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82201331684355578565983045 15412749690816670981121821)
  ·
    refine ⟨5779781134056251617920683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15412749690816670981121821 5779781134056251617920683)
    ·
      refine ⟨8669671701084377426881025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779781134056251617920683 8669671701084377426881025)
      ·
        refine ⟨6502253775813283070160769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8669671701084377426881025 6502253775813283070160769)
        ·
          refine ⟨4876690331859962302620577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6502253775813283070160769 4876690331859962302620577)
          ·
            refine ⟨3657517748894971726965433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4876690331859962302620577 3657517748894971726965433)
            ·
              refine ⟨2743138311671228795224075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657517748894971726965433 2743138311671228795224075)
              ·
                refine ⟨4114707467506843192836113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743138311671228795224075 4114707467506843192836113)
                ·
                  refine ⟨3086030600630132394627085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4114707467506843192836113 3086030600630132394627085)
                  ·
                    refine ⟨1157261475236299647985157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3086030600630132394627085 1157261475236299647985157)
                    ·
                      rfl

theorem cell22_3380638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3380638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380638 prefixEnd_3380638 := by exact prefixLift 3380638
  have htrace : WordTrace (prefixWord ++ tailWord_3380638) baseStart_3380638 baseEnd_3380638 := by
    simpa [prefixWord, tailWord_3380638, baseEnd_3380638] using wordTrace_append hprefix tailTrace_3380638
  have hstable : (prefixWord ++ tailWord_3380638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380638).length < 2 ^ (prefixWord ++ tailWord_3380638).sum := by decide
  have hdescent : baseEnd_3380638 < baseStart_3380638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380643 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 7]
def baseStart_3380643 : Nat := 118140960795 + 3380643 * 2 ^ 59
def prefixEnd_3380643 : Nat := 4983230072969 + 3 ^ 40 * 3380643 * 2
def baseEnd_3380643 : Nat := 1157263186838481301610141

theorem tailTrace_3380643 : CollatzResearch.WordTrace tailWord_3380643 prefixEnd_3380643 1157263186838481301610141 := by
  unfold tailWord_3380643
  simp only [CollatzResearch.WordTrace]
  refine ⟨123302179891515253702906583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82201453261010169135271055 123302179891515253702906583)
  ·
    refine ⟨184953269837272880554359875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123302179891515253702906583 184953269837272880554359875)
    ·
      refine ⟨277429904755909320831539813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184953269837272880554359875 277429904755909320831539813)
      ·
        refine ⟨52018107141732997655913715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277429904755909320831539813 52018107141732997655913715)
        ·
          refine ⟨78027160712599496483870573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52018107141732997655913715 78027160712599496483870573)
          ·
            refine ⟨29260185267224811181451465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78027160712599496483870573 29260185267224811181451465)
            ·
              refine ⟨21945138950418608386088599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29260185267224811181451465 21945138950418608386088599)
              ·
                refine ⟨32917708425627912579132899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21945138950418608386088599 32917708425627912579132899)
                ·
                  refine ⟨49376562638441868868699349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32917708425627912579132899 49376562638441868868699349)
                  ·
                    refine ⟨1157263186838481301610141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49376562638441868868699349 1157263186838481301610141)
                    ·
                      rfl

theorem cell22_3380643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_3380643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380643 prefixEnd_3380643 := by exact prefixLift 3380643
  have htrace : WordTrace (prefixWord ++ tailWord_3380643) baseStart_3380643 baseEnd_3380643 := by
    simpa [prefixWord, tailWord_3380643, baseEnd_3380643] using wordTrace_append hprefix tailTrace_3380643
  have hstable : (prefixWord ++ tailWord_3380643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380643).length < 2 ^ (prefixWord ++ tailWord_3380643).sum := by decide
  have hdescent : baseEnd_3380643 < baseStart_3380643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380675 : List Nat := [1, 1, 1, 3, 1, 1, 4, 5, 1, 4]
def baseStart_3380675 : Nat := 118140960795 + 3380675 * 2 ^ 59
def prefixEnd_3380675 : Nat := 4983230072969 + 3 ^ 40 * 3380675 * 2
def baseEnd_3380675 : Nat := 1157274141092443884810043

theorem tailTrace_3380675 : CollatzResearch.WordTrace tailWord_3380675 prefixEnd_3380675 1157274141092443884810043 := by
  unfold tailWord_3380675
  simp only [CollatzResearch.WordTrace]
  refine ⟨123303347027399323168071479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82202231351599548778714319 123303347027399323168071479)
  ·
    refine ⟨184955020541098984752107219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123303347027399323168071479 184955020541098984752107219)
    ·
      refine ⟨277432530811648477128160829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184955020541098984752107219 277432530811648477128160829)
      ·
        refine ⟨104037199054368178923060311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277432530811648477128160829 104037199054368178923060311)
        ·
          refine ⟨156055798581552268384590467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104037199054368178923060311 156055798581552268384590467)
          ·
            refine ⟨234083697872328402576885701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156055798581552268384590467 234083697872328402576885701)
            ·
              refine ⟨43890693351061575483166069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234083697872328402576885701 43890693351061575483166069)
              ·
                refine ⟨4114752501662022701546819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43890693351061575483166069 4114752501662022701546819)
                ·
                  refine ⟨6172128752493034052320229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114752501662022701546819 6172128752493034052320229)
                  ·
                    refine ⟨1157274141092443884810043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172128752493034052320229 1157274141092443884810043)
                    ·
                      rfl

theorem cell22_3380675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 5, 1, 4].length) (baseStart_3380675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380675 prefixEnd_3380675 := by exact prefixLift 3380675
  have htrace : WordTrace (prefixWord ++ tailWord_3380675) baseStart_3380675 baseEnd_3380675 := by
    simpa [prefixWord, tailWord_3380675, baseEnd_3380675] using wordTrace_append hprefix tailTrace_3380675
  have hstable : (prefixWord ++ tailWord_3380675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380675).length < 2 ^ (prefixWord ++ tailWord_3380675).sum := by decide
  have hdescent : baseEnd_3380675 < baseStart_3380675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380705 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3380705 : Nat := 118140960795 + 3380705 * 2 ^ 59
def prefixEnd_3380705 : Nat := 4983230072969 + 3 ^ 40 * 3380705 * 2
def baseEnd_3380705 : Nat := 1157284410705533806559951

theorem tailTrace_3380705 : CollatzResearch.WordTrace tailWord_3380705 prefixEnd_3380705 1157284410705533806559951 := by
  unfold tailWord_3380705
  simp only [CollatzResearch.WordTrace]
  refine ⟨123304441217290638291663569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82202960811527092194442379 123304441217290638291663569)
  ·
    refine ⟨92478330912967978718747677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123304441217290638291663569 92478330912967978718747677)
    ·
      refine ⟨34679374092362992019530379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92478330912967978718747677 34679374092362992019530379)
      ·
        refine ⟨52019061138544488029295569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34679374092362992019530379 52019061138544488029295569)
        ·
          refine ⟨39014295853908366021971677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52019061138544488029295569 39014295853908366021971677)
          ·
            refine ⟨14630360945215637258239379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39014295853908366021971677 14630360945215637258239379)
            ·
              refine ⟨21945541417823455887359069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630360945215637258239379 21945541417823455887359069)
              ·
                refine ⟨8229578031683795957759651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21945541417823455887359069 8229578031683795957759651)
                ·
                  refine ⟨12344367047525693936639477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229578031683795957759651 12344367047525693936639477)
                  ·
                    refine ⟨1157284410705533806559951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12344367047525693936639477 1157284410705533806559951)
                    ·
                      rfl

theorem cell22_3380705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3380705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380705 prefixEnd_3380705 := by exact prefixLift 3380705
  have htrace : WordTrace (prefixWord ++ tailWord_3380705) baseStart_3380705 baseEnd_3380705 := by
    simpa [prefixWord, tailWord_3380705, baseEnd_3380705] using wordTrace_append hprefix tailTrace_3380705
  have hstable : (prefixWord ++ tailWord_3380705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380705).length < 2 ^ (prefixWord ++ tailWord_3380705).sum := by decide
  have hdescent : baseEnd_3380705 < baseStart_3380705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380720 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 6]
def baseStart_3380720 : Nat := 118140960795 + 3380720 * 2 ^ 59
def prefixEnd_3380720 : Nat := 4983230072969 + 3 ^ 40 * 3380720 * 2
def baseEnd_3380720 : Nat := 1157289545512078767434905

theorem tailTrace_3380720 : CollatzResearch.WordTrace tailWord_3380720 prefixEnd_3380720 1157289545512078767434905 := by
  unfold tailWord_3380720
  simp only [CollatzResearch.WordTrace]
  refine ⟨61652494156118147926729807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82203325541490863902306409 61652494156118147926729807)
  ·
    refine ⟨92478741234177221890094711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61652494156118147926729807 92478741234177221890094711)
    ·
      refine ⟨138718111851265832835142067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92478741234177221890094711 138718111851265832835142067)
      ·
        refine ⟨208077167776898749252713101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138718111851265832835142067 208077167776898749252713101)
        ·
          refine ⟨78028937916337030969767413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208077167776898749252713101 78028937916337030969767413)
          ·
            refine ⟨7315212929656596653415695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78028937916337030969767413 7315212929656596653415695)
            ·
              refine ⟨10972819394484894980123543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315212929656596653415695 10972819394484894980123543)
              ·
                refine ⟨16459229091727342470185315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10972819394484894980123543 16459229091727342470185315)
                ·
                  refine ⟨24688843637591013705277973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16459229091727342470185315 24688843637591013705277973)
                  ·
                    refine ⟨1157289545512078767434905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24688843637591013705277973 1157289545512078767434905)
                    ·
                      rfl

theorem cell22_3380720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 6].length) (baseStart_3380720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380720 prefixEnd_3380720 := by exact prefixLift 3380720
  have htrace : WordTrace (prefixWord ++ tailWord_3380720) baseStart_3380720 baseEnd_3380720 := by
    simpa [prefixWord, tailWord_3380720, baseEnd_3380720] using wordTrace_append hprefix tailTrace_3380720
  have hstable : (prefixWord ++ tailWord_3380720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380720).length < 2 ^ (prefixWord ++ tailWord_3380720).sum := by decide
  have hdescent : baseEnd_3380720 < baseStart_3380720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380722 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_3380722 : Nat := 118140960795 + 3380722 * 2 ^ 59
def prefixEnd_3380722 : Nat := 4983230072969 + 3 ^ 40 * 3380722 * 2
def baseEnd_3380722 : Nat := 1157290230152951428884899

theorem tailTrace_3380722 : CollatzResearch.WordTrace tailWord_3380722 prefixEnd_3380722 1157290230152951428884899 := by
  unfold tailWord_3380722
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826265314557262548758105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82203374172152700130021613 30826265314557262548758105)
  ·
    refine ⟨23119698985917946911568579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30826265314557262548758105 23119698985917946911568579)
    ·
      refine ⟨34679548478876920367352869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23119698985917946911568579 34679548478876920367352869)
      ·
        refine ⟨6502415339789422568878663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34679548478876920367352869 6502415339789422568878663)
        ·
          refine ⟨9753623009684133853317995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502415339789422568878663 9753623009684133853317995)
          ·
            refine ⟨14630434514526200779976993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753623009684133853317995 14630434514526200779976993)
            ·
              refine ⟨10972825885894650584982745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14630434514526200779976993 10972825885894650584982745)
              ·
                refine ⟨8229619414420987938737059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972825885894650584982745 8229619414420987938737059)
                ·
                  refine ⟨12344429121631481908105589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229619414420987938737059 12344429121631481908105589)
                  ·
                    refine ⟨1157290230152951428884899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12344429121631481908105589 1157290230152951428884899)
                    ·
                      rfl

theorem cell22_3380722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_3380722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380722 prefixEnd_3380722 := by exact prefixLift 3380722
  have htrace : WordTrace (prefixWord ++ tailWord_3380722) baseStart_3380722 baseEnd_3380722 := by
    simpa [prefixWord, tailWord_3380722, baseEnd_3380722] using wordTrace_append hprefix tailTrace_3380722
  have hstable : (prefixWord ++ tailWord_3380722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380722).length < 2 ^ (prefixWord ++ tailWord_3380722).sum := by decide
  have hdescent : baseEnd_3380722 < baseStart_3380722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380726 : List Nat := [5, 1, 1, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3380726 : Nat := 118140960795 + 3380726 * 2 ^ 59
def prefixEnd_3380726 : Nat := 4983230072969 + 3 ^ 40 * 3380726 * 2
def baseEnd_3380726 : Nat := 1157291599434696751784887

theorem tailTrace_3380726 : CollatzResearch.WordTrace tailWord_3380726 prefixEnd_3380726 1157291599434696751784887 := by
  unfold tailWord_3380726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7706575446888409929886127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82203471433476372585452021 7706575446888409929886127)
  ·
    refine ⟨11559863170332614894829191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7706575446888409929886127 11559863170332614894829191)
    ·
      refine ⟨17339794755498922342243787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559863170332614894829191 17339794755498922342243787)
      ·
        refine ⟨26009692133248383513365681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17339794755498922342243787 26009692133248383513365681)
        ·
          refine ⟨19507269099936287635024261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26009692133248383513365681 19507269099936287635024261)
          ·
            refine ⟨3657612956238053931567049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19507269099936287635024261 3657612956238053931567049)
            ·
              refine ⟨2743209717178540448675287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657612956238053931567049 2743209717178540448675287)
              ·
                refine ⟨4114814575767810673012931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743209717178540448675287 4114814575767810673012931)
                ·
                  refine ⟨6172221863651716009519397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114814575767810673012931 6172221863651716009519397)
                  ·
                    refine ⟨1157291599434696751784887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172221863651716009519397 1157291599434696751784887)
                    ·
                      rfl

theorem cell22_3380726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3380726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380726 prefixEnd_3380726 := by exact prefixLift 3380726
  have htrace : WordTrace (prefixWord ++ tailWord_3380726) baseStart_3380726 baseEnd_3380726 := by
    simpa [prefixWord, tailWord_3380726, baseEnd_3380726] using wordTrace_append hprefix tailTrace_3380726
  have hstable : (prefixWord ++ tailWord_3380726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380726).length < 2 ^ (prefixWord ++ tailWord_3380726).sum := by decide
  have hdescent : baseEnd_3380726 < baseStart_3380726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380756 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3380756 : Nat := 118140960795 + 3380756 * 2 ^ 59
def prefixEnd_3380756 : Nat := 4983230072969 + 3 ^ 40 * 3380756 * 2
def baseEnd_3380756 : Nat := 1157301869047786673534795

theorem tailTrace_3380756 : CollatzResearch.WordTrace tailWord_3380756 prefixEnd_3380756 1157301869047786673534795 := by
  unfold tailWord_3380756
  simp only [CollatzResearch.WordTrace]
  refine ⟨61653150670052937000885061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82204200893403916001180081 61653150670052937000885061)
  ·
    refine ⟨11559965750634925687665949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61653150670052937000885061 11559965750634925687665949)
    ·
      refine ⟨4334987156488097132874731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11559965750634925687665949 4334987156488097132874731)
      ·
        refine ⟨6502480734732145699312097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334987156488097132874731 6502480734732145699312097)
        ·
          refine ⟨4876860551049109274484073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6502480734732145699312097 4876860551049109274484073)
          ·
            refine ⟨3657645413286831955863055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4876860551049109274484073 3657645413286831955863055)
            ·
              refine ⟨5486468119930247933794583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657645413286831955863055 5486468119930247933794583)
              ·
                refine ⟨8229702179895371900691875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486468119930247933794583 8229702179895371900691875)
                ·
                  refine ⟨12344553269843057851037813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229702179895371900691875 12344553269843057851037813)
                  ·
                    refine ⟨1157301869047786673534795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12344553269843057851037813 1157301869047786673534795)
                    ·
                      rfl

theorem cell22_3380756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3380756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380756 prefixEnd_3380756 := by exact prefixLift 3380756
  have htrace : WordTrace (prefixWord ++ tailWord_3380756) baseStart_3380756 baseEnd_3380756 := by
    simpa [prefixWord, tailWord_3380756, baseEnd_3380756] using wordTrace_append hprefix tailTrace_3380756
  have hstable : (prefixWord ++ tailWord_3380756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380756).length < 2 ^ (prefixWord ++ tailWord_3380756).sum := by decide
  have hdescent : baseEnd_3380756 < baseStart_3380756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380767 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 3, 3]
def baseStart_3380767 : Nat := 118140960795 + 3380767 * 2 ^ 59
def prefixEnd_3380767 : Nat := 4983230072969 + 3 ^ 40 * 3380767 * 2
def baseEnd_3380767 : Nat := 1157305634572586311509761

theorem tailTrace_3380767 : CollatzResearch.WordTrace tailWord_3380767 prefixEnd_3380767 1157305634572586311509761 := by
  unfold tailWord_3380767
  simp only [CollatzResearch.WordTrace]
  refine ⟨123306702543066022880420555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82204468362044015253613703 123306702543066022880420555)
  ·
    refine ⟨184960053814599034320630833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123306702543066022880420555 184960053814599034320630833)
    ·
      refine ⟨138720040360949275740473125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184960053814599034320630833 138720040360949275740473125)
      ·
        refine ⟨26010007567677989201338711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138720040360949275740473125 26010007567677989201338711)
        ·
          refine ⟨39015011351516983802008067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26010007567677989201338711 39015011351516983802008067)
          ·
            refine ⟨58522517027275475703012101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39015011351516983802008067 58522517027275475703012101)
            ·
              refine ⟨10972971942614151694314769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58522517027275475703012101 10972971942614151694314769)
              ·
                refine ⟨8229728956960613770736077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972971942614151694314769 8229728956960613770736077)
                ·
                  refine ⟨3086148358860230164026029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8229728956960613770736077 3086148358860230164026029)
                  ·
                    refine ⟨1157305634572586311509761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3086148358860230164026029 1157305634572586311509761)
                    ·
                      rfl

theorem cell22_3380767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 3].length) (baseStart_3380767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380767 prefixEnd_3380767 := by exact prefixLift 3380767
  have htrace : WordTrace (prefixWord ++ tailWord_3380767) baseStart_3380767 baseEnd_3380767 := by
    simpa [prefixWord, tailWord_3380767, baseEnd_3380767] using wordTrace_append hprefix tailTrace_3380767
  have hstable : (prefixWord ++ tailWord_3380767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380767).length < 2 ^ (prefixWord ++ tailWord_3380767).sum := by decide
  have hdescent : baseEnd_3380767 < baseStart_3380767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380825 : List Nat := [1, 2, 1, 2, 2, 1, 1, 6, 6]
def baseStart_3380825 : Nat := 118140960795 + 3380825 * 2 ^ 59
def prefixEnd_3380825 : Nat := 4983230072969 + 3 ^ 40 * 3380825 * 2
def baseEnd_3380825 : Nat := 385775163052631164519861

theorem tailTrace_3380825 : CollatzResearch.WordTrace tailWord_3380825 prefixEnd_3380825 385775163052631164519861 := by
  unfold tailWord_3380825
  simp only [CollatzResearch.WordTrace]
  refine ⟨123308817976855898786031929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82205878651237265857354619 123308817976855898786031929)
  ·
    refine ⟨92481613482641924089523947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123308817976855898786031929 92481613482641924089523947)
    ·
      refine ⟨138722420223962886134285921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92481613482641924089523947 138722420223962886134285921)
      ·
        refine ⟨104041815167972164600714441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138722420223962886134285921 104041815167972164600714441)
        ·
          refine ⟨78031361375979123450535831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104041815167972164600714441 78031361375979123450535831)
          ·
            refine ⟨117047042063968685175803747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78031361375979123450535831 117047042063968685175803747)
            ·
              refine ⟨175570563095953027763705621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117047042063968685175803747 175570563095953027763705621)
              ·
                refine ⟨8229870145122798176423701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 175570563095953027763705621 8229870145122798176423701)
                ·
                  refine ⟨385775163052631164519861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8229870145122798176423701 385775163052631164519861)
                  ·
                    rfl

theorem cell22_3380825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_3380825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380825 prefixEnd_3380825 := by exact prefixLift 3380825
  have htrace : WordTrace (prefixWord ++ tailWord_3380825) baseStart_3380825 baseEnd_3380825 := by
    simpa [prefixWord, tailWord_3380825, baseEnd_3380825] using wordTrace_append hprefix tailTrace_3380825
  have hstable : (prefixWord ++ tailWord_3380825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380825).length < 2 ^ (prefixWord ++ tailWord_3380825).sum := by decide
  have hdescent : baseEnd_3380825 < baseStart_3380825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380855 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 6]
def baseStart_3380855 : Nat := 118140960795 + 3380855 * 2 ^ 59
def prefixEnd_3380855 : Nat := 4983230072969 + 3 ^ 40 * 3380855 * 2
def baseEnd_3380855 : Nat := 1157335758770983415309491

theorem tailTrace_3380855 : CollatzResearch.WordTrace tailWord_3380855 prefixEnd_3380855 1157335758770983415309491 := by
  unfold tailWord_3380855
  simp only [CollatzResearch.WordTrace]
  refine ⟨123309912166747213909624019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82206608111164809273082679 123309912166747213909624019)
  ·
    refine ⟨184964868250120820864436029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123309912166747213909624019 184964868250120820864436029)
    ·
      refine ⟨69361825593795307824163511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184964868250120820864436029 69361825593795307824163511)
      ·
        refine ⟨104042738390692961736245267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69361825593795307824163511 104042738390692961736245267)
        ·
          refine ⟨156064107586039442604367901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104042738390692961736245267 156064107586039442604367901)
          ·
            refine ⟨58524040344764790976637963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156064107586039442604367901 58524040344764790976637963)
            ·
              refine ⟨87786060517147186464956945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58524040344764790976637963 87786060517147186464956945)
              ·
                refine ⟨65839545387860389848717709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87786060517147186464956945 65839545387860389848717709)
                ·
                  refine ⟨24689829520447646193269141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65839545387860389848717709 24689829520447646193269141)
                  ·
                    refine ⟨1157335758770983415309491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24689829520447646193269141 1157335758770983415309491)
                    ·
                      rfl

theorem cell22_3380855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_3380855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380855 prefixEnd_3380855 := by exact prefixLift 3380855
  have htrace : WordTrace (prefixWord ++ tailWord_3380855) baseStart_3380855 baseEnd_3380855 := by
    simpa [prefixWord, tailWord_3380855, baseEnd_3380855] using wordTrace_append hprefix tailTrace_3380855
  have hstable : (prefixWord ++ tailWord_3380855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380855).length < 2 ^ (prefixWord ++ tailWord_3380855).sum := by decide
  have hdescent : baseEnd_3380855 < baseStart_3380855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380874 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_3380874 : Nat := 118140960795 + 3380874 * 2 ^ 59
def prefixEnd_3380874 : Nat := 4983230072969 + 3 ^ 40 * 3380874 * 2
def baseEnd_3380874 : Nat := 1157342262859273699084433

theorem tailTrace_3380874 : CollatzResearch.WordTrace tailWord_3380874 prefixEnd_3380874 1157342262859273699084433 := by
  unfold tailWord_3380874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30827651288419595038641419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82207070102452253436377117 30827651288419595038641419)
  ·
    refine ⟨46241476932629392557962129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30827651288419595038641419 46241476932629392557962129)
    ·
      refine ⟨34681107699472044418471597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46241476932629392557962129 34681107699472044418471597)
      ·
        refine ⟨13005415387302016656926849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34681107699472044418471597 13005415387302016656926849)
        ·
          refine ⟨9754061540476512492695137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13005415387302016656926849 9754061540476512492695137)
          ·
            refine ⟨7315546155357384369521353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9754061540476512492695137 7315546155357384369521353)
            ·
              refine ⟨5486659616518038277141015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7315546155357384369521353 5486659616518038277141015)
              ·
                refine ⟨8229989424777057415711523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486659616518038277141015 8229989424777057415711523)
                ·
                  refine ⟨12344984137165586123567285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229989424777057415711523 12344984137165586123567285)
                  ·
                    refine ⟨1157342262859273699084433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12344984137165586123567285 1157342262859273699084433)
                    ·
                      rfl

theorem cell22_3380874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_3380874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380874 prefixEnd_3380874 := by exact prefixLift 3380874
  have htrace : WordTrace (prefixWord ++ tailWord_3380874) baseStart_3380874 baseEnd_3380874 := by
    simpa [prefixWord, tailWord_3380874, baseEnd_3380874] using wordTrace_append hprefix tailTrace_3380874
  have hstable : (prefixWord ++ tailWord_3380874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380874).length < 2 ^ (prefixWord ++ tailWord_3380874).sum := by decide
  have hdescent : baseEnd_3380874 < baseStart_3380874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380895 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 1, 4]
def baseStart_3380895 : Nat := 118140960795 + 3380895 * 2 ^ 59
def prefixEnd_3380895 : Nat := 4983230072969 + 3 ^ 40 * 3380895 * 2
def baseEnd_3380895 : Nat := 1157349451588436644309369

theorem tailTrace_3380895 : CollatzResearch.WordTrace tailWord_3380895 prefixEnd_3380895 1157349451588436644309369 := by
  unfold tailWord_3380895
  simp only [CollatzResearch.WordTrace]
  refine ⟨123311371086602300741080139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82207580724401533827386759 123311371086602300741080139)
  ·
    refine ⟨184967056629903451111620209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123311371086602300741080139 184967056629903451111620209)
    ·
      refine ⟨138725292472427588333715157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184967056629903451111620209 138725292472427588333715157)
      ·
        refine ⟨3251374042322521601571449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 138725292472427588333715157 3251374042322521601571449)
        ·
          refine ⟨2438530531741891201178587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251374042322521601571449 2438530531741891201178587)
          ·
            refine ⟨3657795797612836801767881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438530531741891201178587 3657795797612836801767881)
            ·
              refine ⟨2743346848209627601325911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657795797612836801767881 2743346848209627601325911)
              ·
                refine ⟨4115020272314441401988867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743346848209627601325911 4115020272314441401988867)
                ·
                  refine ⟨6172530408471662102983301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115020272314441401988867 6172530408471662102983301)
                  ·
                    refine ⟨1157349451588436644309369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172530408471662102983301 1157349451588436644309369)
                    ·
                      rfl

theorem cell22_3380895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_3380895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380895 prefixEnd_3380895 := by exact prefixLift 3380895
  have htrace : WordTrace (prefixWord ++ tailWord_3380895) baseStart_3380895 baseEnd_3380895 := by
    simpa [prefixWord, tailWord_3380895, baseEnd_3380895] using wordTrace_append hprefix tailTrace_3380895
  have hstable : (prefixWord ++ tailWord_3380895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380895).length < 2 ^ (prefixWord ++ tailWord_3380895).sum := by decide
  have hdescent : baseEnd_3380895 < baseStart_3380895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380919 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 3, 3]
def baseStart_3380919 : Nat := 118140960795 + 3380919 * 2 ^ 59
def prefixEnd_3380919 : Nat := 4983230072969 + 3 ^ 40 * 3380919 * 2
def baseEnd_3380919 : Nat := 1157357667278908581709295

theorem tailTrace_3380919 : CollatzResearch.WordTrace tailWord_3380919 prefixEnd_3380919 1157357667278908581709295 := by
  unfold tailWord_3380919
  simp only [CollatzResearch.WordTrace]
  refine ⟨123312246438515352839953811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82208164292343568559969207 123312246438515352839953811)
  ·
    refine ⟨184968369657773029259930717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123312246438515352839953811 184968369657773029259930717)
    ·
      refine ⟨69363138621664885972474019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184968369657773029259930717 69363138621664885972474019)
      ·
        refine ⟨104044707932497328958711029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69363138621664885972474019 104044707932497328958711029)
        ·
          refine ⟨9754191368671624589879159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104044707932497328958711029 9754191368671624589879159)
          ·
            refine ⟨14631287053007436884818739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754191368671624589879159 14631287053007436884818739)
            ·
              refine ⟨21946930579511155327228109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14631287053007436884818739 21946930579511155327228109)
              ·
                refine ⟨8230098967316683247710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21946930579511155327228109 8230098967316683247710541)
                ·
                  refine ⟨3086287112743756217891453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8230098967316683247710541 3086287112743756217891453)
                  ·
                    refine ⟨1157357667278908581709295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3086287112743756217891453 1157357667278908581709295)
                    ·
                      rfl

theorem cell22_3380919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_3380919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380919 prefixEnd_3380919 := by exact prefixLift 3380919
  have htrace : WordTrace (prefixWord ++ tailWord_3380919) baseStart_3380919 baseEnd_3380919 := by
    simpa [prefixWord, tailWord_3380919, baseEnd_3380919] using wordTrace_append hprefix tailTrace_3380919
  have hstable : (prefixWord ++ tailWord_3380919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380919).length < 2 ^ (prefixWord ++ tailWord_3380919).sum := by decide
  have hdescent : baseEnd_3380919 < baseStart_3380919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380953 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 1, 3]
def baseStart_3380953 : Nat := 118140960795 + 3380953 * 2 ^ 59
def prefixEnd_3380953 : Nat := 4983230072969 + 3 ^ 40 * 3380953 * 2
def baseEnd_3380953 : Nat := 1157369306173743826359191

theorem tailTrace_3380953 : CollatzResearch.WordTrace tailWord_3380953 prefixEnd_3380953 1157369306173743826359191 := by
  unfold tailWord_3380953
  simp only [CollatzResearch.WordTrace]
  refine ⟨123313486520392176646691513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82208991013594784431127675 123313486520392176646691513)
  ·
    refine ⟨92485114890294132485018635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123313486520392176646691513 92485114890294132485018635)
    ·
      refine ⟨138727672335441198727527953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92485114890294132485018635 138727672335441198727527953)
      ·
        refine ⟨104045754251580899045645965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138727672335441198727527953 104045754251580899045645965)
        ·
          refine ⟨39017157844342837142117237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104045754251580899045645965 39017157844342837142117237)
          ·
            refine ⟨3657858547907140982073491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39017157844342837142117237 3657858547907140982073491)
            ·
              refine ⟨5486787821860711473110237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657858547907140982073491 5486787821860711473110237)
              ·
                refine ⟨2057545433197766802416339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5486787821860711473110237 2057545433197766802416339)
                ·
                  refine ⟨3086318149796650203624509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057545433197766802416339 3086318149796650203624509)
                  ·
                    refine ⟨1157369306173743826359191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3086318149796650203624509 1157369306173743826359191)
                    ·
                      rfl

theorem cell22_3380953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_3380953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380953 prefixEnd_3380953 := by exact prefixLift 3380953
  have htrace : WordTrace (prefixWord ++ tailWord_3380953) baseStart_3380953 baseEnd_3380953 := by
    simpa [prefixWord, tailWord_3380953, baseEnd_3380953] using wordTrace_append hprefix tailTrace_3380953
  have hstable : (prefixWord ++ tailWord_3380953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380953).length < 2 ^ (prefixWord ++ tailWord_3380953).sum := by decide
  have hdescent : baseEnd_3380953 < baseStart_3380953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380994 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3380994 : Nat := 118140960795 + 3380994 * 2 ^ 59
def prefixEnd_3380994 : Nat := 4983230072969 + 3 ^ 40 * 3380994 * 2
def baseEnd_3380994 : Nat := 385794447103877795361355

theorem tailTrace_3380994 : CollatzResearch.WordTrace tailWord_3380994 prefixEnd_3380994 385794447103877795361355 := by
  unfold tailWord_3380994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30828745478310910162233509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82209987942162427099289357 30828745478310910162233509)
  ·
    refine ⟨5780389777183295655418783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30828745478310910162233509 5780389777183295655418783)
    ·
      refine ⟨8670584665774943483128175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780389777183295655418783 8670584665774943483128175)
      ·
        refine ⟨13005876998662415224692263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670584665774943483128175 13005876998662415224692263)
        ·
          refine ⟨19508815497993622837038395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005876998662415224692263 19508815497993622837038395)
          ·
            refine ⟨29263223246990434255557593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19508815497993622837038395 29263223246990434255557593)
            ·
              refine ⟨21947417435242825691668195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29263223246990434255557593 21947417435242825691668195)
              ·
                refine ⟨32921126152864238537502293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21947417435242825691668195 32921126152864238537502293)
                ·
                  refine ⟨385794447103877795361355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32921126152864238537502293 385794447103877795361355)
                  ·
                    rfl

theorem cell22_3380994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3380994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380994 prefixEnd_3380994 := by exact prefixLift 3380994
  have htrace : WordTrace (prefixWord ++ tailWord_3380994) baseStart_3380994 baseEnd_3380994 := by
    simpa [prefixWord, tailWord_3380994, baseEnd_3380994] using wordTrace_append hprefix tailTrace_3380994
  have hstable : (prefixWord ++ tailWord_3380994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380994).length < 2 ^ (prefixWord ++ tailWord_3380994).sum := by decide
  have hdescent : baseEnd_3380994 < baseStart_3380994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380996 : List Nat := [2, 3, 2, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3380996 : Nat := 118140960795 + 3380996 * 2 ^ 59
def prefixEnd_3380996 : Nat := 4983230072969 + 3 ^ 40 * 3380996 * 2
def baseEnd_3380996 : Nat := 1157384025952506047534059

theorem tailTrace_3380996 : CollatzResearch.WordTrace tailWord_3380996 prefixEnd_3380996 1157384025952506047534059 := by
  unfold tailWord_3380996
  simp only [CollatzResearch.WordTrace]
  refine ⟨61657527429618197495253421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82210036572824263327004561 61657527429618197495253421)
  ·
    refine ⟨23121572786106824060720033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61657527429618197495253421 23121572786106824060720033)
    ·
      refine ⟨17341179589580118045540025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23121572786106824060720033 17341179589580118045540025)
      ·
        refine ⟨13005884692185088534155019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17341179589580118045540025 13005884692185088534155019)
        ·
          refine ⟨19508827038277632801232529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005884692185088534155019 19508827038277632801232529)
          ·
            refine ⟨14631620278708224600924397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19508827038277632801232529 14631620278708224600924397)
            ·
              refine ⟨5486857604515584225346649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14631620278708224600924397 5486857604515584225346649)
              ·
                refine ⟨4115143203386688169009987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486857604515584225346649 4115143203386688169009987)
                ·
                  refine ⟨6172714805080032253514981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115143203386688169009987 6172714805080032253514981)
                  ·
                    refine ⟨1157384025952506047534059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172714805080032253514981 1157384025952506047534059)
                    ·
                      rfl

theorem cell22_3380996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3380996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3380996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3380996 prefixEnd_3380996 := by exact prefixLift 3380996
  have htrace : WordTrace (prefixWord ++ tailWord_3380996) baseStart_3380996 baseEnd_3380996 := by
    simpa [prefixWord, tailWord_3380996, baseEnd_3380996] using wordTrace_append hprefix tailTrace_3380996
  have hstable : (prefixWord ++ tailWord_3380996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380996).length < 2 ^ (prefixWord ++ tailWord_3380996).sum := by decide
  have hdescent : baseEnd_3380996 < baseStart_3380996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381024 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 2, 4]
def baseStart_3381024 : Nat := 118140960795 + 3381024 * 2 ^ 59
def prefixEnd_3381024 : Nat := 4983230072969 + 3 ^ 40 * 3381024 * 2
def baseEnd_3381024 : Nat := 1157393610924723307833973

theorem tailTrace_3381024 : CollatzResearch.WordTrace tailWord_3381024 prefixEnd_3381024 1157393610924723307833973 := by
  unfold tailWord_3381024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61658038051567477886263063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82210717402089970515017417 61658038051567477886263063)
  ·
    refine ⟨92487057077351216829394595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61658038051567477886263063 92487057077351216829394595)
    ·
      refine ⟨138730585616026825244091893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92487057077351216829394595 138730585616026825244091893)
      ·
        refine ⟨13005992401502514866633615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138730585616026825244091893 13005992401502514866633615)
        ·
          refine ⟨19508988602253772299950423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005992401502514866633615 19508988602253772299950423)
          ·
            refine ⟨29263482903380658449925635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19508988602253772299950423 29263482903380658449925635)
            ·
              refine ⟨43895224355070987674888453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29263482903380658449925635 43895224355070987674888453)
              ·
                refine ⟨8230354566575810189041585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43895224355070987674888453 8230354566575810189041585)
                ·
                  refine ⟨6172765924931857641781189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8230354566575810189041585 6172765924931857641781189)
                  ·
                    refine ⟨1157393610924723307833973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172765924931857641781189 1157393610924723307833973)
                    ·
                      rfl

theorem cell22_3381024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 4].length) (baseStart_3381024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381024 prefixEnd_3381024 := by exact prefixLift 3381024
  have htrace : WordTrace (prefixWord ++ tailWord_3381024) baseStart_3381024 baseEnd_3381024 := by
    simpa [prefixWord, tailWord_3381024, baseEnd_3381024] using wordTrace_append hprefix tailTrace_3381024
  have hstable : (prefixWord ++ tailWord_3381024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381024).length < 2 ^ (prefixWord ++ tailWord_3381024).sum := by decide
  have hdescent : baseEnd_3381024 < baseStart_3381024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381028 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3381028 : Nat := 118140960795 + 3381028 * 2 ^ 59
def prefixEnd_3381028 : Nat := 4983230072969 + 3 ^ 40 * 3381028 * 2
def baseEnd_3381028 : Nat := 385798326735489543577987

theorem tailTrace_3381028 : CollatzResearch.WordTrace tailWord_3381028 prefixEnd_3381028 385798326735489543577987 := by
  unfold tailWord_3381028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61658110997560232227835869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82210814663413642970447825 61658110997560232227835869)
  ·
    refine ⟨23121791624085087085438451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61658110997560232227835869 23121791624085087085438451)
    ·
      refine ⟨34682687436127630628157677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23121791624085087085438451 34682687436127630628157677)
      ·
        refine ⟨13006007788547861485559129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34682687436127630628157677 13006007788547861485559129)
        ·
          refine ⟨9754505841410896114169347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006007788547861485559129 9754505841410896114169347)
          ·
            refine ⟨14631758762116344171254021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754505841410896114169347 14631758762116344171254021)
            ·
              refine ⟨2743454767896814532110129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14631758762116344171254021 2743454767896814532110129)
              ·
                refine ⟨2057591075922610899082597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743454767896814532110129 2057591075922610899082597)
                ·
                  refine ⟨385798326735489543577987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2057591075922610899082597 385798326735489543577987)
                  ·
                    rfl

theorem cell22_3381028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3381028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381028 prefixEnd_3381028 := by exact prefixLift 3381028
  have htrace : WordTrace (prefixWord ++ tailWord_3381028) baseStart_3381028 baseEnd_3381028 := by
    simpa [prefixWord, tailWord_3381028, baseEnd_3381028] using wordTrace_append hprefix tailTrace_3381028
  have hstable : (prefixWord ++ tailWord_3381028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381028).length < 2 ^ (prefixWord ++ tailWord_3381028).sum := by decide
  have hdescent : baseEnd_3381028 < baseStart_3381028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381088 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 1, 3]
def baseStart_3381088 : Nat := 118140960795 + 3381088 * 2 ^ 59
def prefixEnd_3381088 : Nat := 4983230072969 + 3 ^ 40 * 3381088 * 2
def baseEnd_3381088 : Nat := 1157415519432648474233777

theorem tailTrace_3381088 : CollatzResearch.WordTrace tailWord_3381088 prefixEnd_3381088 1157415519432648474233777 := by
  unfold tailWord_3381088
  simp only [CollatzResearch.WordTrace]
  refine ⟨61659205187451547351427959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82212273583268729801903945 61659205187451547351427959)
  ·
    refine ⟨92488807781177321027141939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61659205187451547351427959 92488807781177321027141939)
    ·
      refine ⟨138733211671765981540712909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92488807781177321027141939 138733211671765981540712909)
      ·
        refine ⟨52024954376912243077767341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138733211671765981540712909 52024954376912243077767341)
        ·
          refine ⟨19509357891342091154162753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52024954376912243077767341 19509357891342091154162753)
          ·
            refine ⟨14632018418506568365622065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19509357891342091154162753 14632018418506568365622065)
            ·
              refine ⟨10974013813879926274216549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14632018418506568365622065 10974013813879926274216549)
              ·
                refine ⟨2057627590102486176415603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10974013813879926274216549 2057627590102486176415603)
                ·
                  refine ⟨3086441385153729264623405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057627590102486176415603 3086441385153729264623405)
                  ·
                    refine ⟨1157415519432648474233777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3086441385153729264623405 1157415519432648474233777)
                    ·
                      rfl

theorem cell22_3381088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 3].length) (baseStart_3381088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381088 prefixEnd_3381088 := by exact prefixLift 3381088
  have htrace : WordTrace (prefixWord ++ tailWord_3381088) baseStart_3381088 baseEnd_3381088 := by
    simpa [prefixWord, tailWord_3381088, baseEnd_3381088] using wordTrace_append hprefix tailTrace_3381088
  have hstable : (prefixWord ++ tailWord_3381088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381088).length < 2 ^ (prefixWord ++ tailWord_3381088).sum := by decide
  have hdescent : baseEnd_3381088 < baseStart_3381088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381114 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_3381114 : Nat := 118140960795 + 3381114 * 2 ^ 59
def prefixEnd_3381114 : Nat := 4983230072969 + 3 ^ 40 * 3381114 * 2
def baseEnd_3381114 : Nat := 1157424419763993073083697

theorem tailTrace_3381114 : CollatzResearch.WordTrace tailWord_3381114 prefixEnd_3381114 1157424419763993073083697 := by
  unfold tailWord_3381114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30829839668202225285825599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82212905781872600762201597 30829839668202225285825599)
  ·
    refine ⟨46244759502303337928738399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30829839668202225285825599 46244759502303337928738399)
    ·
      refine ⟨69367139253455006893107599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46244759502303337928738399 69367139253455006893107599)
      ·
        refine ⟨104050708880182510339661399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69367139253455006893107599 104050708880182510339661399)
        ·
          refine ⟨156076063320273765509492099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104050708880182510339661399 156076063320273765509492099)
          ·
            refine ⟨234114094980410648264238149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156076063320273765509492099 234114094980410648264238149)
            ·
              refine ⟨43896392808826996549544653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234114094980410648264238149 43896392808826996549544653)
              ·
                refine ⟨16461147303310123706079245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43896392808826996549544653 16461147303310123706079245)
                ·
                  refine ⟨6172930238741296389779717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16461147303310123706079245 6172930238741296389779717)
                  ·
                    refine ⟨1157424419763993073083697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6172930238741296389779717 1157424419763993073083697)
                    ·
                      rfl

theorem cell22_3381114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_3381114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381114 prefixEnd_3381114 := by exact prefixLift 3381114
  have htrace : WordTrace (prefixWord ++ tailWord_3381114) baseStart_3381114 baseEnd_3381114 := by
    simpa [prefixWord, tailWord_3381114, baseEnd_3381114] using wordTrace_append hprefix tailTrace_3381114
  have hstable : (prefixWord ++ tailWord_3381114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381114).length < 2 ^ (prefixWord ++ tailWord_3381114).sum := by decide
  have hdescent : baseEnd_3381114 < baseStart_3381114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381146 : List Nat := [3, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_3381146 : Nat := 118140960795 + 3381146 * 2 ^ 59
def prefixEnd_3381146 : Nat := 4983230072969 + 3 ^ 40 * 3381146 * 2
def baseEnd_3381146 : Nat := 385811791339318552094533

theorem tailTrace_3381146 : CollatzResearch.WordTrace tailWord_3381146 prefixEnd_3381146 385811791339318552094533 := by
  unfold tailWord_3381146
  simp only [CollatzResearch.WordTrace]
  refine ⟨30830131452173242652116823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82213683872461980405644861 30830131452173242652116823)
  ·
    refine ⟨46245197178259863978175235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30830131452173242652116823 46245197178259863978175235)
    ·
      refine ⟨69367795767389795967262853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46245197178259863978175235 69367795767389795967262853)
      ·
        refine ⟨13006461706385586743861785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69367795767389795967262853 13006461706385586743861785)
        ·
          refine ⟨9754846279789190057896339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006461706385586743861785 9754846279789190057896339)
          ·
            refine ⟨14632269419683785086844509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754846279789190057896339 14632269419683785086844509)
            ·
              refine ⟨5487101032381419407566691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14632269419683785086844509 5487101032381419407566691)
              ·
                refine ⟨8230651548572129111350037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487101032381419407566691 8230651548572129111350037)
                ·
                  refine ⟨385811791339318552094533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8230651548572129111350037 385811791339318552094533)
                  ·
                    rfl

theorem cell22_3381146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_3381146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381146 prefixEnd_3381146 := by exact prefixLift 3381146
  have htrace : WordTrace (prefixWord ++ tailWord_3381146) baseStart_3381146 baseEnd_3381146 := by
    simpa [prefixWord, tailWord_3381146, baseEnd_3381146] using wordTrace_append hprefix tailTrace_3381146
  have hstable : (prefixWord ++ tailWord_3381146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381146).length < 2 ^ (prefixWord ++ tailWord_3381146).sum := by decide
  have hdescent : baseEnd_3381146 < baseStart_3381146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381176 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 2, 4]
def baseStart_3381176 : Nat := 118140960795 + 3381176 * 2 ^ 59
def prefixEnd_3381176 : Nat := 4983230072969 + 3 ^ 40 * 3381176 * 2
def baseEnd_3381176 : Nat := 1157445643631045578033507

theorem tailTrace_3381176 : CollatzResearch.WordTrace tailWord_3381176 prefixEnd_3381176 1157445643631045578033507 := by
  unfold tailWord_3381176
  simp only [CollatzResearch.WordTrace]
  refine ⟨61660809999292142866029691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82214413332389523821372921 61660809999292142866029691)
  ·
    refine ⟨92491214998938214299044537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61660809999292142866029691 92491214998938214299044537)
    ·
      refine ⟨69368411249203660724283403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92491214998938214299044537 69368411249203660724283403)
      ·
        refine ⟨104052616873805491086425105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69368411249203660724283403 104052616873805491086425105)
        ·
          refine ⟨78039462655354118314818829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104052616873805491086425105 78039462655354118314818829)
          ·
            refine ⟨29264798495757794368057061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78039462655354118314818829 29264798495757794368057061)
            ·
              refine ⟨5487149717954586444010699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29264798495757794368057061 5487149717954586444010699)
              ·
                refine ⟨8230724576931879666016049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487149717954586444010699 8230724576931879666016049)
                ·
                  refine ⟨6173043432698909749512037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8230724576931879666016049 6173043432698909749512037)
                  ·
                    refine ⟨1157445643631045578033507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173043432698909749512037 1157445643631045578033507)
                    ·
                      rfl

theorem cell22_3381176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 2, 4].length) (baseStart_3381176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381176 prefixEnd_3381176 := by exact prefixLift 3381176
  have htrace : WordTrace (prefixWord ++ tailWord_3381176) baseStart_3381176 baseEnd_3381176 := by
    simpa [prefixWord, tailWord_3381176, baseEnd_3381176] using wordTrace_append hprefix tailTrace_3381176
  have hstable : (prefixWord ++ tailWord_3381176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381176).length < 2 ^ (prefixWord ++ tailWord_3381176).sum := by decide
  have hdescent : baseEnd_3381176 < baseStart_3381176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381212 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3381212 : Nat := 118140960795 + 3381212 * 2 ^ 59
def prefixEnd_3381212 : Nat := 4983230072969 + 3 ^ 40 * 3381212 * 2
def baseEnd_3381212 : Nat := 1157457967166753484133397

theorem tailTrace_3381212 : CollatzResearch.WordTrace tailWord_3381212 prefixEnd_3381212 1157457967166753484133397 := by
  unfold tailWord_3381212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61661466513226931940184945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82215288684302575920246593 61661466513226931940184945)
  ·
    refine ⟨46246099884920198955138709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61661466513226931940184945 46246099884920198955138709)
    ·
      refine ⟨2167785932105634326022127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46246099884920198955138709 2167785932105634326022127)
      ·
        refine ⟨3251678898158451489033191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167785932105634326022127 3251678898158451489033191)
        ·
          refine ⟨4877518347237677233549787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251678898158451489033191 4877518347237677233549787)
          ·
            refine ⟨7316277520856515850324681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877518347237677233549787 7316277520856515850324681)
            ·
              refine ⟨5487208140642386887743511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7316277520856515850324681 5487208140642386887743511)
              ·
                refine ⟨8230812210963580331615267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487208140642386887743511 8230812210963580331615267)
                ·
                  refine ⟨12346218316445370497422901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230812210963580331615267 12346218316445370497422901)
                  ·
                    refine ⟨1157457967166753484133397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12346218316445370497422901 1157457967166753484133397)
                    ·
                      rfl

theorem cell22_3381212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3381212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381212 prefixEnd_3381212 := by exact prefixLift 3381212
  have htrace : WordTrace (prefixWord ++ tailWord_3381212) baseStart_3381212 baseEnd_3381212 := by
    simpa [prefixWord, tailWord_3381212, baseEnd_3381212] using wordTrace_append hprefix tailTrace_3381212
  have hstable : (prefixWord ++ tailWord_3381212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381212).length < 2 ^ (prefixWord ++ tailWord_3381212).sum := by decide
  have hdescent : baseEnd_3381212 < baseStart_3381212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381253 : List Nat := [1, 3, 1, 1, 2, 6, 1, 2, 5]
def baseStart_3381253 : Nat := 118140960795 + 3381253 * 2 ^ 59
def prefixEnd_3381253 : Nat := 4983230072969 + 3 ^ 40 * 3381253 * 2
def baseEnd_3381253 : Nat := 385824000768214347952757

theorem tailTrace_3381253 : CollatzResearch.WordTrace tailWord_3381253 prefixEnd_3381253 385824000768214347952757 := by
  unfold tailWord_3381253
  simp only [CollatzResearch.WordTrace]
  refine ⟨123324428419305327882612413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82216285612870218588408275 123324428419305327882612413)
  ·
    refine ⟨46246660657239497955979655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123324428419305327882612413 46246660657239497955979655)
    ·
      refine ⟨69369990985859246933969483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46246660657239497955979655 69369990985859246933969483)
      ·
        refine ⟨104054986478788870400954225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69369990985859246933969483 104054986478788870400954225)
        ·
          refine ⟨78041239859091652800715669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104054986478788870400954225 78041239859091652800715669)
          ·
            refine ⟨3658183118394921225033547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78041239859091652800715669 3658183118394921225033547)
            ·
              refine ⟨5487274677592381837550321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658183118394921225033547 5487274677592381837550321)
              ·
                refine ⟨4115456008194286378162741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487274677592381837550321 4115456008194286378162741)
                ·
                  refine ⟨385824000768214347952757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4115456008194286378162741 385824000768214347952757)
                  ·
                    rfl

theorem cell22_3381253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 5].length) (baseStart_3381253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381253 prefixEnd_3381253 := by exact prefixLift 3381253
  have htrace : WordTrace (prefixWord ++ tailWord_3381253) baseStart_3381253 baseEnd_3381253 := by
    simpa [prefixWord, tailWord_3381253, baseEnd_3381253] using wordTrace_append hprefix tailTrace_3381253
  have hstable : (prefixWord ++ tailWord_3381253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381253).length < 2 ^ (prefixWord ++ tailWord_3381253).sum := by decide
  have hdescent : baseEnd_3381253 < baseStart_3381253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381264 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 10]
def baseStart_3381264 : Nat := 118140960795 + 3381264 * 2 ^ 59
def prefixEnd_3381264 : Nat := 4983230072969 + 3 ^ 40 * 3381264 * 2
def baseEnd_3381264 : Nat := 385825255943147560611079

theorem tailTrace_3381264 : CollatzResearch.WordTrace tailWord_3381264 prefixEnd_3381264 385825255943147560611079 := by
  unfold tailWord_3381264
  simp only [CollatzResearch.WordTrace]
  refine ⟨61662414811132738380631423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82216553081510317840841897 61662414811132738380631423)
  ·
    refine ⟨92493622216699107570947135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61662414811132738380631423 92493622216699107570947135)
    ·
      refine ⟨138740433325048661356420703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92493622216699107570947135 138740433325048661356420703)
      ·
        refine ⟨208110649987572992034631055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138740433325048661356420703 208110649987572992034631055)
        ·
          refine ⟨312165974981359488051946583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208110649987572992034631055 312165974981359488051946583)
          ·
            refine ⟨468248962472039232077919875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312165974981359488051946583 468248962472039232077919875)
            ·
              refine ⟨702373443708058848116879813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468248962472039232077919875 702373443708058848116879813)
              ·
                refine ⟨131695020695261034021914965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702373443708058848116879813 131695020695261034021914965)
                ·
                  refine ⟨385825255943147560611079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 131695020695261034021914965 385825255943147560611079)
                  ·
                    rfl

theorem cell22_3381264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 10].length) (baseStart_3381264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381264 prefixEnd_3381264 := by exact prefixLift 3381264
  have htrace : WordTrace (prefixWord ++ tailWord_3381264) baseStart_3381264 baseEnd_3381264 := by
    simpa [prefixWord, tailWord_3381264, baseEnd_3381264] using wordTrace_append hprefix tailTrace_3381264
  have hstable : (prefixWord ++ tailWord_3381264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381264).length < 2 ^ (prefixWord ++ tailWord_3381264).sum := by decide
  have hdescent : baseEnd_3381264 < baseStart_3381264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381283 : List Nat := [1, 1, 1, 4, 3, 1, 4, 2, 1, 4]
def baseStart_3381283 : Nat := 118140960795 + 3381283 * 2 ^ 59
def prefixEnd_3381283 : Nat := 4983230072969 + 3 ^ 40 * 3381283 * 2
def baseEnd_3381283 : Nat := 1157482271917732965608179

theorem tailTrace_3381283 : CollatzResearch.WordTrace tailWord_3381283 prefixEnd_3381283 1157482271917732965608179 := by
  unfold tailWord_3381283
  simp only [CollatzResearch.WordTrace]
  refine ⟨123325522609196643006204503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82217015072797762004136335 123325522609196643006204503)
  ·
    refine ⟨184988283913794964509306755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123325522609196643006204503 184988283913794964509306755)
    ·
      refine ⟨277482425870692446763960133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184988283913794964509306755 277482425870692446763960133)
      ·
        refine ⟨52027954850754833768242525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277482425870692446763960133 52027954850754833768242525)
        ·
          refine ⟨19510483069033062663090947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52027954850754833768242525 19510483069033062663090947)
          ·
            refine ⟨29265724603549593994636421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19510483069033062663090947 29265724603549593994636421)
            ·
              refine ⟨5487323363165548873994329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29265724603549593994636421 5487323363165548873994329)
              ·
                refine ⟨4115492522374161655495747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487323363165548873994329 4115492522374161655495747)
                ·
                  refine ⟨6173238783561242483243621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115492522374161655495747 6173238783561242483243621)
                  ·
                    refine ⟨1157482271917732965608179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173238783561242483243621 1157482271917732965608179)
                    ·
                      rfl

theorem cell22_3381283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 1, 4].length) (baseStart_3381283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381283 prefixEnd_3381283 := by exact prefixLift 3381283
  have htrace : WordTrace (prefixWord ++ tailWord_3381283) baseStart_3381283 baseEnd_3381283 := by
    simpa [prefixWord, tailWord_3381283, baseEnd_3381283] using wordTrace_append hprefix tailTrace_3381283
  have hstable : (prefixWord ++ tailWord_3381283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381283).length < 2 ^ (prefixWord ++ tailWord_3381283).sum := by decide
  have hdescent : baseEnd_3381283 < baseStart_3381283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381311 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 4, 4]
def baseStart_3381311 : Nat := 118140960795 + 3381311 * 2 ^ 59
def prefixEnd_3381311 : Nat := 4983230072969 + 3 ^ 40 * 3381311 * 2
def baseEnd_3381311 : Nat := 1157491856889950225908093

theorem tailTrace_3381311 : CollatzResearch.WordTrace tailWord_3381311 prefixEnd_3381311 1157491856889950225908093 := by
  unfold tailWord_3381311
  simp only [CollatzResearch.WordTrace]
  refine ⟨123326543853095203788223787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82217695902063469192149191 123326543853095203788223787)
  ·
    refine ⟨184989815779642805682335681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123326543853095203788223787 184989815779642805682335681)
    ·
      refine ⟨138742361834732104261751761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184989815779642805682335681 138742361834732104261751761)
      ·
        refine ⟨104056771376049078196313821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138742361834732104261751761 104056771376049078196313821)
        ·
          refine ⟨39021289266018404323617683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104056771376049078196313821 39021289266018404323617683)
          ·
            refine ⟨58531933899027606485426525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39021289266018404323617683 58531933899027606485426525)
            ·
              refine ⟨21949475212135352432034947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58531933899027606485426525 21949475212135352432034947)
              ·
                refine ⟨32924212818203028648052421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21949475212135352432034947 32924212818203028648052421)
                ·
                  refine ⟨6173289903413067871509829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32924212818203028648052421 6173289903413067871509829)
                  ·
                    refine ⟨1157491856889950225908093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173289903413067871509829 1157491856889950225908093)
                    ·
                      rfl

theorem cell22_3381311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_3381311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381311 prefixEnd_3381311 := by exact prefixLift 3381311
  have htrace : WordTrace (prefixWord ++ tailWord_3381311) baseStart_3381311 baseEnd_3381311 := by
    simpa [prefixWord, tailWord_3381311, baseEnd_3381311] using wordTrace_append hprefix tailTrace_3381311
  have hstable : (prefixWord ++ tailWord_3381311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381311).length < 2 ^ (prefixWord ++ tailWord_3381311).sum := by decide
  have hdescent : baseEnd_3381311 < baseStart_3381311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381326 : List Nat := [4, 1, 1, 1, 1, 4, 1, 9]
def baseStart_3381326 : Nat := 118140960795 + 3381326 * 2 ^ 59
def prefixEnd_3381326 : Nat := 4983230072969 + 3 ^ 40 * 3381326 * 2
def baseEnd_3381326 : Nat := 128610776855166131864783

theorem tailTrace_3381326 : CollatzResearch.WordTrace tailWord_3381326 prefixEnd_3381326 128610776855166131864783 := by
  unfold tailWord_3381326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15415886368505107668752479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82218060632027240900013221 15415886368505107668752479)
  ·
    refine ⟨23123829552757661503128719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15415886368505107668752479 23123829552757661503128719)
    ·
      refine ⟨34685744329136492254693079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23123829552757661503128719 34685744329136492254693079)
      ·
        refine ⟨52028616493704738382039619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34685744329136492254693079 52028616493704738382039619)
        ·
          refine ⟨78042924740557107573059429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52028616493704738382039619 78042924740557107573059429)
          ·
            refine ⟨14633048388854457669948643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78042924740557107573059429 14633048388854457669948643)
            ·
              refine ⟨21949572583281686504922965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633048388854457669948643 21949572583281686504922965)
              ·
                refine ⟨128610776855166131864783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21949572583281686504922965 128610776855166131864783)
                ·
                  rfl

theorem cell22_3381326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_3381326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381326 prefixEnd_3381326 := by exact prefixLift 3381326
  have htrace : WordTrace (prefixWord ++ tailWord_3381326) baseStart_3381326 baseEnd_3381326 := by
    simpa [prefixWord, tailWord_3381326, baseEnd_3381326] using wordTrace_append hprefix tailTrace_3381326
  have hstable : (prefixWord ++ tailWord_3381326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381326).length < 2 ^ (prefixWord ++ tailWord_3381326).sum := by decide
  have hdescent : baseEnd_3381326 < baseStart_3381326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381334 : List Nat := [5, 2, 2, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3381334 : Nat := 118140960795 + 3381334 * 2 ^ 59
def prefixEnd_3381334 : Nat := 4983230072969 + 3 ^ 40 * 3381334 * 2
def baseEnd_3381334 : Nat := 1157499730259985832583023

theorem tailTrace_3381334 : CollatzResearch.WordTrace tailWord_3381334 prefixEnd_3381334 1157499730259985832583023 := by
  unfold tailWord_3381334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7707961420750742419769441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82218255154674585810874037 7707961420750742419769441)
  ·
    refine ⟨5780971065563056814827081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7707961420750742419769441 5780971065563056814827081)
    ·
      refine ⟨4335728299172292611120311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5780971065563056814827081 4335728299172292611120311)
      ·
        refine ⟨6503592448758438916680467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335728299172292611120311 6503592448758438916680467)
        ·
          refine ⟨9755388673137658375020701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6503592448758438916680467 9755388673137658375020701)
          ·
            refine ⟨3658270752426621890632763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9755388673137658375020701 3658270752426621890632763)
            ·
              refine ⟨5487406128639932835949145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658270752426621890632763 5487406128639932835949145)
              ·
                refine ⟨4115554596479949626961859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5487406128639932835949145 4115554596479949626961859)
                ·
                  refine ⟨6173331894719924440442789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115554596479949626961859 6173331894719924440442789)
                  ·
                    refine ⟨1157499730259985832583023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173331894719924440442789 1157499730259985832583023)
                    ·
                      rfl

theorem cell22_3381334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3381334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381334 prefixEnd_3381334 := by exact prefixLift 3381334
  have htrace : WordTrace (prefixWord ++ tailWord_3381334) baseStart_3381334 baseEnd_3381334 := by
    simpa [prefixWord, tailWord_3381334, baseEnd_3381334] using wordTrace_append hprefix tailTrace_3381334
  have hstable : (prefixWord ++ tailWord_3381334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381334).length < 2 ^ (prefixWord ++ tailWord_3381334).sum := by decide
  have hdescent : baseEnd_3381334 < baseStart_3381334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381422 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_3381422 : Nat := 118140960795 + 3381422 * 2 ^ 59
def prefixEnd_3381422 : Nat := 4983230072969 + 3 ^ 40 * 3381422 * 2
def baseEnd_3381422 : Nat := 385843284819460978794251

theorem tailTrace_3381422 : CollatzResearch.WordTrace tailWord_3381422 prefixEnd_3381422 385843284819460978794251 := by
  unfold tailWord_3381422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15416324044461633718189315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82220394903795379830343013 15416324044461633718189315)
  ·
    refine ⟨23124486066692450577283973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15416324044461633718189315 23124486066692450577283973)
    ·
      refine ⟨4335841137504834483240745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23124486066692450577283973 4335841137504834483240745)
      ·
        refine ⟨3251880853128625862430559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4335841137504834483240745 3251880853128625862430559)
        ·
          refine ⟨4877821279692938793645839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251880853128625862430559 4877821279692938793645839)
          ·
            refine ⟨7316731919539408190468759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877821279692938793645839 7316731919539408190468759)
            ·
              refine ⟨10975097879309112285703139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316731919539408190468759 10975097879309112285703139)
              ·
                refine ⟨16462646818963668428554709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10975097879309112285703139 16462646818963668428554709)
                ·
                  refine ⟨385843284819460978794251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16462646818963668428554709 385843284819460978794251)
                  ·
                    rfl

theorem cell22_3381422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_3381422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381422 prefixEnd_3381422 := by exact prefixLift 3381422
  have htrace : WordTrace (prefixWord ++ tailWord_3381422) baseStart_3381422 baseEnd_3381422 := by
    simpa [prefixWord, tailWord_3381422, baseEnd_3381422] using wordTrace_append hprefix tailTrace_3381422
  have hstable : (prefixWord ++ tailWord_3381422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381422).length < 2 ^ (prefixWord ++ tailWord_3381422).sum := by decide
  have hdescent : baseEnd_3381422 < baseStart_3381422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381433 : List Nat := [1, 2, 1, 4, 1, 2, 4, 1, 6]
def baseStart_3381433 : Nat := 118140960795 + 3381433 * 2 ^ 59
def prefixEnd_3381433 : Nat := 4983230072969 + 3 ^ 40 * 3381433 * 2
def baseEnd_3381433 : Nat := 385844539994394191452573

theorem tailTrace_3381433 : CollatzResearch.WordTrace tailWord_3381433 prefixEnd_3381433 385844539994394191452573 := by
  unfold tailWord_3381433
  simp only [CollatzResearch.WordTrace]
  refine ⟨123330993558653218624164953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82220662372435479082776635 123330993558653218624164953)
  ·
    refine ⟨92498245168989913968123715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123330993558653218624164953 92498245168989913968123715)
    ·
      refine ⟨138747367753484870952185573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92498245168989913968123715 138747367753484870952185573)
      ·
        refine ⟨26015131453778413303534795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138747367753484870952185573 26015131453778413303534795)
        ·
          refine ⟨39022697180667619955302193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26015131453778413303534795 39022697180667619955302193)
          ·
            refine ⟨29267022885500714966476645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39022697180667619955302193 29267022885500714966476645)
            ·
              refine ⟨5487566791031384056214371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29267022885500714966476645 5487566791031384056214371)
              ·
                refine ⟨8231350186547076084321557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487566791031384056214371 8231350186547076084321557)
                ·
                  refine ⟨385844539994394191452573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8231350186547076084321557 385844539994394191452573)
                  ·
                    rfl

theorem cell22_3381433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 6].length) (baseStart_3381433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381433 prefixEnd_3381433 := by exact prefixLift 3381433
  have htrace : WordTrace (prefixWord ++ tailWord_3381433) baseStart_3381433 baseEnd_3381433 := by
    simpa [prefixWord, tailWord_3381433, baseEnd_3381433] using wordTrace_append hprefix tailTrace_3381433
  have hstable : (prefixWord ++ tailWord_3381433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381433).length < 2 ^ (prefixWord ++ tailWord_3381433).sum := by decide
  have hdescent : baseEnd_3381433 < baseStart_3381433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381463 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3381463 : Nat := 118140960795 + 3381463 * 2 ^ 59
def prefixEnd_3381463 : Nat := 4983230072969 + 3 ^ 40 * 3381463 * 2
def baseEnd_3381463 : Nat := 1157543889596272496107627

theorem tailTrace_3381463 : CollatzResearch.WordTrace tailWord_3381463 prefixEnd_3381463 1157543889596272496107627 := by
  unfold tailWord_3381463
  simp only [CollatzResearch.WordTrace]
  refine ⟨123332087748544533747757043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82221391832363022498504695 123332087748544533747757043)
  ·
    refine ⟨184998131622816800621635565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123332087748544533747757043 184998131622816800621635565)
    ·
      refine ⟨69374299358556300233113337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184998131622816800621635565 69374299358556300233113337)
      ·
        refine ⟨52030724518917225174835003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69374299358556300233113337 52030724518917225174835003)
        ·
          refine ⟨78046086778375837762252505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52030724518917225174835003 78046086778375837762252505)
          ·
            refine ⟨58534565083781878321689379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78046086778375837762252505 58534565083781878321689379)
            ·
              refine ⟨87801847625672817482534069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58534565083781878321689379 87801847625672817482534069)
              ·
                refine ⟨8231423214906826638987569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87801847625672817482534069 8231423214906826638987569)
                ·
                  refine ⟨6173567411180119979240677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231423214906826638987569 6173567411180119979240677)
                  ·
                    refine ⟨1157543889596272496107627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173567411180119979240677 1157543889596272496107627)
                    ·
                      rfl

theorem cell22_3381463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3381463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381463 prefixEnd_3381463 := by exact prefixLift 3381463
  have htrace : WordTrace (prefixWord ++ tailWord_3381463) baseStart_3381463 baseEnd_3381463 := by
    simpa [prefixWord, tailWord_3381463, baseEnd_3381463] using wordTrace_append hprefix tailTrace_3381463
  have hstable : (prefixWord ++ tailWord_3381463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381463).length < 2 ^ (prefixWord ++ tailWord_3381463).sum := by decide
  have hdescent : baseEnd_3381463 < baseStart_3381463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381480 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 2, 4]
def baseStart_3381480 : Nat := 118140960795 + 3381480 * 2 ^ 59
def prefixEnd_3381480 : Nat := 4983230072969 + 3 ^ 40 * 3381480 * 2
def baseEnd_3381480 : Nat := 1157549709043690118432575

theorem tailTrace_3381480 : CollatzResearch.WordTrace tailWord_3381480 prefixEnd_3381480 1157549709043690118432575 := by
  unfold tailWord_3381480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61666353894741472825562947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82221805192988630434083929 61666353894741472825562947)
  ·
    refine ⟨92499530842112209238344421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61666353894741472825562947 92499530842112209238344421)
    ·
      refine ⟨17343662032896039232189579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92499530842112209238344421 17343662032896039232189579)
      ·
        refine ⟨26015493049344058848284369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17343662032896039232189579 26015493049344058848284369)
        ·
          refine ⟨19511619787008044136213277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26015493049344058848284369 19511619787008044136213277)
          ·
            refine ⟨7316857420128016551079979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19511619787008044136213277 7316857420128016551079979)
            ·
              refine ⟨10975286130192024826619969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316857420128016551079979 10975286130192024826619969)
              ·
                refine ⟨8231464597644018619964977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10975286130192024826619969 8231464597644018619964977)
                ·
                  refine ⟨6173598448233013964973733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231464597644018619964977 6173598448233013964973733)
                  ·
                    refine ⟨1157549709043690118432575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173598448233013964973733 1157549709043690118432575)
                    ·
                      rfl

theorem cell22_3381480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_3381480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381480 prefixEnd_3381480 := by exact prefixLift 3381480
  have htrace : WordTrace (prefixWord ++ tailWord_3381480) baseStart_3381480 baseEnd_3381480 := by
    simpa [prefixWord, tailWord_3381480, baseEnd_3381480] using wordTrace_append hprefix tailTrace_3381480
  have hstable : (prefixWord ++ tailWord_3381480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381480).length < 2 ^ (prefixWord ++ tailWord_3381480).sum := by decide
  have hdescent : baseEnd_3381480 < baseStart_3381480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381540 : List Nat := [2, 3, 1, 3, 1, 2, 1, 4, 5]
def baseStart_3381540 : Nat := 118140960795 + 3381540 * 2 ^ 59
def prefixEnd_3381540 : Nat := 4983230072969 + 3 ^ 40 * 3381540 * 2
def baseEnd_3381540 : Nat := 385856749423289987310797

theorem tailTrace_3381540 : CollatzResearch.WordTrace tailWord_3381540 prefixEnd_3381540 385856749423289987310797 := by
  unfold tailWord_3381540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61667448084632787949155037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82223264112843717265540049 61667448084632787949155037)
  ·
    refine ⟨23125293031737295480933139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61667448084632787949155037 23125293031737295480933139)
    ·
      refine ⟨34687939547605943221399709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23125293031737295480933139 34687939547605943221399709)
      ·
        refine ⟨13007977330352228708024891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34687939547605943221399709 13007977330352228708024891)
        ·
          refine ⟨19511965995528343062037337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13007977330352228708024891 19511965995528343062037337)
          ·
            refine ⟨14633974496646257296528003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19511965995528343062037337 14633974496646257296528003)
            ·
              refine ⟨21950961744969385944792005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633974496646257296528003 21950961744969385944792005)
              ·
                refine ⟨4115805327181759864648501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21950961744969385944792005 4115805327181759864648501)
                ·
                  refine ⟨385856749423289987310797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4115805327181759864648501 385856749423289987310797)
                  ·
                    rfl

theorem cell22_3381540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_3381540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381540 prefixEnd_3381540 := by exact prefixLift 3381540
  have htrace : WordTrace (prefixWord ++ tailWord_3381540) baseStart_3381540 baseEnd_3381540 := by
    simpa [prefixWord, tailWord_3381540, baseEnd_3381540] using wordTrace_append hprefix tailTrace_3381540
  have hstable : (prefixWord ++ tailWord_3381540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381540).length < 2 ^ (prefixWord ++ tailWord_3381540).sum := by decide
  have hdescent : baseEnd_3381540 < baseStart_3381540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381583 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 3, 5]
def baseStart_3381583 : Nat := 118140960795 + 3381583 * 2 ^ 59
def prefixEnd_3381583 : Nat := 4983230072969 + 3 ^ 40 * 3381583 * 2
def baseEnd_3381583 : Nat := 1157584968048632183107259

theorem tailTrace_3381583 : CollatzResearch.WordTrace tailWord_3381583 prefixEnd_3381583 1157584968048632183107259 := by
  unfold tailWord_3381583
  simp only [CollatzResearch.WordTrace]
  refine ⟨123336464508109794242125403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82224309672073196161416935 123336464508109794242125403)
  ·
    refine ⟨185004696762164691363188105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123336464508109794242125403 185004696762164691363188105)
    ·
      refine ⟨138753522571623518522391079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185004696762164691363188105 138753522571623518522391079)
      ·
        refine ⟨208130283857435277783586619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138753522571623518522391079 208130283857435277783586619)
        ·
          refine ⟨312195425786152916675379929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208130283857435277783586619 312195425786152916675379929)
          ·
            refine ⟨234146569339614687506534947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312195425786152916675379929 234146569339614687506534947)
            ·
              refine ⟨351219854009422031259802421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234146569339614687506534947 351219854009422031259802421)
              ·
                refine ⟨32926861313383315430606477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351219854009422031259802421 32926861313383315430606477)
                ·
                  refine ⟨12347572992518743286477429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32926861313383315430606477 12347572992518743286477429)
                  ·
                    refine ⟨1157584968048632183107259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12347572992518743286477429 1157584968048632183107259)
                    ·
                      rfl

theorem cell22_3381583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_3381583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381583 prefixEnd_3381583 := by exact prefixLift 3381583
  have htrace : WordTrace (prefixWord ++ tailWord_3381583) baseStart_3381583 baseEnd_3381583 := by
    simpa [prefixWord, tailWord_3381583, baseEnd_3381583] using wordTrace_append hprefix tailTrace_3381583
  have hstable : (prefixWord ++ tailWord_3381583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381583).length < 2 ^ (prefixWord ++ tailWord_3381583).sum := by decide
  have hdescent : baseEnd_3381583 < baseStart_3381583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381602 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_3381602 : Nat := 118140960795 + 3381602 * 2 ^ 59
def prefixEnd_3381602 : Nat := 4983230072969 + 3 ^ 40 * 3381602 * 2
def baseEnd_3381602 : Nat := 385863824045640822294067

theorem tailTrace_3381602 : CollatzResearch.WordTrace tailWord_3381602 prefixEnd_3381602 385863824045640822294067 := by
  unfold tailWord_3381602
  simp only [CollatzResearch.WordTrace]
  refine ⟨30834289373760240121766765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82224771663360640324711373 30834289373760240121766765)
  ·
    refine ⟨11562858515160090045662537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30834289373760240121766765 11562858515160090045662537)
    ·
      refine ⟨8672143886370067534246903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11562858515160090045662537 8672143886370067534246903)
      ·
        refine ⟨13008215829555101301370355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8672143886370067534246903 13008215829555101301370355)
        ·
          refine ⟨19512323744332651952055533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13008215829555101301370355 19512323744332651952055533)
          ·
            refine ⟨7317121404124744482020825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19512323744332651952055533 7317121404124744482020825)
            ·
              refine ⟨5487841053093558361515619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7317121404124744482020825 5487841053093558361515619)
              ·
                refine ⟨8231761579640337542273429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487841053093558361515619 8231761579640337542273429)
                ·
                  refine ⟨385863824045640822294067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8231761579640337542273429 385863824045640822294067)
                  ·
                    rfl

theorem cell22_3381602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_3381602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381602 prefixEnd_3381602 := by exact prefixLift 3381602
  have htrace : WordTrace (prefixWord ++ tailWord_3381602) baseStart_3381602 baseEnd_3381602 := by
    simpa [prefixWord, tailWord_3381602, baseEnd_3381602] using wordTrace_append hprefix tailTrace_3381602
  have hstable : (prefixWord ++ tailWord_3381602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381602).length < 2 ^ (prefixWord ++ tailWord_3381602).sum := by decide
  have hdescent : baseEnd_3381602 < baseStart_3381602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381720 : List Nat := [2, 1, 2, 2, 2, 1, 1, 5, 6]
def baseStart_3381720 : Nat := 118140960795 + 3381720 * 2 ^ 59
def prefixEnd_3381720 : Nat := 4983230072969 + 3 ^ 40 * 3381720 * 2
def baseEnd_3381720 : Nat := 385877288649469830810613

theorem tailTrace_3381720 : CollatzResearch.WordTrace tailWord_3381720 prefixEnd_3381720 385877288649469830810613 := by
  unfold tailWord_3381720
  simp only [CollatzResearch.WordTrace]
  refine ⟨61670730654306733319931307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82227640872408977759908409 61670730654306733319931307)
  ·
    refine ⟨92506095981460099979896961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61670730654306733319931307 92506095981460099979896961)
    ·
      refine ⟨69379571986095074984922721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92506095981460099979896961 69379571986095074984922721)
      ·
        refine ⟨52034678989571306238692041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69379571986095074984922721 52034678989571306238692041)
        ·
          refine ⟨39026009242178479679019031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52034678989571306238692041 39026009242178479679019031)
          ·
            refine ⟨58539013863267719518528547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39026009242178479679019031 58539013863267719518528547)
            ·
              refine ⟨87808520794901579277792821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58539013863267719518528547 87808520794901579277792821)
              ·
                refine ⟨8232048824522023057293077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87808520794901579277792821 8232048824522023057293077)
                ·
                  refine ⟨385877288649469830810613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8232048824522023057293077 385877288649469830810613)
                  ·
                    rfl

theorem cell22_3381720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 6].length) (baseStart_3381720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381720 prefixEnd_3381720 := by exact prefixLift 3381720
  have htrace : WordTrace (prefixWord ++ tailWord_3381720) baseStart_3381720 baseEnd_3381720 := by
    simpa [prefixWord, tailWord_3381720, baseEnd_3381720] using wordTrace_append hprefix tailTrace_3381720
  have hstable : (prefixWord ++ tailWord_3381720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381720).length < 2 ^ (prefixWord ++ tailWord_3381720).sum := by decide
  have hdescent : baseEnd_3381720 < baseStart_3381720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381752 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 4, 3]
def baseStart_3381752 : Nat := 118140960795 + 3381752 * 2 ^ 59
def prefixEnd_3381752 : Nat := 4983230072969 + 3 ^ 40 * 3381752 * 2
def baseEnd_3381752 : Nat := 1157642820202372075631741

theorem tailTrace_3381752 : CollatzResearch.WordTrace tailWord_3381752 prefixEnd_3381752 1157642820202372075631741 := by
  unfold tailWord_3381752
  simp only [CollatzResearch.WordTrace]
  refine ⟨61671314222248768052513755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82228418962998357403351673 61671314222248768052513755)
  ·
    refine ⟨92506971333373152078770633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61671314222248768052513755 92506971333373152078770633)
    ·
      refine ⟨69380228500029864059077975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92506971333373152078770633 69380228500029864059077975)
      ·
        refine ⟨104070342750044796088616963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69380228500029864059077975 104070342750044796088616963)
        ·
          refine ⟨156105514125067194132925445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104070342750044796088616963 156105514125067194132925445)
          ·
            refine ⟨29269783898450098899923521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156105514125067194132925445 29269783898450098899923521)
            ·
              refine ⟨21952337923837574174942641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29269783898450098899923521 21952337923837574174942641)
              ·
                refine ⟨16464253442878180631206981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21952337923837574174942641 16464253442878180631206981)
                ·
                  refine ⟨3087047520539658868351309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16464253442878180631206981 3087047520539658868351309)
                  ·
                    refine ⟨1157642820202372075631741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087047520539658868351309 1157642820202372075631741)
                    ·
                      rfl

theorem cell22_3381752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 3].length) (baseStart_3381752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381752 prefixEnd_3381752 := by exact prefixLift 3381752
  have htrace : WordTrace (prefixWord ++ tailWord_3381752) baseStart_3381752 baseEnd_3381752 := by
    simpa [prefixWord, tailWord_3381752, baseEnd_3381752] using wordTrace_append hprefix tailTrace_3381752
  have hstable : (prefixWord ++ tailWord_3381752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381752).length < 2 ^ (prefixWord ++ tailWord_3381752).sum := by decide
  have hdescent : baseEnd_3381752 < baseStart_3381752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381831 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 3, 3]
def baseStart_3381831 : Nat := 118140960795 + 3381831 * 2 ^ 59
def prefixEnd_3381831 : Nat := 4983230072969 + 3 ^ 40 * 3381831 * 2
def baseEnd_3381831 : Nat := 1157669863516842202906499

theorem tailTrace_3381831 : CollatzResearch.WordTrace tailWord_3381831 prefixEnd_3381831 1157669863516842202906499 := by
  unfold tailWord_3381831
  simp only [CollatzResearch.WordTrace]
  refine ⟨123345509811211332597153347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82230339874140888398102231 123345509811211332597153347)
  ·
    refine ⟨185018264716816998895730021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123345509811211332597153347 185018264716816998895730021)
    ·
      refine ⟨34690924634403187292949379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185018264716816998895730021 34690924634403187292949379)
      ·
        refine ⟨52036386951604780939424069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34690924634403187292949379 52036386951604780939424069)
        ·
          refine ⟨9756822553425896426142013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52036386951604780939424069 9756822553425896426142013)
          ·
            refine ⟨3658808457534711159803255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9756822553425896426142013 3658808457534711159803255)
            ·
              refine ⟨5488212686302066739704883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658808457534711159803255 5488212686302066739704883)
              ·
                refine ⟨8232319029453100109557325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488212686302066739704883 8232319029453100109557325)
                ·
                  refine ⟨3087119636044912541083997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8232319029453100109557325 3087119636044912541083997)
                  ·
                    refine ⟨1157669863516842202906499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087119636044912541083997 1157669863516842202906499)
                    ·
                      rfl

theorem cell22_3381831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_3381831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381831 prefixEnd_3381831 := by exact prefixLift 3381831
  have htrace : WordTrace (prefixWord ++ tailWord_3381831) baseStart_3381831 baseEnd_3381831 := by
    simpa [prefixWord, tailWord_3381831, baseEnd_3381831] using wordTrace_append hprefix tailTrace_3381831
  have hstable : (prefixWord ++ tailWord_3381831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381831).length < 2 ^ (prefixWord ++ tailWord_3381831).sum := by decide
  have hdescent : baseEnd_3381831 < baseStart_3381831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381842 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3381842 : Nat := 118140960795 + 3381842 * 2 ^ 59
def prefixEnd_3381842 : Nat := 4983230072969 + 3 ^ 40 * 3381842 * 2
def baseEnd_3381842 : Nat := 1157673629041641840881465

theorem tailTrace_3381842 : CollatzResearch.WordTrace tailWord_3381842 prefixEnd_3381842 1157673629041641840881465 := by
  unfold tailWord_3381842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30836477753542870368950945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82230607342780987650535853 30836477753542870368950945)
  ·
    refine ⟨23127358315157152776713209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30836477753542870368950945 23127358315157152776713209)
    ·
      refine ⟨17345518736367864582534907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23127358315157152776713209 17345518736367864582534907)
      ·
        refine ⟨26018278104551796873802361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17345518736367864582534907 26018278104551796873802361)
        ·
          refine ⟨19513708578413847655351771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26018278104551796873802361 19513708578413847655351771)
          ·
            refine ⟨29270562867620771483027657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19513708578413847655351771 29270562867620771483027657)
            ·
              refine ⟨21952922150715578612270743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29270562867620771483027657 21952922150715578612270743)
              ·
                refine ⟨32929383226073367918406115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21952922150715578612270743 32929383226073367918406115)
                ·
                  refine ⟨49394074839110051877609173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32929383226073367918406115 49394074839110051877609173)
                  ·
                    refine ⟨1157673629041641840881465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49394074839110051877609173 1157673629041641840881465)
                    ·
                      rfl

theorem cell22_3381842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3381842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381842 prefixEnd_3381842 := by exact prefixLift 3381842
  have htrace : WordTrace (prefixWord ++ tailWord_3381842) baseStart_3381842 baseEnd_3381842 := by
    simpa [prefixWord, tailWord_3381842, baseEnd_3381842] using wordTrace_append hprefix tailTrace_3381842
  have hstable : (prefixWord ++ tailWord_3381842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381842).length < 2 ^ (prefixWord ++ tailWord_3381842).sum := by decide
  have hdescent : baseEnd_3381842 < baseStart_3381842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381844 : List Nat := [2, 4, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3381844 : Nat := 118140960795 + 3381844 * 2 ^ 59
def prefixEnd_3381844 : Nat := 4983230072969 + 3 ^ 40 * 3381844 * 2
def baseEnd_3381844 : Nat := 385891437894171500777153

theorem tailTrace_3381844 : CollatzResearch.WordTrace tailWord_3381844 prefixEnd_3381844 385891437894171500777153 := by
  unfold tailWord_3381844
  simp only [CollatzResearch.WordTrace]
  refine ⟨61672991980082117908688293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82230655973442823878251057 61672991980082117908688293)
  ·
    refine ⟨11563685996265397107879055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61672991980082117908688293 11563685996265397107879055)
    ·
      refine ⟨17345528994398095661818583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11563685996265397107879055 17345528994398095661818583)
      ·
        refine ⟨26018293491597143492727875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17345528994398095661818583 26018293491597143492727875)
        ·
          refine ⟨39027440237395715239091813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26018293491597143492727875 39027440237395715239091813)
          ·
            refine ⟨7317645044511696607329715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39027440237395715239091813 7317645044511696607329715)
            ·
              refine ⟨10976467566767544910994573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317645044511696607329715 10976467566767544910994573)
              ·
                refine ⟨4116175337537829341622965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10976467566767544910994573 4116175337537829341622965)
                ·
                  refine ⟨385891437894171500777153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116175337537829341622965 385891437894171500777153)
                  ·
                    rfl

theorem cell22_3381844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3381844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381844 prefixEnd_3381844 := by exact prefixLift 3381844
  have htrace : WordTrace (prefixWord ++ tailWord_3381844) baseStart_3381844 baseEnd_3381844 := by
    simpa [prefixWord, tailWord_3381844, baseEnd_3381844] using wordTrace_append hprefix tailTrace_3381844
  have hstable : (prefixWord ++ tailWord_3381844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381844).length < 2 ^ (prefixWord ++ tailWord_3381844).sum := by decide
  have hdescent : baseEnd_3381844 < baseStart_3381844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381917 : List Nat := [1, 4, 2, 1, 1, 1, 2, 10]
def baseStart_3381917 : Nat := 118140960795 + 3381917 * 2 ^ 59
def prefixEnd_3381917 : Nat := 4983230072969 + 3 ^ 40 * 3381917 * 2
def baseEnd_3381917 : Nat := 128633255897151849472915

theorem tailTrace_3381917 : CollatzResearch.WordTrace tailWord_3381917 prefixEnd_3381917 128633255897151849472915 := by
  unfold tailWord_3381917
  simp only [CollatzResearch.WordTrace]
  refine ⟨123348646488899769284784005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82232430992599846189856003 123348646488899769284784005)
  ·
    refine ⟨23127871216668706740897001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123348646488899769284784005 23127871216668706740897001)
    ·
      refine ⟨17345903412501530055672751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23127871216668706740897001 17345903412501530055672751)
      ·
        refine ⟨26018855118752295083509127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17345903412501530055672751 26018855118752295083509127)
        ·
          refine ⟨39028282678128442625263691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26018855118752295083509127 39028282678128442625263691)
          ·
            refine ⟨58542424017192663937895537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39028282678128442625263691 58542424017192663937895537)
            ·
              refine ⟨43906818012894497953421653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58542424017192663937895537 43906818012894497953421653)
              ·
                refine ⟨128633255897151849472915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43906818012894497953421653 128633255897151849472915)
                ·
                  rfl

theorem cell22_3381917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 10].length) (baseStart_3381917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381917 prefixEnd_3381917 := by exact prefixLift 3381917
  have htrace : WordTrace (prefixWord ++ tailWord_3381917) baseStart_3381917 baseEnd_3381917 := by
    simpa [prefixWord, tailWord_3381917, baseEnd_3381917] using wordTrace_append hprefix tailTrace_3381917
  have hstable : (prefixWord ++ tailWord_3381917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381917).length < 2 ^ (prefixWord ++ tailWord_3381917).sum := by decide
  have hdescent : baseEnd_3381917 < baseStart_3381917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381966 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_3381966 : Nat := 118140960795 + 3381966 * 2 ^ 59
def prefixEnd_3381966 : Nat := 4983230072969 + 3 ^ 40 * 3381966 * 2
def baseEnd_3381966 : Nat := 1157716076775746850781085

theorem tailTrace_3381966 : CollatzResearch.WordTrace tailWord_3381966 prefixEnd_3381966 1157716076775746850781085 := by
  unfold tailWord_3381966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15418804208215281331664719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82233622443814833768878501 15418804208215281331664719)
  ·
    refine ⟨23128206312322921997497079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15418804208215281331664719 23128206312322921997497079)
    ·
      refine ⟨34692309468484382996245619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23128206312322921997497079 34692309468484382996245619)
      ·
        refine ⟨52038464202726574494368429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34692309468484382996245619 52038464202726574494368429)
        ·
          refine ⟨19514424076022465435388161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52038464202726574494368429 19514424076022465435388161)
          ·
            refine ⟨14635818057016849076541121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19514424076022465435388161 14635818057016849076541121)
            ·
              refine ⟨10976863542762636807405841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14635818057016849076541121 10976863542762636807405841)
              ·
                refine ⟨8232647657071977605554381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10976863542762636807405841 8232647657071977605554381)
                ·
                  refine ⟨3087242871401991602082893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8232647657071977605554381 3087242871401991602082893)
                  ·
                    refine ⟨1157716076775746850781085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087242871401991602082893 1157716076775746850781085)
                    ·
                      rfl

theorem cell22_3381966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_3381966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381966 prefixEnd_3381966 := by exact prefixLift 3381966
  have htrace : WordTrace (prefixWord ++ tailWord_3381966) baseStart_3381966 baseEnd_3381966 := by
    simpa [prefixWord, tailWord_3381966, baseEnd_3381966] using wordTrace_append hprefix tailTrace_3381966
  have hstable : (prefixWord ++ tailWord_3381966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381966).length < 2 ^ (prefixWord ++ tailWord_3381966).sum := by decide
  have hdescent : baseEnd_3381966 < baseStart_3381966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381983 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 1, 3]
def baseStart_3381983 : Nat := 118140960795 + 3381983 * 2 ^ 59
def prefixEnd_3381983 : Nat := 4983230072969 + 3 ^ 40 * 3381983 * 2
def baseEnd_3381983 : Nat := 1157721896223164473106033

theorem tailTrace_3381983 : CollatzResearch.WordTrace tailWord_3381983 prefixEnd_3381983 1157721896223164473106033 := by
  unfold tailWord_3381983
  simp only [CollatzResearch.WordTrace]
  refine ⟨123351053706660662556686603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82234035804440441704457735 123351053706660662556686603)
  ·
    refine ⟨185026580559990993835029905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123351053706660662556686603 185026580559990993835029905)
    ·
      refine ⟨138769935419993245376272429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185026580559990993835029905 138769935419993245376272429)
      ·
        refine ⟨52038725782497467016102161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138769935419993245376272429 52038725782497467016102161)
        ·
          refine ⟨39029044336873100262076621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52038725782497467016102161 39029044336873100262076621)
          ·
            refine ⟨14635891626327412598278733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39029044336873100262076621 14635891626327412598278733)
            ·
              refine ⟨5488459359872779724354525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14635891626327412598278733 5488459359872779724354525)
              ·
                refine ⟨2058172259952292396632947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488459359872779724354525 2058172259952292396632947)
                ·
                  refine ⟨3087258389928438594949421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058172259952292396632947 3087258389928438594949421)
                  ·
                    refine ⟨1157721896223164473106033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087258389928438594949421 1157721896223164473106033)
                    ·
                      rfl

theorem cell22_3381983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_3381983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3381983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3381983 prefixEnd_3381983 := by exact prefixLift 3381983
  have htrace : WordTrace (prefixWord ++ tailWord_3381983) baseStart_3381983 baseEnd_3381983 := by
    simpa [prefixWord, tailWord_3381983, baseEnd_3381983] using wordTrace_append hprefix tailTrace_3381983
  have hstable : (prefixWord ++ tailWord_3381983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381983).length < 2 ^ (prefixWord ++ tailWord_3381983).sum := by decide
  have hdescent : baseEnd_3381983 < baseStart_3381983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382101 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_3382101 : Nat := 118140960795 + 3382101 * 2 ^ 59
def prefixEnd_3382101 : Nat := 4983230072969 + 3 ^ 40 * 3382101 * 2
def baseEnd_3382101 : Nat := 1157762290034651498655671

theorem tailTrace_3382101 : CollatzResearch.WordTrace tailWord_3382101 prefixEnd_3382101 1157762290034651498655671 := by
  unfold tailWord_3382101
  simp only [CollatzResearch.WordTrace]
  refine ⟨123355357520233168709482157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82236905013488779139654771 123355357520233168709482157)
  ·
    refine ⟨46258259070087438266055809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123355357520233168709482157 46258259070087438266055809)
    ·
      refine ⟨34693694302565578699541857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46258259070087438266055809 34693694302565578699541857)
      ·
        refine ⟨26020270726924184024656393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34693694302565578699541857 26020270726924184024656393)
        ·
          refine ⟨19515203045193138018492295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26020270726924184024656393 19515203045193138018492295)
          ·
            refine ⟨29272804567789707027738443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19515203045193138018492295 29272804567789707027738443)
            ·
              refine ⟨43909206851684560541607665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29272804567789707027738443 43909206851684560541607665)
              ·
                refine ⟨32931905138763420406205749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43909206851684560541607665 32931905138763420406205749)
                ·
                  refine ⟨3087366106759070663081789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32931905138763420406205749 3087366106759070663081789)
                  ·
                    refine ⟨1157762290034651498655671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087366106759070663081789 1157762290034651498655671)
                    ·
                      rfl

theorem cell22_3382101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_3382101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382101 prefixEnd_3382101 := by exact prefixLift 3382101
  have htrace : WordTrace (prefixWord ++ tailWord_3382101) baseStart_3382101 baseEnd_3382101 := by
    simpa [prefixWord, tailWord_3382101, baseEnd_3382101] using wordTrace_append hprefix tailTrace_3382101
  have hstable : (prefixWord ++ tailWord_3382101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382101).length < 2 ^ (prefixWord ++ tailWord_3382101).sum := by decide
  have hdescent : baseEnd_3382101 < baseStart_3382101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382152 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 1, 3]
def baseStart_3382152 : Nat := 118140960795 + 3382152 * 2 ^ 59
def prefixEnd_3382152 : Nat := 4983230072969 + 3 ^ 40 * 3382152 * 2
def baseEnd_3382152 : Nat := 1157779748376904365630515

theorem tailTrace_3382152 : CollatzResearch.WordTrace tailWord_3382152 prefixEnd_3382152 1157779748376904365630515 := by
  unfold tailWord_3382152
  simp only [CollatzResearch.WordTrace]
  refine ⟨61678608821524202209794355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82238145095365602946392473 61678608821524202209794355)
  ·
    refine ⟨92517913232286303314691533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61678608821524202209794355 92517913232286303314691533)
    ·
      refine ⟨34694217462107363743009325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92517913232286303314691533 34694217462107363743009325)
      ·
        refine ⟨13010331548290261403628497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34694217462107363743009325 13010331548290261403628497)
        ·
          refine ⟨9757748661217696052721373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13010331548290261403628497 9757748661217696052721373)
          ·
            refine ⟨3659155747956636019770515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9757748661217696052721373 3659155747956636019770515)
            ·
              refine ⟨5488733621934954029655773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659155747956636019770515 5488733621934954029655773)
              ·
                refine ⟨2058275108225607761120915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5488733621934954029655773 2058275108225607761120915)
                ·
                  refine ⟨3087412662338411641681373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058275108225607761120915 3087412662338411641681373)
                  ·
                    refine ⟨1157779748376904365630515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087412662338411641681373 1157779748376904365630515)
                    ·
                      rfl

theorem cell22_3382152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_3382152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382152 prefixEnd_3382152 := by exact prefixLift 3382152
  have htrace : WordTrace (prefixWord ++ tailWord_3382152) baseStart_3382152 baseEnd_3382152 := by
    simpa [prefixWord, tailWord_3382152, baseEnd_3382152] using wordTrace_append hprefix tailTrace_3382152
  have hstable : (prefixWord ++ tailWord_3382152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382152).length < 2 ^ (prefixWord ++ tailWord_3382152).sum := by decide
  have hdescent : baseEnd_3382152 < baseStart_3382152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382176 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 6]
def baseStart_3382176 : Nat := 118140960795 + 3382176 * 2 ^ 59
def prefixEnd_3382176 : Nat := 4983230072969 + 3 ^ 40 * 3382176 * 2
def baseEnd_3382176 : Nat := 385929321355792101010147

theorem tailTrace_3382176 : CollatzResearch.WordTrace tailWord_3382176 prefixEnd_3382176 385929321355792101010147 := by
  unfold tailWord_3382176
  simp only [CollatzResearch.WordTrace]
  refine ⟨61679046497480728259231191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82238728663307637678974921 61679046497480728259231191)
  ·
    refine ⟨92518569746221092388846787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61679046497480728259231191 92518569746221092388846787)
    ·
      refine ⟨138777854619331638583270181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92518569746221092388846787 138777854619331638583270181)
      ·
        refine ⟨26020847741124682234363159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138777854619331638583270181 26020847741124682234363159)
        ·
          refine ⟨39031271611687023351544739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26020847741124682234363159 39031271611687023351544739)
          ·
            refine ⟨58546907417530535027317109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39031271611687023351544739 58546907417530535027317109)
            ·
              refine ⟨5488772570393487658810979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58546907417530535027317109 5488772570393487658810979)
              ·
                refine ⟨8233158855590231488216469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488772570393487658810979 8233158855590231488216469)
                ·
                  refine ⟨385929321355792101010147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8233158855590231488216469 385929321355792101010147)
                  ·
                    rfl

theorem cell22_3382176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 6].length) (baseStart_3382176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382176 prefixEnd_3382176 := by exact prefixLift 3382176
  have htrace : WordTrace (prefixWord ++ tailWord_3382176) baseStart_3382176 baseEnd_3382176 := by
    simpa [prefixWord, tailWord_3382176, baseEnd_3382176] using wordTrace_append hprefix tailTrace_3382176
  have hstable : (prefixWord ++ tailWord_3382176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382176).length < 2 ^ (prefixWord ++ tailWord_3382176).sum := by decide
  have hdescent : baseEnd_3382176 < baseStart_3382176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382191 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 6, 3]
def baseStart_3382191 : Nat := 118140960795 + 3382191 * 2 ^ 59
def prefixEnd_3382191 : Nat := 4983230072969 + 3 ^ 40 * 3382191 * 2
def baseEnd_3382191 : Nat := 1157793098873921263905395

theorem tailTrace_3382191 : CollatzResearch.WordTrace tailWord_3382191 prefixEnd_3382191 1157793098873921263905395 := by
  unfold tailWord_3382191
  simp only [CollatzResearch.WordTrace]
  refine ⟨123358640089907114080258427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82239093393271409386838951 123358640089907114080258427)
  ·
    refine ⟨185037960134860671120387641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123358640089907114080258427 185037960134860671120387641)
    ·
      refine ⟨138778470101145503340290731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185037960134860671120387641 138778470101145503340290731)
      ·
        refine ⟨208167705151718255010436097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138778470101145503340290731 208167705151718255010436097)
        ·
          refine ⟨156125778863788691257827073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208167705151718255010436097 156125778863788691257827073)
          ·
            refine ⟨117094334147841518443370305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156125778863788691257827073 117094334147841518443370305)
            ·
              refine ⟨87820750610881138832527729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117094334147841518443370305 87820750610881138832527729)
              ·
                refine ⟨65865562958160854124395797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87820750610881138832527729 65865562958160854124395797)
                ·
                  refine ⟨3087448263663790037081053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65865562958160854124395797 3087448263663790037081053)
                  ·
                    refine ⟨1157793098873921263905395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087448263663790037081053 1157793098873921263905395)
                    ·
                      rfl

theorem cell22_3382191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_3382191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382191 prefixEnd_3382191 := by exact prefixLift 3382191
  have htrace : WordTrace (prefixWord ++ tailWord_3382191) baseStart_3382191 baseEnd_3382191 := by
    simpa [prefixWord, tailWord_3382191, baseEnd_3382191] using wordTrace_append hprefix tailTrace_3382191
  have hstable : (prefixWord ++ tailWord_3382191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382191).length < 2 ^ (prefixWord ++ tailWord_3382191).sum := by decide
  have hdescent : baseEnd_3382191 < baseStart_3382191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382242 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3382242 : Nat := 118140960795 + 3382242 * 2 ^ 59
def prefixEnd_3382242 : Nat := 4983230072969 + 3 ^ 40 * 3382242 * 2
def baseEnd_3382242 : Nat := 1157810557216174130880239

theorem tailTrace_3382242 : CollatzResearch.WordTrace tailWord_3382242 prefixEnd_3382242 1157810557216174130880239 := by
  unfold tailWord_3382242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840125053180587447591245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82240333475148233193576653 30840125053180587447591245)
  ·
    refine ⟨11565046894942720292846717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30840125053180587447591245 11565046894942720292846717)
    ·
      refine ⟨4336892585603520109817519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11565046894942720292846717 4336892585603520109817519)
      ·
        refine ⟨6505338878405280164726279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336892585603520109817519 6505338878405280164726279)
        ·
          refine ⟨9758008317607920247089419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505338878405280164726279 9758008317607920247089419)
          ·
            refine ⟨14637012476411880370634129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758008317607920247089419 14637012476411880370634129)
            ·
              refine ⟨10977759357308910277975597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14637012476411880370634129 10977759357308910277975597)
              ·
                refine ⟨4116659758990841354240849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977759357308910277975597 4116659758990841354240849)
                ·
                  refine ⟨3087494819243131015680637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4116659758990841354240849 3087494819243131015680637)
                  ·
                    refine ⟨1157810557216174130880239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087494819243131015680637 1157810557216174130880239)
                    ·
                      rfl

theorem cell22_3382242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3382242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382242 prefixEnd_3382242 := by exact prefixLift 3382242
  have htrace : WordTrace (prefixWord ++ tailWord_3382242) baseStart_3382242 baseEnd_3382242 := by
    simpa [prefixWord, tailWord_3382242, baseEnd_3382242] using wordTrace_append hprefix tailTrace_3382242
  have hstable : (prefixWord ++ tailWord_3382242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382242).length < 2 ^ (prefixWord ++ tailWord_3382242).sum := by decide
  have hdescent : baseEnd_3382242 < baseStart_3382242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382283 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 5]
def baseStart_3382283 : Nat := 118140960795 + 3382283 * 2 ^ 59
def prefixEnd_3382283 : Nat := 4983230072969 + 3 ^ 40 * 3382283 * 2
def baseEnd_3382283 : Nat := 385941530784687896868371

theorem tailTrace_3382283 : CollatzResearch.WordTrace tailWord_3382283 prefixEnd_3382283 385941530784687896868371 := by
  unfold tailWord_3382283
  simp only [CollatzResearch.WordTrace]
  refine ⟨123361995605573813792607503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82241330403715875861738335 123361995605573813792607503)
  ·
    refine ⟨185042993408360720688911255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123361995605573813792607503 185042993408360720688911255)
    ·
      refine ⟨277564490112541081033366883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185042993408360720688911255 277564490112541081033366883)
      ·
        refine ⟨416346735168811621550050325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277564490112541081033366883 416346735168811621550050325)
        ·
          refine ⟨19516253211038044760158609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 416346735168811621550050325 19516253211038044760158609)
          ·
            refine ⟨14637189908278533570118957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19516253211038044760158609 14637189908278533570118957)
            ·
              refine ⟨5488946215604450088794609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14637189908278533570118957 5488946215604450088794609)
              ·
                refine ⟨4116709661703337566595957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488946215604450088794609 4116709661703337566595957)
                ·
                  refine ⟨385941530784687896868371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4116709661703337566595957 385941530784687896868371)
                  ·
                    rfl

theorem cell22_3382283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 5].length) (baseStart_3382283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382283 prefixEnd_3382283 := by exact prefixLift 3382283
  have htrace : WordTrace (prefixWord ++ tailWord_3382283) baseStart_3382283 baseEnd_3382283 := by
    simpa [prefixWord, tailWord_3382283, baseEnd_3382283] using wordTrace_append hprefix tailTrace_3382283
  have hstable : (prefixWord ++ tailWord_3382283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382283).length < 2 ^ (prefixWord ++ tailWord_3382283).sum := by decide
  have hdescent : baseEnd_3382283 < baseStart_3382283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382360 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 2, 3]
def baseStart_3382360 : Nat := 118140960795 + 3382360 * 2 ^ 59
def prefixEnd_3382360 : Nat := 4983230072969 + 3 ^ 40 * 3382360 * 2
def baseEnd_3382360 : Nat := 1157850951027661156429877

theorem tailTrace_3382360 : CollatzResearch.WordTrace tailWord_3382360 prefixEnd_3382360 1157850951027661156429877 := by
  unfold tailWord_3382360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61682402013147427971580267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82243202684196570628773689 61682402013147427971580267)
  ·
    refine ⟨92523603019721141957370401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61682402013147427971580267 92523603019721141957370401)
    ·
      refine ⟨69392702264790856468027801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92523603019721141957370401 69392702264790856468027801)
      ·
        refine ⟨52044526698593142351020851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69392702264790856468027801 52044526698593142351020851)
        ·
          refine ⟨78066790047889713526531277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52044526698593142351020851 78066790047889713526531277)
          ·
            refine ⟨29275046267958642572449229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78066790047889713526531277 29275046267958642572449229)
            ·
              refine ⟨10978142350484490964668461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29275046267958642572449229 10978142350484490964668461)
              ·
                refine ⟨4116803381431684111750673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10978142350484490964668461 4116803381431684111750673)
                ·
                  refine ⟨3087602536073763083813005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4116803381431684111750673 3087602536073763083813005)
                  ·
                    refine ⟨1157850951027661156429877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087602536073763083813005 1157850951027661156429877)
                    ·
                      rfl

theorem cell22_3382360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 3].length) (baseStart_3382360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382360 prefixEnd_3382360 := by exact prefixLift 3382360
  have htrace : WordTrace (prefixWord ++ tailWord_3382360) baseStart_3382360 baseEnd_3382360 := by
    simpa [prefixWord, tailWord_3382360, baseEnd_3382360] using wordTrace_append hprefix tailTrace_3382360
  have hstable : (prefixWord ++ tailWord_3382360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382360).length < 2 ^ (prefixWord ++ tailWord_3382360).sum := by decide
  have hdescent : baseEnd_3382360 < baseStart_3382360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382375 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3382375 : Nat := 118140960795 + 3382375 * 2 ^ 59
def prefixEnd_3382375 : Nat := 4983230072969 + 3 ^ 40 * 3382375 * 2
def baseEnd_3382375 : Nat := 1157856085834206117304831

theorem tailTrace_3382375 : CollatzResearch.WordTrace tailWord_3382375 prefixEnd_3382375 1157856085834206117304831 := by
  unfold tailWord_3382375
  simp only [CollatzResearch.WordTrace]
  refine ⟨123365351121240513504956579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82243567414160342336637719 123365351121240513504956579)
  ·
    refine ⟨185048026681860770257434869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123365351121240513504956579 185048026681860770257434869)
    ·
      refine ⟨17348252501424447211634519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185048026681860770257434869 17348252501424447211634519)
      ·
        refine ⟨26022378752136670817451779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348252501424447211634519 26022378752136670817451779)
        ·
          refine ⟨39033568128205006226177669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26022378752136670817451779 39033568128205006226177669)
          ·
            refine ⟨7318794024038438667408313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39033568128205006226177669 7318794024038438667408313)
            ·
              refine ⟨5489095518028829000556235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7318794024038438667408313 5489095518028829000556235)
              ·
                refine ⟨8233643277043243500834353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489095518028829000556235 8233643277043243500834353)
                ·
                  refine ⟨6175232457782432625625765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233643277043243500834353 6175232457782432625625765)
                  ·
                    refine ⟨1157856085834206117304831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175232457782432625625765 1157856085834206117304831)
                    ·
                      rfl

theorem cell22_3382375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3382375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382375 prefixEnd_3382375 := by exact prefixLift 3382375
  have htrace : WordTrace (prefixWord ++ tailWord_3382375) baseStart_3382375 baseEnd_3382375 := by
    simpa [prefixWord, tailWord_3382375, baseEnd_3382375] using wordTrace_append hprefix tailTrace_3382375
  have hstable : (prefixWord ++ tailWord_3382375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382375).length < 2 ^ (prefixWord ++ tailWord_3382375).sum := by decide
  have hdescent : baseEnd_3382375 < baseStart_3382375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382433 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3382433 : Nat := 118140960795 + 3382433 * 2 ^ 59
def prefixEnd_3382433 : Nat := 4983230072969 + 3 ^ 40 * 3382433 * 2
def baseEnd_3382433 : Nat := 1157875940419513299354653

theorem tailTrace_3382433 : CollatzResearch.WordTrace tailWord_3382433 prefixEnd_3382433 1157875940419513299354653 := by
  unfold tailWord_3382433
  simp only [CollatzResearch.WordTrace]
  refine ⟨123367466555030389410567953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82244977703353592940378635 123367466555030389410567953)
  ·
    refine ⟨92525599916272792057925965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123367466555030389410567953 92525599916272792057925965)
    ·
      refine ⟨34697099968602297021722237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92525599916272792057925965 34697099968602297021722237)
      ·
        refine ⟨13011412488225861383145839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34697099968602297021722237 13011412488225861383145839)
        ·
          refine ⟨19517118732338792074718759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13011412488225861383145839 19517118732338792074718759)
          ·
            refine ⟨29275678098508188112078139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19517118732338792074718759 29275678098508188112078139)
            ·
              refine ⟨43913517147762282168117209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29275678098508188112078139 43913517147762282168117209)
              ·
                refine ⟨32935137860821711626087907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43913517147762282168117209 32935137860821711626087907)
                ·
                  refine ⟨49402706791232567439131861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32935137860821711626087907 49402706791232567439131861)
                  ·
                    refine ⟨1157875940419513299354653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49402706791232567439131861 1157875940419513299354653)
                    ·
                      rfl

theorem cell22_3382433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3382433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382433 prefixEnd_3382433 := by exact prefixLift 3382433
  have htrace : WordTrace (prefixWord ++ tailWord_3382433) baseStart_3382433 baseEnd_3382433 := by
    simpa [prefixWord, tailWord_3382433, baseEnd_3382433] using wordTrace_append hprefix tailTrace_3382433
  have hstable : (prefixWord ++ tailWord_3382433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382433).length < 2 ^ (prefixWord ++ tailWord_3382433).sum := by decide
  have hdescent : baseEnd_3382433 < baseStart_3382433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382439 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3382439 : Nat := 118140960795 + 3382439 * 2 ^ 59
def prefixEnd_3382439 : Nat := 4983230072969 + 3 ^ 40 * 3382439 * 2
def baseEnd_3382439 : Nat := 1157877994342131283704635

theorem tailTrace_3382439 : CollatzResearch.WordTrace tailWord_3382439 prefixEnd_3382439 1157877994342131283704635 := by
  unfold tailWord_3382439
  simp only [CollatzResearch.WordTrace]
  refine ⟨123367685393008652435286371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82245123595339101623524247 123367685393008652435286371)
  ·
    refine ⟨185051528089512978652929557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123367685393008652435286371 185051528089512978652929557)
    ·
      refine ⟨8674290379195920874356073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185051528089512978652929557 8674290379195920874356073)
      ·
        refine ⟨6505717784396940655767055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8674290379195920874356073 6505717784396940655767055)
        ·
          refine ⟨9758576676595410983650583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6505717784396940655767055 9758576676595410983650583)
          ·
            refine ⟨14637865014893116475475875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9758576676595410983650583 14637865014893116475475875)
            ·
              refine ⟨21956797522339674713213813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14637865014893116475475875 21956797522339674713213813)
              ·
                refine ⟨2058449767719344504363795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21956797522339674713213813 2058449767719344504363795)
                ·
                  refine ⟨3087674651579016756545693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058449767719344504363795 3087674651579016756545693)
                  ·
                    refine ⟨1157877994342131283704635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087674651579016756545693 1157877994342131283704635)
                    ·
                      rfl

theorem cell22_3382439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3382439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382439 prefixEnd_3382439 := by exact prefixLift 3382439
  have htrace : WordTrace (prefixWord ++ tailWord_3382439) baseStart_3382439 baseEnd_3382439 := by
    simpa [prefixWord, tailWord_3382439, baseEnd_3382439] using wordTrace_append hprefix tailTrace_3382439
  have hstable : (prefixWord ++ tailWord_3382439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382439).length < 2 ^ (prefixWord ++ tailWord_3382439).sum := by decide
  have hdescent : baseEnd_3382439 < baseStart_3382439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382463 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 6]
def baseStart_3382463 : Nat := 118140960795 + 3382463 * 2 ^ 59
def prefixEnd_3382463 : Nat := 4983230072969 + 3 ^ 40 * 3382463 * 2
def baseEnd_3382463 : Nat := 385962070010867740368187

theorem tailTrace_3382463 : CollatzResearch.WordTrace tailWord_3382463 prefixEnd_3382463 385962070010867740368187 := by
  unfold tailWord_3382463
  simp only [CollatzResearch.WordTrace]
  refine ⟨123368560744921704534160043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82245707163281136356106695 123368560744921704534160043)
  ·
    refine ⟨185052841117382556801240065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123368560744921704534160043 185052841117382556801240065)
    ·
      refine ⟨138789630838036917600930049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185052841117382556801240065 138789630838036917600930049)
      ·
        refine ⟨104092223128527688200697537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138789630838036917600930049 104092223128527688200697537)
        ·
          refine ⟨78069167346395766150523153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104092223128527688200697537 78069167346395766150523153)
          ·
            refine ⟨58551875509796824612892365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78069167346395766150523153 58551875509796824612892365)
            ·
              refine ⟨21956953316173809229834637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58551875509796824612892365 21956953316173809229834637)
              ·
                refine ⟨8233857493565178461187989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21956953316173809229834637 8233857493565178461187989)
                ·
                  refine ⟨385962070010867740368187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8233857493565178461187989 385962070010867740368187)
                  ·
                    rfl

theorem cell22_3382463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 6].length) (baseStart_3382463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382463 prefixEnd_3382463 := by exact prefixLift 3382463
  have htrace : WordTrace (prefixWord ++ tailWord_3382463) baseStart_3382463 baseEnd_3382463 := by
    simpa [prefixWord, tailWord_3382463, baseEnd_3382463] using wordTrace_append hprefix tailTrace_3382463
  have hstable : (prefixWord ++ tailWord_3382463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382463).length < 2 ^ (prefixWord ++ tailWord_3382463).sum := by decide
  have hdescent : baseEnd_3382463 < baseStart_3382463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382482 : List Nat := [3, 2, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_3382482 : Nat := 118140960795 + 3382482 * 2 ^ 59
def prefixEnd_3382482 : Nat := 4983230072969 + 3 ^ 40 * 3382482 * 2
def baseEnd_3382482 : Nat := 1157892714120893504879503

theorem tailTrace_3382482 : CollatzResearch.WordTrace tailWord_3382482 prefixEnd_3382482 1157892714120893504879503 := by
  unfold tailWord_3382482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842313432963217694775425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82246169154568580519401133 30842313432963217694775425)
  ·
    refine ⟨23131735074722413271081569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30842313432963217694775425 23131735074722413271081569)
    ·
      refine ⟨17348801306041809953311177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23131735074722413271081569 17348801306041809953311177)
      ·
        refine ⟨13011600979531357464983383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17348801306041809953311177 13011600979531357464983383)
        ·
          refine ⟨19517401469297036197475075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13011600979531357464983383 19517401469297036197475075)
          ·
            refine ⟨29276102203945554296212613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19517401469297036197475075 29276102203945554296212613)
            ·
              refine ⟨5489269163239791430539865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29276102203945554296212613 5489269163239791430539865)
              ·
                refine ⟨4116951872429843572904899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5489269163239791430539865 4116951872429843572904899)
                ·
                  refine ⟨6175427808644765359357349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116951872429843572904899 6175427808644765359357349)
                  ·
                    refine ⟨1157892714120893504879503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175427808644765359357349 1157892714120893504879503)
                    ·
                      rfl

theorem cell22_3382482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_3382482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382482 prefixEnd_3382482 := by exact prefixLift 3382482
  have htrace : WordTrace (prefixWord ++ tailWord_3382482) baseStart_3382482 baseEnd_3382482 := by
    simpa [prefixWord, tailWord_3382482, baseEnd_3382482] using wordTrace_append hprefix tailTrace_3382482
  have hstable : (prefixWord ++ tailWord_3382482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382482).length < 2 ^ (prefixWord ++ tailWord_3382482).sum := by decide
  have hdescent : baseEnd_3382482 < baseStart_3382482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382495 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 4, 3]
def baseStart_3382495 : Nat := 118140960795 + 3382495 * 2 ^ 59
def prefixEnd_3382495 : Nat := 4983230072969 + 3 ^ 40 * 3382495 * 2
def baseEnd_3382495 : Nat := 1157897164286565804304463

theorem tailTrace_3382495 : CollatzResearch.WordTrace tailWord_3382495 prefixEnd_3382495 1157897164286565804304463 := by
  unfold tailWord_3382495
  simp only [CollatzResearch.WordTrace]
  refine ⟨123369727880805773999324939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82246485253870515999549959 123369727880805773999324939)
  ·
    refine ⟨185054591821208660998987409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123369727880805773999324939 185054591821208660998987409)
    ·
      refine ⟨138790943865906495749240557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185054591821208660998987409 138790943865906495749240557)
      ·
        refine ⟨52046603949714935905965209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138790943865906495749240557 52046603949714935905965209)
        ·
          refine ⟨39034952962286201929473907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52046603949714935905965209 39034952962286201929473907)
          ·
            refine ⟨58552429443429302894210861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39034952962286201929473907 58552429443429302894210861)
            ·
              refine ⟨21957161041285988585329073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58552429443429302894210861 21957161041285988585329073)
              ·
                refine ⟨16467870780964491438996805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21957161041285988585329073 16467870780964491438996805)
                ·
                  refine ⟨3087725771430842144811901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16467870780964491438996805 3087725771430842144811901)
                  ·
                    refine ⟨1157897164286565804304463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087725771430842144811901 1157897164286565804304463)
                    ·
                      rfl

theorem cell22_3382495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_3382495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382495 prefixEnd_3382495 := by exact prefixLift 3382495
  have htrace : WordTrace (prefixWord ++ tailWord_3382495) baseStart_3382495 baseEnd_3382495 := by
    simpa [prefixWord, tailWord_3382495, baseEnd_3382495] using wordTrace_append hprefix tailTrace_3382495
  have hstable : (prefixWord ++ tailWord_3382495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382495).length < 2 ^ (prefixWord ++ tailWord_3382495).sum := by decide
  have hdescent : baseEnd_3382495 < baseStart_3382495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382497 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 4]
def baseStart_3382497 : Nat := 118140960795 + 3382497 * 2 ^ 59
def prefixEnd_3382497 : Nat := 4983230072969 + 3 ^ 40 * 3382497 * 2
def baseEnd_3382497 : Nat := 385965949642479488584819

theorem tailTrace_3382497 : CollatzResearch.WordTrace tailWord_3382497 prefixEnd_3382497 385965949642479488584819 := by
  unfold tailWord_3382497
  simp only [CollatzResearch.WordTrace]
  refine ⟨123369800826798528340897745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82246533884532352227265163 123369800826798528340897745)
  ·
    refine ⟨92527350620098896255673309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123369800826798528340897745 92527350620098896255673309)
    ·
      refine ⟨34697756482537086095877491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92527350620098896255673309 34697756482537086095877491)
      ·
        refine ⟨52046634723805629143816237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34697756482537086095877491 52046634723805629143816237)
        ·
          refine ⟨19517488021427110928931089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52046634723805629143816237 19517488021427110928931089)
          ·
            refine ⟨14638116016070333196698317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19517488021427110928931089 14638116016070333196698317)
            ·
              refine ⟨5489293506026374948761869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14638116016070333196698317 5489293506026374948761869)
              ·
                refine ⟨2058485064759890605785701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5489293506026374948761869 2058485064759890605785701)
                ·
                  refine ⟨385965949642479488584819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2058485064759890605785701 385965949642479488584819)
                  ·
                    rfl

theorem cell22_3382497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_3382497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382497 prefixEnd_3382497 := by exact prefixLift 3382497
  have htrace : WordTrace (prefixWord ++ tailWord_3382497) baseStart_3382497 baseEnd_3382497 := by
    simpa [prefixWord, tailWord_3382497, baseEnd_3382497] using wordTrace_append hprefix tailTrace_3382497
  have hstable : (prefixWord ++ tailWord_3382497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382497).length < 2 ^ (prefixWord ++ tailWord_3382497).sum := by decide
  have hdescent : baseEnd_3382497 < baseStart_3382497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382508 : List Nat := [2, 2, 1, 1, 2, 4, 10]
def baseStart_3382508 : Nat := 118140960795 + 3382508 * 2 ^ 59
def prefixEnd_3382508 : Nat := 4983230072969 + 3 ^ 40 * 3382508 * 2
def baseEnd_3382508 : Nat := 42885244979712522360349

theorem tailTrace_3382508 : CollatzResearch.WordTrace tailWord_3382508 prefixEnd_3382508 42885244979712522360349 := by
  unfold tailWord_3382508
  simp only [CollatzResearch.WordTrace]
  refine ⟨61685101014879338609774089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82246801353172451479698785 61685101014879338609774089)
  ·
    refine ⟨46263825761159503957330567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61685101014879338609774089 46263825761159503957330567)
    ·
      refine ⟨69395738641739255935995851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46263825761159503957330567 69395738641739255935995851)
      ·
        refine ⟨104093607962608883903993777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69395738641739255935995851 104093607962608883903993777)
        ·
          refine ⟨78070205971956662927995333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104093607962608883903993777 78070205971956662927995333)
          ·
            refine ⟨14638163619741874298999125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78070205971956662927995333 14638163619741874298999125)
            ·
              refine ⟨42885244979712522360349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14638163619741874298999125 42885244979712522360349)
              ·
                rfl

theorem cell22_3382508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 10].length) (baseStart_3382508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382508 prefixEnd_3382508 := by exact prefixLift 3382508
  have htrace : WordTrace (prefixWord ++ tailWord_3382508) baseStart_3382508 baseEnd_3382508 := by
    simpa [prefixWord, tailWord_3382508, baseEnd_3382508] using wordTrace_append hprefix tailTrace_3382508
  have hstable : (prefixWord ++ tailWord_3382508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382508).length < 2 ^ (prefixWord ++ tailWord_3382508).sum := by decide
  have hdescent : baseEnd_3382508 < baseStart_3382508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382510 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3382510 : Nat := 118140960795 + 3382510 * 2 ^ 59
def prefixEnd_3382510 : Nat := 4983230072969 + 3 ^ 40 * 3382510 * 2
def baseEnd_3382510 : Nat := 1157902299093110765179417

theorem tailTrace_3382510 : CollatzResearch.WordTrace tailWord_3382510 prefixEnd_3382510 1157902299093110765179417 := by
  unfold tailWord_3382510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15421284371968928945140123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82246849983834287707413989 15421284371968928945140123)
  ·
    refine ⟨23131926557953393417710185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15421284371968928945140123 23131926557953393417710185)
    ·
      refine ⟨17348944918465045063282639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23131926557953393417710185 17348944918465045063282639)
      ·
        refine ⟨26023417377697567594923959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17348944918465045063282639 26023417377697567594923959)
        ·
          refine ⟨39035126066546351392385939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26023417377697567594923959 39035126066546351392385939)
          ·
            refine ⟨58552689099819527088578909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39035126066546351392385939 58552689099819527088578909)
            ·
              refine ⟨21957258412432322658217091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58552689099819527088578909 21957258412432322658217091)
              ·
                refine ⟨32935887618648483987325637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21957258412432322658217091 32935887618648483987325637)
                ·
                  refine ⟨6175478928496590747623557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32935887618648483987325637 6175478928496590747623557)
                  ·
                    refine ⟨1157902299093110765179417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175478928496590747623557 1157902299093110765179417)
                    ·
                      rfl

theorem cell22_3382510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3382510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382510 prefixEnd_3382510 := by exact prefixLift 3382510
  have htrace : WordTrace (prefixWord ++ tailWord_3382510) baseStart_3382510 baseEnd_3382510 := by
    simpa [prefixWord, tailWord_3382510, baseEnd_3382510] using wordTrace_append hprefix tailTrace_3382510
  have hstable : (prefixWord ++ tailWord_3382510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382510).length < 2 ^ (prefixWord ++ tailWord_3382510).sum := by decide
  have hdescent : baseEnd_3382510 < baseStart_3382510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382514 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_3382514 : Nat := 118140960795 + 3382514 * 2 ^ 59
def prefixEnd_3382514 : Nat := 4983230072969 + 3 ^ 40 * 3382514 * 2
def baseEnd_3382514 : Nat := 385967889458285362693135

theorem tailTrace_3382514 : CollatzResearch.WordTrace tailWord_3382514 prefixEnd_3382514 385967889458285362693135 := by
  unfold tailWord_3382514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842605216934235061066649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82246947245157960162844397 30842605216934235061066649)
  ·
    refine ⟨23131953912700676295799987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30842605216934235061066649 23131953912700676295799987)
    ·
      refine ⟨34697930869051014443699981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23131953912700676295799987 34697930869051014443699981)
      ·
        refine ⟨13011724075894130416387493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34697930869051014443699981 13011724075894130416387493)
        ·
          refine ⟨2439698264230149453072655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13011724075894130416387493 2439698264230149453072655)
          ·
            refine ⟨3659547396345224179608983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439698264230149453072655 3659547396345224179608983)
            ·
              refine ⟨5489321094517836269413475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659547396345224179608983 5489321094517836269413475)
              ·
                refine ⟨8233981641776754404120213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489321094517836269413475 8233981641776754404120213)
                ·
                  refine ⟨385967889458285362693135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8233981641776754404120213 385967889458285362693135)
                  ·
                    rfl

theorem cell22_3382514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_3382514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382514 prefixEnd_3382514 := by exact prefixLift 3382514
  have htrace : WordTrace (prefixWord ++ tailWord_3382514) baseStart_3382514 baseEnd_3382514 := by
    simpa [prefixWord, tailWord_3382514, baseEnd_3382514] using wordTrace_append hprefix tailTrace_3382514
  have hstable : (prefixWord ++ tailWord_3382514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382514).length < 2 ^ (prefixWord ++ tailWord_3382514).sum := by decide
  have hdescent : baseEnd_3382514 < baseStart_3382514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382529 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 2, 3]
def baseStart_3382529 : Nat := 118140960795 + 3382529 * 2 ^ 59
def prefixEnd_3382529 : Nat := 4983230072969 + 3 ^ 40 * 3382529 * 2
def baseEnd_3382529 : Nat := 1157908803181401048954359

theorem tailTrace_3382529 : CollatzResearch.WordTrace tailWord_3382529 prefixEnd_3382529 1157908803181401048954359 := by
  unfold tailWord_3382529
  simp only [CollatzResearch.WordTrace]
  refine ⟨123370967962682597806062641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82247311975121731870708427 123370967962682597806062641)
  ·
    refine ⟨92528225972011948354546981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123370967962682597806062641 92528225972011948354546981)
    ·
      refine ⟨17349042369752240316477559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92528225972011948354546981 17349042369752240316477559)
      ·
        refine ⟨26023563554628360474716339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17349042369752240316477559 26023563554628360474716339)
        ·
          refine ⟨39035345331942540712074509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26023563554628360474716339 39035345331942540712074509)
          ·
            refine ⟨14638254499478452767027941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39035345331942540712074509 14638254499478452767027941)
            ·
              refine ⟨2744672718652209893817739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14638254499478452767027941 2744672718652209893817739)
              ·
                refine ⟨4117009077978314840726609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744672718652209893817739 4117009077978314840726609)
                ·
                  refine ⟨3087756808483736130544957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117009077978314840726609 3087756808483736130544957)
                  ·
                    refine ⟨1157908803181401048954359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087756808483736130544957 1157908803181401048954359)
                    ·
                      rfl

theorem cell22_3382529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_3382529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382529 prefixEnd_3382529 := by exact prefixLift 3382529
  have htrace : WordTrace (prefixWord ++ tailWord_3382529) baseStart_3382529 baseEnd_3382529 := by
    simpa [prefixWord, tailWord_3382529, baseEnd_3382529] using wordTrace_append hprefix tailTrace_3382529
  have hstable : (prefixWord ++ tailWord_3382529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382529).length < 2 ^ (prefixWord ++ tailWord_3382529).sum := by decide
  have hdescent : baseEnd_3382529 < baseStart_3382529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382621 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 7]
def baseStart_3382621 : Nat := 118140960795 + 3382621 * 2 ^ 59
def prefixEnd_3382621 : Nat := 4983230072969 + 3 ^ 40 * 3382621 * 2
def baseEnd_3382621 : Nat := 385980098887181158551359

theorem tailTrace_3382621 : CollatzResearch.WordTrace tailWord_3382621 prefixEnd_3382621 385980098887181158551359 := by
  unfold tailWord_3382621
  simp only [CollatzResearch.WordTrace]
  refine ⟨123374323478349297518411717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82249548985566198345607811 123374323478349297518411717)
  ·
    refine ⟨23132685652190493284702197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123374323478349297518411717 23132685652190493284702197)
    ·
      refine ⟨2168689279892858745440831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23132685652190493284702197 2168689279892858745440831)
      ·
        refine ⟨3253033919839288118161247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168689279892858745440831 3253033919839288118161247)
        ·
          refine ⟨4879550879758932177241871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253033919839288118161247 4879550879758932177241871)
          ·
            refine ⟨7319326319638398265862807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879550879758932177241871 7319326319638398265862807)
            ·
              refine ⟨10978989479457597398794211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7319326319638398265862807 10978989479457597398794211)
              ·
                refine ⟨16468484219186396098191317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10978989479457597398794211 16468484219186396098191317)
                ·
                  refine ⟨385980098887181158551359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16468484219186396098191317 385980098887181158551359)
                  ·
                    rfl

theorem cell22_3382621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 7].length) (baseStart_3382621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382621 prefixEnd_3382621 := by exact prefixLift 3382621
  have htrace : WordTrace (prefixWord ++ tailWord_3382621) baseStart_3382621 baseEnd_3382621 := by
    simpa [prefixWord, tailWord_3382621, baseEnd_3382621] using wordTrace_append hprefix tailTrace_3382621
  have hstable : (prefixWord ++ tailWord_3382621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382621).length < 2 ^ (prefixWord ++ tailWord_3382621).sum := by decide
  have hdescent : baseEnd_3382621 < baseStart_3382621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382812 : List Nat := [2, 2, 3, 1, 2, 1, 2, 9]
def baseStart_3382812 : Nat := 118140960795 + 3382812 * 2 ^ 59
def prefixEnd_3382812 : Nat := 4983230072969 + 3 ^ 40 * 3382812 * 2
def baseEnd_3382812 : Nat := 128667297762764738236499

theorem tailTrace_3382812 : CollatzResearch.WordTrace tailWord_3382812 prefixEnd_3382812 128667297762764738236499 := by
  unfold tailWord_3382812
  simp only [CollatzResearch.WordTrace]
  refine ⟨61690644910328668569307345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82254193213771558092409793 61690644910328668569307345)
  ·
    refine ⟨46267983682746501426980509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61690644910328668569307345 46267983682746501426980509)
    ·
      refine ⟨17350493881029938035117691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46267983682746501426980509 17350493881029938035117691)
      ·
        refine ⟨26025740821544907052676537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17350493881029938035117691 26025740821544907052676537)
        ·
          refine ⟨19519305616158680289507403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26025740821544907052676537 19519305616158680289507403)
          ·
            refine ⟨29278958424238020434261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19519305616158680289507403 29278958424238020434261105)
            ·
              refine ⟨21959218818178515325695829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29278958424238020434261105 21959218818178515325695829)
              ·
                refine ⟨128667297762764738236499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21959218818178515325695829 128667297762764738236499)
                ·
                  rfl

theorem cell22_3382812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 9].length) (baseStart_3382812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382812 prefixEnd_3382812 := by exact prefixLift 3382812
  have htrace : WordTrace (prefixWord ++ tailWord_3382812) baseStart_3382812 baseEnd_3382812 := by
    simpa [prefixWord, tailWord_3382812, baseEnd_3382812] using wordTrace_append hprefix tailTrace_3382812
  have hstable : (prefixWord ++ tailWord_3382812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382812).length < 2 ^ (prefixWord ++ tailWord_3382812).sum := by decide
  have hdescent : baseEnd_3382812 < baseStart_3382812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382816 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 1, 5]
def baseStart_3382816 : Nat := 118140960795 + 3382816 * 2 ^ 59
def prefixEnd_3382816 : Nat := 4983230072969 + 3 ^ 40 * 3382816 * 2
def baseEnd_3382816 : Nat := 1158007049146627967028479

theorem tailTrace_3382816 : CollatzResearch.WordTrace tailWord_3382816 prefixEnd_3382816 1158007049146627967028479 := by
  unfold tailWord_3382816
  simp only [CollatzResearch.WordTrace]
  refine ⟨61690717856321422910880151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82254290475095230547840201 61690717856321422910880151)
  ·
    refine ⟨92536076784482134366320227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61690717856321422910880151 92536076784482134366320227)
    ·
      refine ⟨138804115176723201549480341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92536076784482134366320227 138804115176723201549480341)
      ·
        refine ⟨6506442898908900072631891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138804115176723201549480341 6506442898908900072631891)
        ·
          refine ⟨9759664348363350108947837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506442898908900072631891 9759664348363350108947837)
          ·
            refine ⟨3659874130636256290855439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9759664348363350108947837 3659874130636256290855439)
            ·
              refine ⟨5489811195954384436283159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659874130636256290855439 5489811195954384436283159)
              ·
                refine ⟨8234716793931576654424739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489811195954384436283159 8234716793931576654424739)
                ·
                  refine ⟨12352075190897364981637109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8234716793931576654424739 12352075190897364981637109)
                  ·
                    refine ⟨1158007049146627967028479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12352075190897364981637109 1158007049146627967028479)
                    ·
                      rfl

theorem cell22_3382816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 5].length) (baseStart_3382816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382816 prefixEnd_3382816 := by exact prefixLift 3382816
  have htrace : WordTrace (prefixWord ++ tailWord_3382816) baseStart_3382816 baseEnd_3382816 := by
    simpa [prefixWord, tailWord_3382816, baseEnd_3382816] using wordTrace_append hprefix tailTrace_3382816
  have hstable : (prefixWord ++ tailWord_3382816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382816).length < 2 ^ (prefixWord ++ tailWord_3382816).sum := by decide
  have hdescent : baseEnd_3382816 < baseStart_3382816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382872 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 7]
def baseStart_3382872 : Nat := 118140960795 + 3382872 * 2 ^ 59
def prefixEnd_3382872 : Nat := 4983230072969 + 3 ^ 40 * 3382872 * 2
def baseEnd_3382872 : Nat := 1158026219091062487628307

theorem tailTrace_3382872 : CollatzResearch.WordTrace tailWord_3382872 prefixEnd_3382872 1158026219091062487628307 := by
  unfold tailWord_3382872
  simp only [CollatzResearch.WordTrace]
  refine ⟨61691739100219983692899435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82255652133626644923865913 61691739100219983692899435)
  ·
    refine ⟨92537608650329975539349153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61691739100219983692899435 92537608650329975539349153)
    ·
      refine ⟨69403206487747481654511865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92537608650329975539349153 69403206487747481654511865)
      ·
        refine ⟨52052404865810611240883899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69403206487747481654511865 52052404865810611240883899)
        ·
          refine ⟨78078607298715916861325849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52052404865810611240883899 78078607298715916861325849)
          ·
            refine ⟨58558955474036937645994387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78078607298715916861325849 58558955474036937645994387)
            ·
              refine ⟨87838433211055406468991581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58558955474036937645994387 87838433211055406468991581)
              ·
                refine ⟨32939412454145777425871843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87838433211055406468991581 32939412454145777425871843)
                ·
                  refine ⟨49409118681218666138807765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32939412454145777425871843 49409118681218666138807765)
                  ·
                    refine ⟨1158026219091062487628307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49409118681218666138807765 1158026219091062487628307)
                    ·
                      rfl

theorem cell22_3382872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_3382872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3382872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3382872 prefixEnd_3382872 := by exact prefixLift 3382872
  have htrace : WordTrace (prefixWord ++ tailWord_3382872) baseStart_3382872 baseEnd_3382872 := by
    simpa [prefixWord, tailWord_3382872, baseEnd_3382872] using wordTrace_append hprefix tailTrace_3382872
  have hstable : (prefixWord ++ tailWord_3382872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382872).length < 2 ^ (prefixWord ++ tailWord_3382872).sum := by decide
  have hdescent : baseEnd_3382872 < baseStart_3382872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383024 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 2, 5]
def baseStart_3383024 : Nat := 118140960795 + 3383024 * 2 ^ 59
def prefixEnd_3383024 : Nat := 4983230072969 + 3 ^ 40 * 3383024 * 2
def baseEnd_3383024 : Nat := 1158078251797384757827841

theorem tailTrace_3383024 : CollatzResearch.WordTrace tailWord_3383024 prefixEnd_3383024 1158078251797384757827841 := by
  unfold tailWord_3383024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61694511047944648672666063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82259348063926198230221417 61694511047944648672666063)
  ·
    refine ⟨92541766571916973008999095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61694511047944648672666063 92541766571916973008999095)
    ·
      refine ⟨138812649857875459513498643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92541766571916973008999095 138812649857875459513498643)
      ·
        refine ⟨208218974786813189270247965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138812649857875459513498643 208218974786813189270247965)
        ·
          refine ⟨78082115545054945976342987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208218974786813189270247965 78082115545054945976342987)
          ·
            refine ⟨117123173317582418964514481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78082115545054945976342987 117123173317582418964514481)
            ·
              refine ⟨87842379988186814223385861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117123173317582418964514481 87842379988186814223385861)
              ·
                refine ⟨16470446247785027666884849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87842379988186814223385861 16470446247785027666884849)
                ·
                  refine ⟨12352834685838770750163637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16470446247785027666884849 12352834685838770750163637)
                  ·
                    refine ⟨1158078251797384757827841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12352834685838770750163637 1158078251797384757827841)
                    ·
                      rfl

theorem cell22_3383024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_3383024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383024 prefixEnd_3383024 := by exact prefixLift 3383024
  have htrace : WordTrace (prefixWord ++ tailWord_3383024) baseStart_3383024 baseEnd_3383024 := by
    simpa [prefixWord, tailWord_3383024, baseEnd_3383024] using wordTrace_append hprefix tailTrace_3383024
  have hstable : (prefixWord ++ tailWord_3383024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383024).length < 2 ^ (prefixWord ++ tailWord_3383024).sum := by decide
  have hdescent : baseEnd_3383024 < baseStart_3383024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383026 : List Nat := [3, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_3383026 : Nat := 118140960795 + 3383026 * 2 ^ 59
def prefixEnd_3383026 : Nat := 4983230072969 + 3 ^ 40 * 3383026 * 2
def baseEnd_3383026 : Nat := 386026312146085806425945

theorem tailTrace_3383026 : CollatzResearch.WordTrace tailWord_3383026 prefixEnd_3383026 386026312146085806425945 := by
  unfold tailWord_3383026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30847273760470512921726233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82259396694588034457936621 30847273760470512921726233)
  ·
    refine ⟨23135455320352884691294675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30847273760470512921726233 23135455320352884691294675)
    ·
      refine ⟨34703182980529327036942013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23135455320352884691294675 34703182980529327036942013)
      ·
        refine ⟨13013693617698497638853255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34703182980529327036942013 13013693617698497638853255)
        ·
          refine ⟨19520540426547746458279883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013693617698497638853255 19520540426547746458279883)
          ·
            refine ⟨29280810639821619687419825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19520540426547746458279883 29280810639821619687419825)
            ·
              refine ⟨21960607979866214765564869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29280810639821619687419825 21960607979866214765564869)
              ·
                refine ⟨4117613996224915268543413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21960607979866214765564869 4117613996224915268543413)
                ·
                  refine ⟨386026312146085806425945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4117613996224915268543413 386026312146085806425945)
                  ·
                    rfl

theorem cell22_3383026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_3383026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383026 prefixEnd_3383026 := by exact prefixLift 3383026
  have htrace : WordTrace (prefixWord ++ tailWord_3383026) baseStart_3383026 baseEnd_3383026 := by
    simpa [prefixWord, tailWord_3383026, baseEnd_3383026] using wordTrace_append hprefix tailTrace_3383026
  have hstable : (prefixWord ++ tailWord_3383026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383026).length < 2 ^ (prefixWord ++ tailWord_3383026).sum := by decide
  have hdescent : baseEnd_3383026 < baseStart_3383026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383030 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3383030 : Nat := 118140960795 + 3383030 * 2 ^ 59
def prefixEnd_3383030 : Nat := 4983230072969 + 3 ^ 40 * 3383030 * 2
def baseEnd_3383030 : Nat := 1158080305720002742177823

theorem tailTrace_3383030 : CollatzResearch.WordTrace tailWord_3383030 prefixEnd_3383030 1158080305720002742177823 := by
  unfold tailWord_3383030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7711827558366722523128159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82259493955911706913367029 7711827558366722523128159)
  ·
    refine ⟨11567741337550083784692239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7711827558366722523128159 11567741337550083784692239)
    ·
      refine ⟨17351612006325125677038359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11567741337550083784692239 17351612006325125677038359)
      ·
        refine ⟨26027418009487688515557539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17351612006325125677038359 26027418009487688515557539)
        ·
          refine ⟨39041127014231532773336309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26027418009487688515557539 39041127014231532773336309)
          ·
            refine ⟨3660105657584206197500279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39041127014231532773336309 3660105657584206197500279)
            ·
              refine ⟨5490158486376309296250419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660105657584206197500279 5490158486376309296250419)
              ·
                refine ⟨8235237729564463944375629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490158486376309296250419 8235237729564463944375629)
                ·
                  refine ⟨3088214148586673979140861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8235237729564463944375629 3088214148586673979140861)
                  ·
                    refine ⟨1158080305720002742177823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088214148586673979140861 1158080305720002742177823)
                    ·
                      rfl

theorem cell22_3383030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3383030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383030 prefixEnd_3383030 := by exact prefixLift 3383030
  have htrace : WordTrace (prefixWord ++ tailWord_3383030) baseStart_3383030 baseEnd_3383030 := by
    simpa [prefixWord, tailWord_3383030, baseEnd_3383030] using wordTrace_append hprefix tailTrace_3383030
  have hstable : (prefixWord ++ tailWord_3383030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383030).length < 2 ^ (prefixWord ++ tailWord_3383030).sum := by decide
  have hdescent : baseEnd_3383030 < baseStart_3383030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383103 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 1, 5]
def baseStart_3383103 : Nat := 118140960795 + 3383103 * 2 ^ 59
def prefixEnd_3383103 : Nat := 4983230072969 + 3 ^ 40 * 3383103 * 2
def baseEnd_3383103 : Nat := 1158105295111854885102599

theorem tailTrace_3383103 : CollatzResearch.WordTrace tailWord_3383103 prefixEnd_3383103 1158105295111854885102599 := by
  unfold tailWord_3383103
  simp only [CollatzResearch.WordTrace]
  refine ⟨123391903462603093837457963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82261268975068729224971975 123391903462603093837457963)
  ·
    refine ⟨185087855193904640756186945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123391903462603093837457963 185087855193904640756186945)
    ·
      refine ⟨138815891395428480567140209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185087855193904640756186945 138815891395428480567140209)
      ·
        refine ⟨104111918546571360425355157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138815891395428480567140209 104111918546571360425355157)
        ·
          refine ⟨4880246181870532519938523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104111918546571360425355157 4880246181870532519938523)
          ·
            refine ⟨7320369272805798779907785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880246181870532519938523 7320369272805798779907785)
            ·
              refine ⟨5490276954604349084930839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320369272805798779907785 5490276954604349084930839)
              ·
                refine ⟨8235415431906523627396259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490276954604349084930839 8235415431906523627396259)
                ·
                  refine ⟨12353123147859785441094389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8235415431906523627396259 12353123147859785441094389)
                  ·
                    refine ⟨1158105295111854885102599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12353123147859785441094389 1158105295111854885102599)
                    ·
                      rfl

theorem cell22_3383103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_3383103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383103 prefixEnd_3383103 := by exact prefixLift 3383103
  have htrace : WordTrace (prefixWord ++ tailWord_3383103) baseStart_3383103 baseEnd_3383103 := by
    simpa [prefixWord, tailWord_3383103, baseEnd_3383103] using wordTrace_append hprefix tailTrace_3383103
  have hstable : (prefixWord ++ tailWord_3383103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383103).length < 2 ^ (prefixWord ++ tailWord_3383103).sum := by decide
  have hdescent : baseEnd_3383103 < baseStart_3383103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383148 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 3, 3]
def baseStart_3383148 : Nat := 118140960795 + 3383148 * 2 ^ 59
def prefixEnd_3383148 : Nat := 4983230072969 + 3 ^ 40 * 3383148 * 2
def baseEnd_3383148 : Nat := 1158120699531489767727461

theorem tailTrace_3383148 : CollatzResearch.WordTrace tailWord_3383148 prefixEnd_3383148 1158120699531489767727461 := by
  unfold tailWord_3383148
  simp only [CollatzResearch.WordTrace]
  refine ⟨61696772373720033261423049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82262363164960044348564065 61696772373720033261423049)
  ·
    refine ⟨46272579280290024946067287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61696772373720033261423049 46272579280290024946067287)
    ·
      refine ⟨69408868920435037419100931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46272579280290024946067287 69408868920435037419100931)
      ·
        refine ⟨104113303380652556128651397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69408868920435037419100931 104113303380652556128651397)
        ·
          refine ⟨19521244383872354274122137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104113303380652556128651397 19521244383872354274122137)
          ·
            refine ⟨14640933287904265705591603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19521244383872354274122137 14640933287904265705591603)
            ·
              refine ⟨21961399931856398558387405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14640933287904265705591603 21961399931856398558387405)
              ·
                refine ⟨8235524974446149459395277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21961399931856398558387405 8235524974446149459395277)
                ·
                  refine ⟨3088321865417306047273229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8235524974446149459395277 3088321865417306047273229)
                  ·
                    refine ⟨1158120699531489767727461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088321865417306047273229 1158120699531489767727461)
                    ·
                      rfl

theorem cell22_3383148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 3].length) (baseStart_3383148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383148 prefixEnd_3383148 := by exact prefixLift 3383148
  have htrace : WordTrace (prefixWord ++ tailWord_3383148) baseStart_3383148 baseEnd_3383148 := by
    simpa [prefixWord, tailWord_3383148, baseEnd_3383148] using wordTrace_append hprefix tailTrace_3383148
  have hstable : (prefixWord ++ tailWord_3383148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383148).length < 2 ^ (prefixWord ++ tailWord_3383148).sum := by decide
  have hdescent : baseEnd_3383148 < baseStart_3383148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383199 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 1, 3]
def baseStart_3383199 : Nat := 118140960795 + 3383199 * 2 ^ 59
def prefixEnd_3383199 : Nat := 4983230072969 + 3 ^ 40 * 3383199 * 2
def baseEnd_3383199 : Nat := 1158138157873742634702305

theorem tailTrace_3383199 : CollatzResearch.WordTrace tailWord_3383199 prefixEnd_3383199 1158138157873742634702305 := by
  unfold tailWord_3383199
  simp only [CollatzResearch.WordTrace]
  refine ⟨123395404870255302232952651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82263603246836868155301767 123395404870255302232952651)
  ·
    refine ⟨185093107305382953349428977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123395404870255302232952651 185093107305382953349428977)
    ·
      refine ⟨138819830479037215012071733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185093107305382953349428977 138819830479037215012071733)
      ·
        refine ⟨13014359107409738907381725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138819830479037215012071733 13014359107409738907381725)
        ·
          refine ⟨4880384665278652090268147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13014359107409738907381725 4880384665278652090268147)
          ·
            refine ⟨7320576997917978135402221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880384665278652090268147 7320576997917978135402221)
            ·
              refine ⟨2745216374219241800775833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7320576997917978135402221 2745216374219241800775833)
              ·
                refine ⟨2058912280664431350581875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2745216374219241800775833 2058912280664431350581875)
                ·
                  refine ⟨3088368420996647025872813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058912280664431350581875 3088368420996647025872813)
                  ·
                    refine ⟨1158138157873742634702305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088368420996647025872813 1158138157873742634702305)
                    ·
                      rfl

theorem cell22_3383199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_3383199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383199 prefixEnd_3383199 := by exact prefixLift 3383199
  have htrace : WordTrace (prefixWord ++ tailWord_3383199) baseStart_3383199 baseEnd_3383199 := by
    simpa [prefixWord, tailWord_3383199, baseEnd_3383199] using wordTrace_append hprefix tailTrace_3383199
  have hstable : (prefixWord ++ tailWord_3383199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383199).length < 2 ^ (prefixWord ++ tailWord_3383199).sum := by decide
  have hdescent : baseEnd_3383199 < baseStart_3383199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383255 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 2, 3]
def baseStart_3383255 : Nat := 118140960795 + 3383255 * 2 ^ 59
def prefixEnd_3383255 : Nat := 4983230072969 + 3 ^ 40 * 3383255 * 2
def baseEnd_3383255 : Nat := 1158157327818177155302133

theorem tailTrace_3383255 : CollatzResearch.WordTrace tailWord_3383255 prefixEnd_3383255 1158157327818177155302133 := by
  unfold tailWord_3383255
  simp only [CollatzResearch.WordTrace]
  refine ⟨123397447358052423796991219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82264964905368282531327479 123397447358052423796991219)
  ·
    refine ⟨185096171037078635695486829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123397447358052423796991219 185096171037078635695486829)
    ·
      refine ⟨69411064138904488385807561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185096171037078635695486829 69411064138904488385807561)
      ·
        refine ⟨52058298104178366289355671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69411064138904488385807561 52058298104178366289355671)
        ·
          refine ⟨78087447156267549434033507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52058298104178366289355671 78087447156267549434033507)
          ·
            refine ⟨117131170734401324151050261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78087447156267549434033507 117131170734401324151050261)
            ·
              refine ⟨5490523628175062069580481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117131170734401324151050261 5490523628175062069580481)
              ·
                refine ⟨4117892721131296552185361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5490523628175062069580481 4117892721131296552185361)
                ·
                  refine ⟨3088419540848472414139021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4117892721131296552185361 3088419540848472414139021)
                  ·
                    refine ⟨1158157327818177155302133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088419540848472414139021 1158157327818177155302133)
                    ·
                      rfl

theorem cell22_3383255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 3].length) (baseStart_3383255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383255 prefixEnd_3383255 := by exact prefixLift 3383255
  have htrace : WordTrace (prefixWord ++ tailWord_3383255) baseStart_3383255 baseEnd_3383255 := by
    simpa [prefixWord, tailWord_3383255, baseEnd_3383255] using wordTrace_append hprefix tailTrace_3383255
  have hstable : (prefixWord ++ tailWord_3383255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383255).length < 2 ^ (prefixWord ++ tailWord_3383255).sum := by decide
  have hdescent : baseEnd_3383255 < baseStart_3383255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383317 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3383317 : Nat := 118140960795 + 3383317 * 2 ^ 59
def prefixEnd_3383317 : Nat := 4983230072969 + 3 ^ 40 * 3383317 * 2
def baseEnd_3383317 : Nat := 1158178551685229660251943

theorem tailTrace_3383317 : CollatzResearch.WordTrace tailWord_3383317 prefixEnd_3383317 1158178551685229660251943 := by
  unfold tailWord_3383317
  simp only [CollatzResearch.WordTrace]
  refine ⟨123399708683827808385748205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82266472455885205590498803 123399708683827808385748205)
  ·
    refine ⟨46274890756435428144655577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123399708683827808385748205 46274890756435428144655577)
    ·
      refine ⟨34706168067326571108491683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46274890756435428144655577 34706168067326571108491683)
      ·
        refine ⟨52059252100989856662737525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34706168067326571108491683 52059252100989856662737525)
        ·
          refine ⟨4880554884467799062131643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52059252100989856662737525 4880554884467799062131643)
          ·
            refine ⟨7320832326701698593197465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880554884467799062131643 7320832326701698593197465)
            ·
              refine ⟨5490624245026273944898099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320832326701698593197465 5490624245026273944898099)
              ·
                refine ⟨8235936367539410917347149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490624245026273944898099 8235936367539410917347149)
                ·
                  refine ⟨3088476137827279094005181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8235936367539410917347149 3088476137827279094005181)
                  ·
                    refine ⟨1158178551685229660251943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088476137827279094005181 1158178551685229660251943)
                    ·
                      rfl

theorem cell22_3383317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3383317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383317 prefixEnd_3383317 := by exact prefixLift 3383317
  have htrace : WordTrace (prefixWord ++ tailWord_3383317) baseStart_3383317 baseEnd_3383317 := by
    simpa [prefixWord, tailWord_3383317, baseEnd_3383317] using wordTrace_append hprefix tailTrace_3383317
  have hstable : (prefixWord ++ tailWord_3383317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383317).length < 2 ^ (prefixWord ++ tailWord_3383317).sum := by decide
  have hdescent : baseEnd_3383317 < baseStart_3383317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383360 : List Nat := [2, 1, 1, 2, 2, 4, 2, 3, 1, 4]
def baseStart_3383360 : Nat := 118140960795 + 3383360 * 2 ^ 59
def prefixEnd_3383360 : Nat := 4983230072969 + 3 ^ 40 * 3383360 * 2
def baseEnd_3383360 : Nat := 1158193271463991881426811

theorem tailTrace_3383360 : CollatzResearch.WordTrace tailWord_3383360 prefixEnd_3383360 1158193271463991881426811 := by
  unfold tailWord_3383360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61700638511336013364781767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82267518015114684486375689 61700638511336013364781767)
  ·
    refine ⟨92550957767004020047172651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61700638511336013364781767 92550957767004020047172651)
    ·
      refine ⟨138826436650506030070758977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92550957767004020047172651 138826436650506030070758977)
      ·
        refine ⟨104119827487879522553069233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138826436650506030070758977 104119827487879522553069233)
        ·
          refine ⟨78089870615909641914801925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104119827487879522553069233 78089870615909641914801925)
          ·
            refine ⟨14641850740483057859025361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78089870615909641914801925 14641850740483057859025361)
            ·
              refine ⟨10981388055362293394269021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14641850740483057859025361 10981388055362293394269021)
              ·
                refine ⟨4118020520760860022850883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10981388055362293394269021 4118020520760860022850883)
                ·
                  refine ⟨6177030781141290034276325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118020520760860022850883 6177030781141290034276325)
                  ·
                    refine ⟨1158193271463991881426811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177030781141290034276325 1158193271463991881426811)
                    ·
                      rfl

theorem cell22_3383360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_3383360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383360 prefixEnd_3383360 := by exact prefixLift 3383360
  have htrace : WordTrace (prefixWord ++ tailWord_3383360) baseStart_3383360 baseEnd_3383360 := by
    simpa [prefixWord, tailWord_3383360, baseEnd_3383360] using wordTrace_append hprefix tailTrace_3383360
  have hstable : (prefixWord ++ tailWord_3383360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383360).length < 2 ^ (prefixWord ++ tailWord_3383360).sum := by decide
  have hdescent : baseEnd_3383360 < baseStart_3383360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383433 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_3383433 : Nat := 118140960795 + 3383433 * 2 ^ 59
def prefixEnd_3383433 : Nat := 4983230072969 + 3 ^ 40 * 3383433 * 2
def baseEnd_3383433 : Nat := 1158218260855844024351587

theorem tailTrace_3383433 : CollatzResearch.WordTrace tailWord_3383433 prefixEnd_3383433 1158218260855844024351587 := by
  unfold tailWord_3383433
  simp only [CollatzResearch.WordTrace]
  refine ⟨123403939551407560196970953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82269293034271706797980635 123403939551407560196970953)
  ·
    refine ⟨92552954663555670147728215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123403939551407560196970953 92552954663555670147728215)
    ·
      refine ⟨138829431995333505221592323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92552954663555670147728215 138829431995333505221592323)
      ·
        refine ⟨208244147993000257832388485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138829431995333505221592323 208244147993000257832388485)
        ·
          refine ⟨39045777748687548343572841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208244147993000257832388485 39045777748687548343572841)
          ·
            refine ⟨29284333311515661257679631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39045777748687548343572841 29284333311515661257679631)
            ·
              refine ⟨43926499967273491886519447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29284333311515661257679631 43926499967273491886519447)
              ·
                refine ⟨65889749950910237829779171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43926499967273491886519447 65889749950910237829779171)
                ·
                  refine ⟨98834624926365356744668757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65889749950910237829779171 98834624926365356744668757)
                  ·
                    refine ⟨1158218260855844024351587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98834624926365356744668757 1158218260855844024351587)
                    ·
                      rfl

theorem cell22_3383433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_3383433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383433 prefixEnd_3383433 := by exact prefixLift 3383433
  have htrace : WordTrace (prefixWord ++ tailWord_3383433) baseStart_3383433 baseEnd_3383433 := by
    simpa [prefixWord, tailWord_3383433, baseEnd_3383433] using wordTrace_append hprefix tailTrace_3383433
  have hstable : (prefixWord ++ tailWord_3383433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383433).length < 2 ^ (prefixWord ++ tailWord_3383433).sum := by decide
  have hdescent : baseEnd_3383433 < baseStart_3383433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383452 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_3383452 : Nat := 118140960795 + 3383452 * 2 ^ 59
def prefixEnd_3383452 : Nat := 4983230072969 + 3 ^ 40 * 3383452 * 2
def baseEnd_3383452 : Nat := 1158224764944134308126529

theorem tailTrace_3383452 : CollatzResearch.WordTrace tailWord_3383452 prefixEnd_3383452 1158224764944134308126529 := by
  unfold tailWord_3383452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61702316269169363220956305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82269755025559150961275073 61702316269169363220956305)
  ·
    refine ⟨46276737201877022415717229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61702316269169363220956305 46276737201877022415717229)
    ·
      refine ⟨17353776450703883405893961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46276737201877022415717229 17353776450703883405893961)
      ·
        refine ⟨13015332338027912554420471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17353776450703883405893961 13015332338027912554420471)
        ·
          refine ⟨19522998507041868831630707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13015332338027912554420471 19522998507041868831630707)
          ·
            refine ⟨29284497760562803247446061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19522998507041868831630707 29284497760562803247446061)
            ·
              refine ⟨10981686660211051217792273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29284497760562803247446061 10981686660211051217792273)
              ·
                refine ⟨8236264995158288413344205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10981686660211051217792273 8236264995158288413344205)
                ·
                  refine ⟨3088599373184358155004077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8236264995158288413344205 3088599373184358155004077)
                  ·
                    refine ⟨1158224764944134308126529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088599373184358155004077 1158224764944134308126529)
                    ·
                      rfl

theorem cell22_3383452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_3383452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383452 prefixEnd_3383452 := by exact prefixLift 3383452
  have htrace : WordTrace (prefixWord ++ tailWord_3383452) baseStart_3383452 baseEnd_3383452 := by
    simpa [prefixWord, tailWord_3383452, baseEnd_3383452] using wordTrace_append hprefix tailTrace_3383452
  have hstable : (prefixWord ++ tailWord_3383452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383452).length < 2 ^ (prefixWord ++ tailWord_3383452).sum := by decide
  have hdescent : baseEnd_3383452 < baseStart_3383452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383454 : List Nat := [4, 3, 1, 1, 3, 1, 3, 6]
def baseStart_3383454 : Nat := 118140960795 + 3383454 * 2 ^ 59
def prefixEnd_3383454 : Nat := 4983230072969 + 3 ^ 40 * 3383454 * 2
def baseEnd_3383454 : Nat := 128691716620556329952947

theorem tailTrace_3383454 : CollatzResearch.WordTrace tailWord_3383454 prefixEnd_3383454 128691716620556329952947 := by
  unfold tailWord_3383454
  simp only [CollatzResearch.WordTrace]
  refine ⟨15425588185541435097935677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82269803656220987188990277 15425588185541435097935677)
  ·
    refine ⟨5784595569578038161725879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15425588185541435097935677 5784595569578038161725879)
    ·
      refine ⟨8676893354367057242588819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5784595569578038161725879 8676893354367057242588819)
      ·
        refine ⟨13015340031550585863883229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8676893354367057242588819 13015340031550585863883229)
        ·
          refine ⟨4880752511831469698956211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13015340031550585863883229 4880752511831469698956211)
          ·
            refine ⟨7321128767747204548434317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4880752511831469698956211 7321128767747204548434317)
            ·
              refine ⟨2745423287905201705662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7321128767747204548434317 2745423287905201705662869)
              ·
                refine ⟨128691716620556329952947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2745423287905201705662869 128691716620556329952947)
                ·
                  rfl

theorem cell22_3383454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_3383454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383454 prefixEnd_3383454 := by exact prefixLift 3383454
  have htrace : WordTrace (prefixWord ++ tailWord_3383454) baseStart_3383454 baseEnd_3383454 := by
    simpa [prefixWord, tailWord_3383454, baseEnd_3383454] using wordTrace_append hprefix tailTrace_3383454
  have hstable : (prefixWord ++ tailWord_3383454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383454).length < 2 ^ (prefixWord ++ tailWord_3383454).sum := by decide
  have hdescent : baseEnd_3383454 < baseStart_3383454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383512 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 1, 4]
def baseStart_3383512 : Nat := 118140960795 + 3383512 * 2 ^ 59
def prefixEnd_3383512 : Nat := 4983230072969 + 3 ^ 40 * 3383512 * 2
def baseEnd_3383512 : Nat := 1158245304170314151626345

theorem tailTrace_3383512 : CollatzResearch.WordTrace tailWord_3383512 prefixEnd_3383512 1158245304170314151626345 := by
  unfold tailWord_3383512
  simp only [CollatzResearch.WordTrace]
  refine ⟨61703410459060678344548395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82271213945414237792731193 61703410459060678344548395)
  ·
    refine ⟨92555115688591017516822593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61703410459060678344548395 92555115688591017516822593)
    ·
      refine ⟨69416336766443263137616945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92555115688591017516822593 69416336766443263137616945)
      ·
        refine ⟨52062252574832447353212709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69416336766443263137616945 52062252574832447353212709)
        ·
          refine ⟨9761672357781083878727383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52062252574832447353212709 9761672357781083878727383)
          ·
            refine ⟨14642508536671625818091075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9761672357781083878727383 14642508536671625818091075)
            ·
              refine ⟨21963762805007438727136613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14642508536671625818091075 21963762805007438727136613)
              ·
                refine ⟨4118205525938894761338115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21963762805007438727136613 4118205525938894761338115)
                ·
                  refine ⟨6177308288908342142007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118205525938894761338115 6177308288908342142007173)
                  ·
                    refine ⟨1158245304170314151626345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177308288908342142007173 1158245304170314151626345)
                    ·
                      rfl

theorem cell22_3383512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_3383512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383512 prefixEnd_3383512 := by exact prefixLift 3383512
  have htrace : WordTrace (prefixWord ++ tailWord_3383512) baseStart_3383512 baseEnd_3383512 := by
    simpa [prefixWord, tailWord_3383512, baseEnd_3383512] using wordTrace_append hprefix tailTrace_3383512
  have hstable : (prefixWord ++ tailWord_3383512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383512).length < 2 ^ (prefixWord ++ tailWord_3383512).sum := by decide
  have hdescent : baseEnd_3383512 < baseStart_3383512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383555 : List Nat := [1, 1, 1, 3, 2, 3, 4, 7]
def baseStart_3383555 : Nat := 118140960795 + 3383555 * 2 ^ 59
def prefixEnd_3383555 : Nat := 4983230072969 + 3 ^ 40 * 3383555 * 2
def baseEnd_3383555 : Nat := 128695558216564041422357

theorem tailTrace_3383555 : CollatzResearch.WordTrace tailWord_3383555 prefixEnd_3383555 128695558216564041422357 := by
  unfold tailWord_3383555
  simp only [CollatzResearch.WordTrace]
  refine ⟨123408389256965575032912119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82272259504643716688608079 123408389256965575032912119)
  ·
    refine ⟨185112583885448362549368179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123408389256965575032912119 185112583885448362549368179)
    ·
      refine ⟨277668875828172543824052269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185112583885448362549368179 277668875828172543824052269)
      ·
        refine ⟨104125828435564703934019601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277668875828172543824052269 104125828435564703934019601)
        ·
          refine ⟨78094371326673527950514701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104125828435564703934019601 78094371326673527950514701)
          ·
            refine ⟨29285389247502572981443013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78094371326673527950514701 29285389247502572981443013)
            ·
              refine ⟨5491010483906732434020565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29285389247502572981443013 5491010483906732434020565)
              ·
                refine ⟨128695558216564041422357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5491010483906732434020565 128695558216564041422357)
                ·
                  rfl

theorem cell22_3383555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 7].length) (baseStart_3383555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383555 prefixEnd_3383555 := by exact prefixLift 3383555
  have htrace : WordTrace (prefixWord ++ tailWord_3383555) baseStart_3383555 baseEnd_3383555 := by
    simpa [prefixWord, tailWord_3383555, baseEnd_3383555] using wordTrace_append hprefix tailTrace_3383555
  have hstable : (prefixWord ++ tailWord_3383555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383555).length < 2 ^ (prefixWord ++ tailWord_3383555).sum := by decide
  have hdescent : baseEnd_3383555 < baseStart_3383555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383681 : List Nat := [1, 2, 4, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3383681 : Nat := 118140960795 + 3383681 * 2 ^ 59
def prefixEnd_3383681 : Nat := 4983230072969 + 3 ^ 40 * 3383681 * 2
def baseEnd_3383681 : Nat := 1158303156324054044150827

theorem tailTrace_3383681 : CollatzResearch.WordTrace tailWord_3383681 prefixEnd_3383681 1158303156324054044150827 := by
  unfold tailWord_3383681
  simp only [CollatzResearch.WordTrace]
  refine ⟨123412984854509098551998897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82275323236339399034665931 123412984854509098551998897)
  ·
    refine ⟨92559738640881823913999173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123412984854509098551998897 92559738640881823913999173)
    ·
      refine ⟨17354950995165341983874845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92559738640881823913999173 17354950995165341983874845)
      ·
        refine ⟨6508106623187003243953067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17354950995165341983874845 6508106623187003243953067)
        ·
          refine ⟨9762159934780504865929601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508106623187003243953067 9762159934780504865929601)
          ·
            refine ⟨7321619951085378649447201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9762159934780504865929601 7321619951085378649447201)
            ·
              refine ⟨5491214963314033987085401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7321619951085378649447201 5491214963314033987085401)
              ·
                refine ⟨4118411222485525490314051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491214963314033987085401 4118411222485525490314051)
                ·
                  refine ⟨6177616833728288235471077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118411222485525490314051 6177616833728288235471077)
                  ·
                    refine ⟨1158303156324054044150827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177616833728288235471077 1158303156324054044150827)
                    ·
                      rfl

theorem cell22_3383681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3383681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383681 prefixEnd_3383681 := by exact prefixLift 3383681
  have htrace : WordTrace (prefixWord ++ tailWord_3383681) baseStart_3383681 baseEnd_3383681 := by
    simpa [prefixWord, tailWord_3383681, baseEnd_3383681] using wordTrace_append hprefix tailTrace_3383681
  have hstable : (prefixWord ++ tailWord_3383681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383681).length < 2 ^ (prefixWord ++ tailWord_3383681).sum := by decide
  have hdescent : baseEnd_3383681 < baseStart_3383681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383692 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3383692 : Nat := 118140960795 + 3383692 * 2 ^ 59
def prefixEnd_3383692 : Nat := 4983230072969 + 3 ^ 40 * 3383692 * 2
def baseEnd_3383692 : Nat := 1158306921848853682125793

theorem tailTrace_3383692 : CollatzResearch.WordTrace tailWord_3383692 prefixEnd_3383692 1158306921848853682125793 := by
  unfold tailWord_3383692
  simp only [CollatzResearch.WordTrace]
  refine ⟨61706693028734623715324665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82275590704979498287099553 61706693028734623715324665)
  ·
    refine ⟨46280019771550967786493499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61706693028734623715324665 46280019771550967786493499)
    ·
      refine ⟨69420029657326451679740249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46280019771550967786493499 69420029657326451679740249)
      ·
        refine ⟨52065022242994838759805187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69420029657326451679740249 52065022242994838759805187)
        ·
          refine ⟨78097533364492258139707781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52065022242994838759805187 78097533364492258139707781)
          ·
            refine ⟨14643287505842298401195209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78097533364492258139707781 14643287505842298401195209)
            ·
              refine ⟨10982465629381723800896407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14643287505842298401195209 10982465629381723800896407)
              ·
                refine ⟨16473698444072585701344611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982465629381723800896407 16473698444072585701344611)
                ·
                  refine ⟨24710547666108878552016917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16473698444072585701344611 24710547666108878552016917)
                  ·
                    refine ⟨1158306921848853682125793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24710547666108878552016917 1158306921848853682125793)
                    ·
                      rfl

theorem cell22_3383692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3383692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383692 prefixEnd_3383692 := by exact prefixLift 3383692
  have htrace : WordTrace (prefixWord ++ tailWord_3383692) baseStart_3383692 baseEnd_3383692 := by
    simpa [prefixWord, tailWord_3383692, baseEnd_3383692] using wordTrace_append hprefix tailTrace_3383692
  have hstable : (prefixWord ++ tailWord_3383692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383692).length < 2 ^ (prefixWord ++ tailWord_3383692).sum := by decide
  have hdescent : baseEnd_3383692 < baseStart_3383692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383713 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 6]
def baseStart_3383713 : Nat := 118140960795 + 3383713 * 2 ^ 59
def prefixEnd_3383713 : Nat := 4983230072969 + 3 ^ 40 * 3383713 * 2
def baseEnd_3383713 : Nat := 386104703526005542450243

theorem tailTrace_3383713 : CollatzResearch.WordTrace tailWord_3383713 prefixEnd_3383713 386104703526005542450243 := by
  unfold tailWord_3383713
  simp only [CollatzResearch.WordTrace]
  refine ⟨123414151990393168017163793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82276101326928778678109195 123414151990393168017163793)
  ·
    refine ⟨92560613992794876012872845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123414151990393168017163793 92560613992794876012872845)
    ·
      refine ⟨34710230247298078504827317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92560613992794876012872845 34710230247298078504827317)
      ·
        refine ⟨3254084085684194859827561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34710230247298078504827317 3254084085684194859827561)
        ·
          refine ⟨2440563064263146144870671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3254084085684194859827561 2440563064263146144870671)
          ·
            refine ⟨3660844596394719217306007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440563064263146144870671 3660844596394719217306007)
            ·
              refine ⟨5491266894592078825959011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660844596394719217306007 5491266894592078825959011)
              ·
                refine ⟨8236900341888118238938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491266894592078825959011 8236900341888118238938517)
                ·
                  refine ⟨386104703526005542450243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8236900341888118238938517 386104703526005542450243)
                  ·
                    rfl

theorem cell22_3383713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 6].length) (baseStart_3383713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383713 prefixEnd_3383713 := by exact prefixLift 3383713
  have htrace : WordTrace (prefixWord ++ tailWord_3383713) baseStart_3383713 baseEnd_3383713 := by
    simpa [prefixWord, tailWord_3383713, baseEnd_3383713] using wordTrace_append hprefix tailTrace_3383713
  have hstable : (prefixWord ++ tailWord_3383713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383713).length < 2 ^ (prefixWord ++ tailWord_3383713).sum := by decide
  have hdescent : baseEnd_3383713 < baseStart_3383713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383732 : List Nat := [2, 5, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3383732 : Nat := 118140960795 + 3383732 * 2 ^ 59
def prefixEnd_3383732 : Nat := 4983230072969 + 3 ^ 40 * 3383732 * 2
def baseEnd_3383732 : Nat := 1158320614666306911125671

theorem tailTrace_3383732 : CollatzResearch.WordTrace tailWord_3383732 prefixEnd_3383732 1158320614666306911125671 := by
  unfold tailWord_3383732
  simp only [CollatzResearch.WordTrace]
  refine ⟨61707422488662167131052725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82276563318216222841403633 61707422488662167131052725)
  ·
    refine ⟨5785070858312078168536193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61707422488662167131052725 5785070858312078168536193)
    ·
      refine ⟨4338803143734058626402145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5785070858312078168536193 4338803143734058626402145)
      ·
        refine ⟨3254102357800543969801609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4338803143734058626402145 3254102357800543969801609)
        ·
          refine ⟨2440576768350407977351207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3254102357800543969801609 2440576768350407977351207)
          ·
            refine ⟨3660865152525611966026811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2440576768350407977351207 3660865152525611966026811)
            ·
              refine ⟨5491297728788417949040217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660865152525611966026811 5491297728788417949040217)
              ·
                refine ⟨4118473296591313461780163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491297728788417949040217 4118473296591313461780163)
                ·
                  refine ⟨6177709944886970192670245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118473296591313461780163 6177709944886970192670245)
                  ·
                    refine ⟨1158320614666306911125671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177709944886970192670245 1158320614666306911125671)
                    ·
                      rfl

theorem cell22_3383732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3383732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383732 prefixEnd_3383732 := by exact prefixLift 3383732
  have htrace : WordTrace (prefixWord ++ tailWord_3383732) baseStart_3383732 baseEnd_3383732 := by
    simpa [prefixWord, tailWord_3383732, baseEnd_3383732] using wordTrace_append hprefix tailTrace_3383732
  have hstable : (prefixWord ++ tailWord_3383732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383732).length < 2 ^ (prefixWord ++ tailWord_3383732).sum := by decide
  have hdescent : baseEnd_3383732 < baseStart_3383732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383769 : List Nat := [1, 2, 1, 2, 4, 1, 4, 2, 5]
def baseStart_3383769 : Nat := 118140960795 + 3383769 * 2 ^ 59
def prefixEnd_3383769 : Nat := 4983230072969 + 3 ^ 40 * 3383769 * 2
def baseEnd_3383769 : Nat := 386111093507483715983519

theorem tailTrace_3383769 : CollatzResearch.WordTrace tailWord_3383769 prefixEnd_3383769 386111093507483715983519 := by
  unfold tailWord_3383769
  simp only [CollatzResearch.WordTrace]
  refine ⟨123416194478190289581202361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82277462985460193054134907 123416194478190289581202361)
  ·
    refine ⟨92562145858642717185901771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123416194478190289581202361 92562145858642717185901771)
    ·
      refine ⟨138843218787964075778852657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92562145858642717185901771 138843218787964075778852657)
      ·
        refine ⟨104132414090973056834139493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138843218787964075778852657 104132414090973056834139493)
        ·
          refine ⟨19524827642057448156401155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104132414090973056834139493 19524827642057448156401155)
          ·
            refine ⟨29287241463086172234601733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19524827642057448156401155 29287241463086172234601733)
            ·
              refine ⟨5491357774328657293987825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29287241463086172234601733 5491357774328657293987825)
              ·
                refine ⟨4118518330746492970490869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5491357774328657293987825 4118518330746492970490869)
                ·
                  refine ⟨386111093507483715983519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4118518330746492970490869 386111093507483715983519)
                  ·
                    rfl

theorem cell22_3383769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_3383769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383769 prefixEnd_3383769 := by exact prefixLift 3383769
  have htrace : WordTrace (prefixWord ++ tailWord_3383769) baseStart_3383769 baseEnd_3383769 := by
    simpa [prefixWord, tailWord_3383769, baseEnd_3383769] using wordTrace_append hprefix tailTrace_3383769
  have hstable : (prefixWord ++ tailWord_3383769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383769).length < 2 ^ (prefixWord ++ tailWord_3383769).sum := by decide
  have hdescent : baseEnd_3383769 < baseStart_3383769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383773 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 1, 3]
def baseStart_3383773 : Nat := 118140960795 + 3383773 * 2 ^ 59
def prefixEnd_3383773 : Nat := 4983230072969 + 3 ^ 40 * 3383773 * 2
def baseEnd_3383773 : Nat := 1158334649804196470850545

theorem tailTrace_3383773 : CollatzResearch.WordTrace tailWord_3383773 prefixEnd_3383773 1158334649804196470850545 := by
  unfold tailWord_3383773
  simp only [CollatzResearch.WordTrace]
  refine ⟨123416340370175798264347973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82277560246783865509565315 123416340370175798264347973)
  ·
    refine ⟨23140563819407962174565245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123416340370175798264347973 23140563819407962174565245)
    ·
      refine ⟨8677711432277985815461967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23140563819407962174565245 8677711432277985815461967)
      ·
        refine ⟨13016567148416978723192951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677711432277985815461967 13016567148416978723192951)
        ·
          refine ⟨19524850722625468084789427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13016567148416978723192951 19524850722625468084789427)
          ·
            refine ⟨29287276083938202127184141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19524850722625468084789427 29287276083938202127184141)
            ·
              refine ⟨10982728531476825797694053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29287276083938202127184141 10982728531476825797694053)
              ·
                refine ⟨2059261599651904837067635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10982728531476825797694053 2059261599651904837067635)
                ·
                  refine ⟨3088892399477857255601453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059261599651904837067635 3088892399477857255601453)
                  ·
                    refine ⟨1158334649804196470850545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3088892399477857255601453 1158334649804196470850545)
                    ·
                      rfl

theorem cell22_3383773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_3383773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383773 prefixEnd_3383773 := by exact prefixLift 3383773
  have htrace : WordTrace (prefixWord ++ tailWord_3383773) baseStart_3383773 baseEnd_3383773 := by
    simpa [prefixWord, tailWord_3383773, baseEnd_3383773] using wordTrace_append hprefix tailTrace_3383773
  have hstable : (prefixWord ++ tailWord_3383773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383773).length < 2 ^ (prefixWord ++ tailWord_3383773).sum := by decide
  have hdescent : baseEnd_3383773 < baseStart_3383773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383784 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 2, 5]
def baseStart_3383784 : Nat := 118140960795 + 3383784 * 2 ^ 59
def prefixEnd_3383784 : Nat := 4983230072969 + 3 ^ 40 * 3383784 * 2
def baseEnd_3383784 : Nat := 1158338415328996108825511

theorem tailTrace_3383784 : CollatzResearch.WordTrace tailWord_3383784 prefixEnd_3383784 1158338415328996108825511 := by
  unfold tailWord_3383784
  simp only [CollatzResearch.WordTrace]
  refine ⟨61708370786567973571499203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82277827715423964761998937 61708370786567973571499203)
  ·
    refine ⟨92562556179851960357248805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61708370786567973571499203 92562556179851960357248805)
    ·
      refine ⟨17355479283722242566984151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92562556179851960357248805 17355479283722242566984151)
      ·
        refine ⟨26033218925583363850476227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17355479283722242566984151 26033218925583363850476227)
        ·
          refine ⟨39049828388375045775714341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26033218925583363850476227 39049828388375045775714341)
          ·
            refine ⟨7321842822820321082946439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39049828388375045775714341 7321842822820321082946439)
            ·
              refine ⟨10982764234230481624419659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7321842822820321082946439 10982764234230481624419659)
              ·
                refine ⟨16474146351345722436629489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10982764234230481624419659 16474146351345722436629489)
                ·
                  refine ⟨12355609763509291827472117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16474146351345722436629489 12355609763509291827472117)
                  ·
                    refine ⟨1158338415328996108825511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12355609763509291827472117 1158338415328996108825511)
                    ·
                      rfl

theorem cell22_3383784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_3383784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383784 prefixEnd_3383784 := by exact prefixLift 3383784
  have htrace : WordTrace (prefixWord ++ tailWord_3383784) baseStart_3383784 baseEnd_3383784 := by
    simpa [prefixWord, tailWord_3383784, baseEnd_3383784] using wordTrace_append hprefix tailTrace_3383784
  have hstable : (prefixWord ++ tailWord_3383784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383784).length < 2 ^ (prefixWord ++ tailWord_3383784).sum := by decide
  have hdescent : baseEnd_3383784 < baseStart_3383784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383878 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_3383878 : Nat := 118140960795 + 3383878 * 2 ^ 59
def prefixEnd_3383878 : Nat := 4983230072969 + 3 ^ 40 * 3383878 * 2
def baseEnd_3383878 : Nat := 1158370593450011196975223

theorem tailTrace_3383878 : CollatzResearch.WordTrace tailWord_3383878 prefixEnd_3383878 1158370593450011196975223 := by
  unfold tailWord_3383878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856880313587356287403759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82280113356530267464613525 3856880313587356287403759)
  ·
    refine ⟨5785320470381034431105639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856880313587356287403759 5785320470381034431105639)
    ·
      refine ⟨8677980705571551646658459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5785320470381034431105639 8677980705571551646658459)
      ·
        refine ⟨13016971058357327469987689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8677980705571551646658459 13016971058357327469987689)
        ·
          refine ⟨9762728293767995602490767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13016971058357327469987689 9762728293767995602490767)
          ·
            refine ⟨14644092440651993403736151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9762728293767995602490767 14644092440651993403736151)
            ·
              refine ⟨21966138660977990105604227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14644092440651993403736151 21966138660977990105604227)
              ·
                refine ⟨32949207991466985158406341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21966138660977990105604227 32949207991466985158406341)
                ·
                  refine ⟨6177976498400059717201189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32949207991466985158406341 6177976498400059717201189)
                  ·
                    refine ⟨1158370593450011196975223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6177976498400059717201189 1158370593450011196975223)
                    ·
                      rfl

theorem cell22_3383878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_3383878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383878 prefixEnd_3383878 := by exact prefixLift 3383878
  have htrace : WordTrace (prefixWord ++ tailWord_3383878) baseStart_3383878 baseEnd_3383878 := by
    simpa [prefixWord, tailWord_3383878, baseEnd_3383878] using wordTrace_append hprefix tailTrace_3383878
  have hstable : (prefixWord ++ tailWord_3383878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383878).length < 2 ^ (prefixWord ++ tailWord_3383878).sum := by decide
  have hdescent : baseEnd_3383878 < baseStart_3383878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383983 : List Nat := [1, 1, 2, 1, 2, 6, 2, 3, 4]
def baseStart_3383983 : Nat := 118140960795 + 3383983 * 2 ^ 59
def prefixEnd_3383983 : Nat := 4983230072969 + 3 ^ 40 * 3383983 * 2
def baseEnd_3383983 : Nat := 386135512365275307699967

theorem tailTrace_3383983 : CollatzResearch.WordTrace tailWord_3383983 prefixEnd_3383983 386135512365275307699967 := by
  unfold tailWord_3383983
  simp only [CollatzResearch.WordTrace]
  refine ⟨123423999699415004129492603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82282666466276669419661735 123423999699415004129492603)
  ·
    refine ⟨185135999549122506194238905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123423999699415004129492603 185135999549122506194238905)
    ·
      refine ⟨138851999661841879645679179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185135999549122506194238905 138851999661841879645679179)
      ·
        refine ⟨208277999492762819468518769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138851999661841879645679179 208277999492762819468518769)
        ·
          refine ⟨156208499619572114601389077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208277999492762819468518769 156208499619572114601389077)
          ·
            refine ⟨7322273419667442871940113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156208499619572114601389077 7322273419667442871940113)
            ·
              refine ⟨5491705064750582153955085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7322273419667442871940113 5491705064750582153955085)
              ·
                refine ⟨2059389399281468307733157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5491705064750582153955085 2059389399281468307733157)
                ·
                  refine ⟨386135512365275307699967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059389399281468307733157 386135512365275307699967)
                  ·
                    rfl

theorem cell22_3383983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 4].length) (baseStart_3383983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383983 prefixEnd_3383983 := by exact prefixLift 3383983
  have htrace : WordTrace (prefixWord ++ tailWord_3383983) baseStart_3383983 baseEnd_3383983 := by
    simpa [prefixWord, tailWord_3383983, baseEnd_3383983] using wordTrace_append hprefix tailTrace_3383983
  have hstable : (prefixWord ++ tailWord_3383983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383983).length < 2 ^ (prefixWord ++ tailWord_3383983).sum := by decide
  have hdescent : baseEnd_3383983 < baseStart_3383983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383985 : List Nat := [1, 2, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_3383985 : Nat := 118140960795 + 3383985 * 2 ^ 59
def prefixEnd_3383985 : Nat := 4983230072969 + 3 ^ 40 * 3383985 * 2
def baseEnd_3383985 : Nat := 1158407221736698584549895

theorem tailTrace_3383985 : CollatzResearch.WordTrace tailWord_3383985 prefixEnd_3383985 1158407221736698584549895 := by
  unfold tailWord_3383985
  simp only [CollatzResearch.WordTrace]
  refine ⟨123424072645407758471065409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82282715096938505647376939 123424072645407758471065409)
  ·
    refine ⟨92568054484055818853299057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123424072645407758471065409 92568054484055818853299057)
    ·
      refine ⟨69426040863041864139974293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92568054484055818853299057 69426040863041864139974293)
      ·
        refine ⟨3254345665455087381561295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69426040863041864139974293 3254345665455087381561295)
        ·
          refine ⟨4881518498182631072341943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254345665455087381561295 4881518498182631072341943)
          ·
            refine ⟨7322277747273946608512915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881518498182631072341943 7322277747273946608512915)
            ·
              refine ⟨10983416620910919912769373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322277747273946608512915 10983416620910919912769373)
              ·
                refine ⟨4118781232841594967288515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10983416620910919912769373 4118781232841594967288515)
                ·
                  refine ⟨6178171849262392450932773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4118781232841594967288515 6178171849262392450932773)
                  ·
                    refine ⟨1158407221736698584549895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6178171849262392450932773 1158407221736698584549895)
                    ·
                      rfl

theorem cell22_3383985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_3383985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383985 prefixEnd_3383985 := by exact prefixLift 3383985
  have htrace : WordTrace (prefixWord ++ tailWord_3383985) baseStart_3383985 baseEnd_3383985 := by
    simpa [prefixWord, tailWord_3383985, baseEnd_3383985] using wordTrace_append hprefix tailTrace_3383985
  have hstable : (prefixWord ++ tailWord_3383985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383985).length < 2 ^ (prefixWord ++ tailWord_3383985).sum := by decide
  have hdescent : baseEnd_3383985 < baseStart_3383985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383994 : List Nat := [3, 1, 1, 1, 2, 3, 11]
def baseStart_3383994 : Nat := 118140960795 + 3383994 * 2 ^ 59
def prefixEnd_3383994 : Nat := 4983230072969 + 3 ^ 40 * 3383994 * 2
def baseEnd_3383994 : Nat := 42904085282245391150921

theorem tailTrace_3383994 : CollatzResearch.WordTrace tailWord_3383994 prefixEnd_3383994 42904085282245391150921 := by
  unfold tailWord_3383994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30856100225593788252035759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82282933934916768672095357 30856100225593788252035759)
  ·
    refine ⟨46284150338390682378053639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30856100225593788252035759 46284150338390682378053639)
    ·
      refine ⟨69426225507586023567080459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46284150338390682378053639 69426225507586023567080459)
      ·
        refine ⟨104139338261379035350620689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69426225507586023567080459 104139338261379035350620689)
        ·
          refine ⟨78104503696034276512965517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104139338261379035350620689 78104503696034276512965517)
          ·
            refine ⟨29289188886012853692362069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78104503696034276512965517 29289188886012853692362069)
            ·
              refine ⟨42904085282245391150921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29289188886012853692362069 42904085282245391150921)
              ·
                rfl

theorem cell22_3383994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 11].length) (baseStart_3383994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383994 prefixEnd_3383994 := by exact prefixLift 3383994
  have htrace : WordTrace (prefixWord ++ tailWord_3383994) baseStart_3383994 baseEnd_3383994 := by
    simpa [prefixWord, tailWord_3383994, baseEnd_3383994] using wordTrace_append hprefix tailTrace_3383994
  have hstable : (prefixWord ++ tailWord_3383994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383994).length < 2 ^ (prefixWord ++ tailWord_3383994).sum := by decide
  have hdescent : baseEnd_3383994 < baseStart_3383994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383996 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3383996 : Nat := 118140960795 + 3383996 * 2 ^ 59
def prefixEnd_3383996 : Nat := 4983230072969 + 3 ^ 40 * 3383996 * 2
def baseEnd_3383996 : Nat := 1158410987261498222524861

theorem tailTrace_3383996 : CollatzResearch.WordTrace tailWord_3383996 prefixEnd_3383996 1158410987261498222524861 := by
  unfold tailWord_3383996
  simp only [CollatzResearch.WordTrace]
  refine ⟨61712236924183953674857921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82282982565578604899810561 61712236924183953674857921)
  ·
    refine ⟨46284177693137965256143441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61712236924183953674857921 46284177693137965256143441)
    ·
      refine ⟨34713133269853473942107581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46284177693137965256143441 34713133269853473942107581)
      ·
        refine ⟨13017424976195052728290343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34713133269853473942107581 13017424976195052728290343)
        ·
          refine ⟨19526137464292579092435515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13017424976195052728290343 19526137464292579092435515)
          ·
            refine ⟨29289206196438868638653273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19526137464292579092435515 29289206196438868638653273)
            ·
              refine ⟨21966904647329151478989955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29289206196438868638653273 21966904647329151478989955)
              ·
                refine ⟨32950356970993727218484933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21966904647329151478989955 32950356970993727218484933)
                ·
                  refine ⟨6178191932061323853465925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32950356970993727218484933 6178191932061323853465925)
                  ·
                    refine ⟨1158410987261498222524861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6178191932061323853465925 1158410987261498222524861)
                    ·
                      rfl

theorem cell22_3383996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3383996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383996 prefixEnd_3383996 := by exact prefixLift 3383996
  have htrace : WordTrace (prefixWord ++ tailWord_3383996) baseStart_3383996 baseEnd_3383996 := by
    simpa [prefixWord, tailWord_3383996, baseEnd_3383996] using wordTrace_append hprefix tailTrace_3383996
  have hstable : (prefixWord ++ tailWord_3383996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383996).length < 2 ^ (prefixWord ++ tailWord_3383996).sum := by decide
  have hdescent : baseEnd_3383996 < baseStart_3383996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3383998 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_3383998 : Nat := 118140960795 + 3383998 * 2 ^ 59
def prefixEnd_3383998 : Nat := 4983230072969 + 3 ^ 40 * 3383998 * 2
def baseEnd_3383998 : Nat := 1158411671902370883974855

theorem tailTrace_3383998 : CollatzResearch.WordTrace tailWord_3383998 prefixEnd_3383998 1158411671902370883974855 := by
  unfold tailWord_3383998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15428068349295082711411081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82283031196240441127525765 15428068349295082711411081)
  ·
    refine ⟨11571051261971312033558311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15428068349295082711411081 11571051261971312033558311)
    ·
      refine ⟨17356576892956968050337467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11571051261971312033558311 17356576892956968050337467)
      ·
        refine ⟨26034865339435452075506201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17356576892956968050337467 26034865339435452075506201)
        ·
          refine ⟨19526149004576589056629651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26034865339435452075506201 19526149004576589056629651)
          ·
            refine ⟨29289223506864883584944477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19526149004576589056629651 29289223506864883584944477)
            ·
              refine ⟨10983458815074331344354179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29289223506864883584944477 10983458815074331344354179)
              ·
                refine ⟨16475188222611497016531269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10983458815074331344354179 16475188222611497016531269)
                ·
                  refine ⟨3089097791739655690599613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16475188222611497016531269 3089097791739655690599613)
                  ·
                    refine ⟨1158411671902370883974855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089097791739655690599613 1158411671902370883974855)
                    ·
                      rfl

theorem cell22_3383998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_3383998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3383998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3383998 prefixEnd_3383998 := by exact prefixLift 3383998
  have htrace : WordTrace (prefixWord ++ tailWord_3383998) baseStart_3383998 baseEnd_3383998 := by
    simpa [prefixWord, tailWord_3383998, baseEnd_3383998] using wordTrace_append hprefix tailTrace_3383998
  have hstable : (prefixWord ++ tailWord_3383998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3383998).length < 2 ^ (prefixWord ++ tailWord_3383998).sum := by decide
  have hdescent : baseEnd_3383998 < baseStart_3383998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3383998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384028 : List Nat := [2, 2, 5, 1, 1, 2, 1, 8]
def baseStart_3384028 : Nat := 118140960795 + 3384028 * 2 ^ 59
def prefixEnd_3384028 : Nat := 4983230072969 + 3 ^ 40 * 3384028 * 2
def baseEnd_3384028 : Nat := 128713549057273422858307

theorem tailTrace_3384028 : CollatzResearch.WordTrace tailWord_3384028 prefixEnd_3384028 128713549057273422858307 := by
  unfold tailWord_3384028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61712820492125988407440369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82283760656167984543253825 61712820492125988407440369)
  ·
    refine ⟨46284615369094491305580277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61712820492125988407440369 46284615369094491305580277)
    ·
      refine ⟨4339182690852608559898151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46284615369094491305580277 4339182690852608559898151)
      ·
        refine ⟨6508774036278912839847227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339182690852608559898151 6508774036278912839847227)
        ·
          refine ⟨9763161054418369259770841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6508774036278912839847227 9763161054418369259770841)
          ·
            refine ⟨7322370790813776944828131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9763161054418369259770841 7322370790813776944828131)
            ·
              refine ⟨10983556186220665417242197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322370790813776944828131 10983556186220665417242197)
              ·
                refine ⟨128713549057273422858307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10983556186220665417242197 128713549057273422858307)
                ·
                  rfl

theorem cell22_3384028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 8].length) (baseStart_3384028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384028 prefixEnd_3384028 := by exact prefixLift 3384028
  have htrace : WordTrace (prefixWord ++ tailWord_3384028) baseStart_3384028 baseEnd_3384028 := by
    simpa [prefixWord, tailWord_3384028, baseEnd_3384028] using wordTrace_append hprefix tailTrace_3384028
  have hstable : (prefixWord ++ tailWord_3384028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384028).length < 2 ^ (prefixWord ++ tailWord_3384028).sum := by decide
  have hdescent : baseEnd_3384028 < baseStart_3384028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384056 : List Nat := [2, 1, 2, 1, 1, 2, 4, 4, 5]
def baseStart_3384056 : Nat := 118140960795 + 3384056 * 2 ^ 59
def prefixEnd_3384056 : Nat := 4983230072969 + 3 ^ 40 * 3384056 * 2
def baseEnd_3384056 : Nat := 386143842162559355341559

theorem tailTrace_3384056 : CollatzResearch.WordTrace tailWord_3384056 prefixEnd_3384056 386143842162559355341559 := by
  unfold tailWord_3384056
  simp only [CollatzResearch.WordTrace]
  refine ⟨61713331114075268798450011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82284441485433691731266681 61713331114075268798450011)
  ·
    refine ⟨92569996671112903197675017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61713331114075268798450011 92569996671112903197675017)
    ·
      refine ⟨69427497503334677398256263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92569996671112903197675017 69427497503334677398256263)
      ·
        refine ⟨104141246255002016097384395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69427497503334677398256263 104141246255002016097384395)
        ·
          refine ⟨156211869382503024146076593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104141246255002016097384395 156211869382503024146076593)
          ·
            refine ⟨117158902036877268109557445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156211869382503024146076593 117158902036877268109557445)
            ·
              refine ⟨21967294131914487770542021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117158902036877268109557445 21967294131914487770542021)
              ·
                refine ⟨4118867649733966456976629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21967294131914487770542021 4118867649733966456976629)
                ·
                  refine ⟨386143842162559355341559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4118867649733966456976629 386143842162559355341559)
                  ·
                    rfl

theorem cell22_3384056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 4, 5].length) (baseStart_3384056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384056 prefixEnd_3384056 := by exact prefixLift 3384056
  have htrace : WordTrace (prefixWord ++ tailWord_3384056) baseStart_3384056 baseEnd_3384056 := by
    simpa [prefixWord, tailWord_3384056, baseEnd_3384056] using wordTrace_append hprefix tailTrace_3384056
  have hstable : (prefixWord ++ tailWord_3384056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384056).length < 2 ^ (prefixWord ++ tailWord_3384056).sum := by decide
  have hdescent : baseEnd_3384056 < baseStart_3384056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384060 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 3, 3]
def baseStart_3384060 : Nat := 118140960795 + 3384060 * 2 ^ 59
def prefixEnd_3384060 : Nat := 4983230072969 + 3 ^ 40 * 3384060 * 2
def baseEnd_3384060 : Nat := 1158432895769423388924665

theorem tailTrace_3384060 : CollatzResearch.WordTrace tailWord_3384060 prefixEnd_3384060 1158432895769423388924665 := by
  unfold tailWord_3384060
  simp only [CollatzResearch.WordTrace]
  refine ⟨61713404060068023140022817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82284538746757364186697089 61713404060068023140022817)
  ·
    refine ⟨46285053045051017355017113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61713404060068023140022817 46285053045051017355017113)
    ·
      refine ⟨34713789783788263016262835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46285053045051017355017113 34713789783788263016262835)
      ·
        refine ⟨52070684675682394524394253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34713789783788263016262835 52070684675682394524394253)
        ·
          refine ⟨19526506753380897946647845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52070684675682394524394253 19526506753380897946647845)
          ·
            refine ⟨3661220016258918364996471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19526506753380897946647845 3661220016258918364996471)
            ·
              refine ⟨5491830024388377547494707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661220016258918364996471 5491830024388377547494707)
              ·
                refine ⟨8237745036582566321242061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5491830024388377547494707 8237745036582566321242061)
                ·
                  refine ⟨3089154388718462370465773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8237745036582566321242061 3089154388718462370465773)
                  ·
                    refine ⟨1158432895769423388924665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089154388718462370465773 1158432895769423388924665)
                    ·
                      rfl

theorem cell22_3384060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_3384060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384060 prefixEnd_3384060 := by exact prefixLift 3384060
  have htrace : WordTrace (prefixWord ++ tailWord_3384060) baseStart_3384060 baseEnd_3384060 := by
    simpa [prefixWord, tailWord_3384060, baseEnd_3384060] using wordTrace_append hprefix tailTrace_3384060
  have hstable : (prefixWord ++ tailWord_3384060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384060).length < 2 ^ (prefixWord ++ tailWord_3384060).sum := by decide
  have hdescent : baseEnd_3384060 < baseStart_3384060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384073 : List Nat := [1, 2, 1, 1, 3, 2, 6, 1, 5]
def baseStart_3384073 : Nat := 118140960795 + 3384073 * 2 ^ 59
def prefixEnd_3384073 : Nat := 4983230072969 + 3 ^ 40 * 3384073 * 2
def baseEnd_3384073 : Nat := 386145781978365229449875

theorem tailTrace_3384073 : CollatzResearch.WordTrace tailWord_3384073 prefixEnd_3384073 386145781978365229449875 := by
  unfold tailWord_3384073
  simp only [CollatzResearch.WordTrace]
  refine ⟨123427282269088949500268873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82284854846059299666845915 123427282269088949500268873)
  ·
    refine ⟨92570461701816712125201655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123427282269088949500268873 92570461701816712125201655)
    ·
      refine ⟨138855692552725068187802483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92570461701816712125201655 138855692552725068187802483)
      ·
        refine ⟨208283538829087602281703725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138855692552725068187802483 208283538829087602281703725)
        ·
          refine ⟨78106327060907850855638897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208283538829087602281703725 78106327060907850855638897)
          ·
            refine ⟨58579745295680888141729173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78106327060907850855638897 58579745295680888141729173)
            ·
              refine ⟨2745925560735041631643555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58579745295680888141729173 2745925560735041631643555)
              ·
                refine ⟨4118888341102562447465333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2745925560735041631643555 4118888341102562447465333)
                ·
                  refine ⟨386145781978365229449875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4118888341102562447465333 386145781978365229449875)
                  ·
                    rfl

theorem cell22_3384073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 5].length) (baseStart_3384073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384073 prefixEnd_3384073 := by exact prefixLift 3384073
  have htrace : WordTrace (prefixWord ++ tailWord_3384073) baseStart_3384073 baseEnd_3384073 := by
    simpa [prefixWord, tailWord_3384073, baseEnd_3384073] using wordTrace_append hprefix tailTrace_3384073
  have hstable : (prefixWord ++ tailWord_3384073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384073).length < 2 ^ (prefixWord ++ tailWord_3384073).sum := by decide
  have hdescent : baseEnd_3384073 < baseStart_3384073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384131 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 6]
def baseStart_3384131 : Nat := 118140960795 + 3384131 * 2 ^ 59
def prefixEnd_3384131 : Nat := 4983230072969 + 3 ^ 40 * 3384131 * 2
def baseEnd_3384131 : Nat := 1158457200520402870399447

theorem tailTrace_3384131 : CollatzResearch.WordTrace tailWord_3384131 prefixEnd_3384131 1158457200520402870399447 := by
  unfold tailWord_3384131
  simp only [CollatzResearch.WordTrace]
  refine ⟨123429397702878825405880247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82286265135252550270586831 123429397702878825405880247)
  ·
    refine ⟨185144096554318238108820371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123429397702878825405880247 185144096554318238108820371)
    ·
      refine ⟨277716144831477357163230557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185144096554318238108820371 277716144831477357163230557)
      ·
        refine ⟨104143554311804008936211459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277716144831477357163230557 104143554311804008936211459)
        ·
          refine ⟨156215331467706013404317189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104143554311804008936211459 156215331467706013404317189)
          ·
            refine ⟨29290374650194877513309473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156215331467706013404317189 29290374650194877513309473)
            ·
              refine ⟨21967780987646158134982105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29290374650194877513309473 21967780987646158134982105)
              ·
                refine ⟨16475835740734618601236579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21967780987646158134982105 16475835740734618601236579)
                ·
                  refine ⟨24713753611101927901854869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16475835740734618601236579 24713753611101927901854869)
                  ·
                    refine ⟨1158457200520402870399447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24713753611101927901854869 1158457200520402870399447)
                    ·
                      rfl

theorem cell22_3384131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 6].length) (baseStart_3384131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384131 prefixEnd_3384131 := by exact prefixLift 3384131
  have htrace : WordTrace (prefixWord ++ tailWord_3384131) baseStart_3384131 baseEnd_3384131 := by
    simpa [prefixWord, tailWord_3384131, baseEnd_3384131] using wordTrace_append hprefix tailTrace_3384131
  have hstable : (prefixWord ++ tailWord_3384131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384131).length < 2 ^ (prefixWord ++ tailWord_3384131).sum := by decide
  have hdescent : baseEnd_3384131 < baseStart_3384131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384167 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 2, 3]
def baseStart_3384167 : Nat := 118140960795 + 3384167 * 2 ^ 59
def prefixEnd_3384167 : Nat := 4983230072969 + 3 ^ 40 * 3384167 * 2
def baseEnd_3384167 : Nat := 1158469524056110776499337

theorem tailTrace_3384167 : CollatzResearch.WordTrace tailWord_3384167 prefixEnd_3384167 1158469524056110776499337 := by
  unfold tailWord_3384167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123430710730748403554190755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82287140487165602369460503 123430710730748403554190755)
  ·
    refine ⟨185146066096122605331286133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123430710730748403554190755 185146066096122605331286133)
    ·
      refine ⟨17357443696511494249808075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185146066096122605331286133 17357443696511494249808075)
      ·
        refine ⟨26036165544767241374712113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17357443696511494249808075 26036165544767241374712113)
        ·
          refine ⟨19527124158575431031034085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26036165544767241374712113 19527124158575431031034085)
          ·
            refine ⟨3661335779732893318318891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19527124158575431031034085 3661335779732893318318891)
            ·
              refine ⟨5492003669599339977478337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661335779732893318318891 5492003669599339977478337)
              ·
                refine ⟨4119002752199504983108753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492003669599339977478337 4119002752199504983108753)
                ·
                  refine ⟨3089252064149628737331565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4119002752199504983108753 3089252064149628737331565)
                  ·
                    refine ⟨1158469524056110776499337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089252064149628737331565 1158469524056110776499337)
                    ·
                      rfl

theorem cell22_3384167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_3384167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384167 prefixEnd_3384167 := by exact prefixLift 3384167
  have htrace : WordTrace (prefixWord ++ tailWord_3384167) baseStart_3384167 baseEnd_3384167 := by
    simpa [prefixWord, tailWord_3384167, baseEnd_3384167] using wordTrace_append hprefix tailTrace_3384167
  have hstable : (prefixWord ++ tailWord_3384167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384167).length < 2 ^ (prefixWord ++ tailWord_3384167).sum := by decide
  have hdescent : baseEnd_3384167 < baseStart_3384167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384176 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_3384176 : Nat := 118140960795 + 3384176 * 2 ^ 59
def prefixEnd_3384176 : Nat := 4983230072969 + 3 ^ 40 * 3384176 * 2
def baseEnd_3384176 : Nat := 1158472604940037753024309

theorem tailTrace_3384176 : CollatzResearch.WordTrace tailWord_3384176 prefixEnd_3384176 1158472604940037753024309 := by
  unfold tailWord_3384176
  simp only [CollatzResearch.WordTrace]
  refine ⟨61715519493857899045634191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82287359325143865394178921 61715519493857899045634191)
  ·
    refine ⟨92573279240786848568451287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61715519493857899045634191 92573279240786848568451287)
    ·
      refine ⟨138859918861180272852676931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92573279240786848568451287 138859918861180272852676931)
      ·
        refine ⟨208289878291770409279015397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138859918861180272852676931 208289878291770409279015397)
        ·
          refine ⟨39054352179706951739815387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208289878291770409279015397 39054352179706951739815387)
          ·
            refine ⟨58581528269560427609723081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39054352179706951739815387 58581528269560427609723081)
            ·
              refine ⟨43936146202170320707292311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58581528269560427609723081 43936146202170320707292311)
              ·
                refine ⟨65904219303255481060938467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43936146202170320707292311 65904219303255481060938467)
                ·
                  refine ⟨98856328954883221591407701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65904219303255481060938467 98856328954883221591407701)
                  ·
                    refine ⟨1158472604940037753024309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98856328954883221591407701 1158472604940037753024309)
                    ·
                      rfl

theorem cell22_3384176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_3384176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384176 prefixEnd_3384176 := by exact prefixLift 3384176
  have htrace : WordTrace (prefixWord ++ tailWord_3384176) baseStart_3384176 baseEnd_3384176 := by
    simpa [prefixWord, tailWord_3384176, baseEnd_3384176] using wordTrace_append hprefix tailTrace_3384176
  have hstable : (prefixWord ++ tailWord_3384176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384176).length < 2 ^ (prefixWord ++ tailWord_3384176).sum := by decide
  have hdescent : baseEnd_3384176 < baseStart_3384176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384287 : List Nat := [1, 1, 2, 3, 5, 1, 1, 4, 4]
def baseStart_3384287 : Nat := 118140960795 + 3384287 * 2 ^ 59
def prefixEnd_3384287 : Nat := 4983230072969 + 3 ^ 40 * 3384287 * 2
def baseEnd_3384287 : Nat := 386170200836156821166323

theorem tailTrace_3384287 : CollatzResearch.WordTrace tailWord_3384287 prefixEnd_3384287 386170200836156821166323 := by
  unfold tailWord_3384287
  simp only [CollatzResearch.WordTrace]
  refine ⟨123435087490313664048559115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82290058326875776032372743 123435087490313664048559115)
  ·
    refine ⟨185152631235470496072838673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123435087490313664048559115 185152631235470496072838673)
    ·
      refine ⟨138864473426602872054629005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185152631235470496072838673 138864473426602872054629005)
      ·
        refine ⟨52074177534976077020485877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138864473426602872054629005 52074177534976077020485877)
        ·
          refine ⟨4881954143904007220670551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52074177534976077020485877 4881954143904007220670551)
          ·
            refine ⟨7322931215856010831005827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881954143904007220670551 7322931215856010831005827)
            ·
              refine ⟨10984396823784016246508741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7322931215856010831005827 10984396823784016246508741)
              ·
                refine ⟨2059574404459503046220389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10984396823784016246508741 2059574404459503046220389)
                ·
                  refine ⟨386170200836156821166323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059574404459503046220389 386170200836156821166323)
                  ·
                    rfl

theorem cell22_3384287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 4, 4].length) (baseStart_3384287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384287 prefixEnd_3384287 := by exact prefixLift 3384287
  have htrace : WordTrace (prefixWord ++ tailWord_3384287) baseStart_3384287 baseEnd_3384287 := by
    simpa [prefixWord, tailWord_3384287, baseEnd_3384287] using wordTrace_append hprefix tailTrace_3384287
  have hstable : (prefixWord ++ tailWord_3384287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384287).length < 2 ^ (prefixWord ++ tailWord_3384287).sum := by decide
  have hdescent : baseEnd_3384287 < baseStart_3384287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384302 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3384302 : Nat := 118140960795 + 3384302 * 2 ^ 59
def prefixEnd_3384302 : Nat := 4983230072969 + 3 ^ 40 * 3384302 * 2
def baseEnd_3384302 : Nat := 1158515737315015424373923

theorem tailTrace_3384302 : CollatzResearch.WordTrace tailWord_3384302 prefixEnd_3384302 1158515737315015424373923 := by
  unfold tailWord_3384302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15429454323157415201294395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82290423056839547740236773 15429454323157415201294395)
  ·
    refine ⟨23144181484736122801941593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15429454323157415201294395 23144181484736122801941593)
    ·
      refine ⟨17358136113552092101456195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23144181484736122801941593 17358136113552092101456195)
      ·
        refine ⟨26037204170328138152184293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358136113552092101456195 26037204170328138152184293)
        ·
          refine ⟨4881975781936525903534555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26037204170328138152184293 4881975781936525903534555)
          ·
            refine ⟨7322963672904788855301833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4881975781936525903534555 7322963672904788855301833)
            ·
              refine ⟨5492222754678591641476375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7322963672904788855301833 5492222754678591641476375)
              ·
                refine ⟨8238334132017887462214563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492222754678591641476375 8238334132017887462214563)
                ·
                  refine ⟨12357501198026831193321845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238334132017887462214563 12357501198026831193321845)
                  ·
                    refine ⟨1158515737315015424373923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12357501198026831193321845 1158515737315015424373923)
                    ·
                      rfl

theorem cell22_3384302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3384302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384302 prefixEnd_3384302 := by exact prefixLift 3384302
  have htrace : WordTrace (prefixWord ++ tailWord_3384302) baseStart_3384302 baseEnd_3384302 := by
    simpa [prefixWord, tailWord_3384302, baseEnd_3384302] using wordTrace_append hprefix tailTrace_3384302
  have hstable : (prefixWord ++ tailWord_3384302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384302).length < 2 ^ (prefixWord ++ tailWord_3384302).sum := by decide
  have hdescent : baseEnd_3384302 < baseStart_3384302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384381 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_3384381 : Nat := 118140960795 + 3384381 * 2 ^ 59
def prefixEnd_3384381 : Nat := 4983230072969 + 3 ^ 40 * 3384381 * 2
def baseEnd_3384381 : Nat := 1158542780629485551648681

theorem tailTrace_3384381 : CollatzResearch.WordTrace tailWord_3384381 prefixEnd_3384381 1158542780629485551648681 := by
  unfold tailWord_3384381
  simp only [CollatzResearch.WordTrace]
  refine ⟨123438515951973118102480997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82292343967982078734987331 123438515951973118102480997)
  ·
    refine ⟨23144721740994959644215187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123438515951973118102480997 23144721740994959644215187)
    ·
      refine ⟨34717082611492439466322781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23144721740994959644215187 34717082611492439466322781)
      ·
        refine ⟨13018905979309664799871043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34717082611492439466322781 13018905979309664799871043)
        ·
          refine ⟨19528358968964497199806565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13018905979309664799871043 19528358968964497199806565)
          ·
            refine ⟨3661567306680843224963731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19528358968964497199806565 3661567306680843224963731)
            ·
              refine ⟨5492350960021264837445597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3661567306680843224963731 5492350960021264837445597)
              ·
                refine ⟨2059631610007974314042099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5492350960021264837445597 2059631610007974314042099)
                ·
                  refine ⟨3089447415011961471063149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059631610007974314042099 3089447415011961471063149)
                  ·
                    refine ⟨1158542780629485551648681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089447415011961471063149 1158542780629485551648681)
                    ·
                      rfl

theorem cell22_3384381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_3384381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384381 prefixEnd_3384381 := by exact prefixLift 3384381
  have htrace : WordTrace (prefixWord ++ tailWord_3384381) baseStart_3384381 baseEnd_3384381 := by
    simpa [prefixWord, tailWord_3384381, baseEnd_3384381] using wordTrace_append hprefix tailTrace_3384381
  have hstable : (prefixWord ++ tailWord_3384381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384381).length < 2 ^ (prefixWord ++ tailWord_3384381).sum := by decide
  have hdescent : baseEnd_3384381 < baseStart_3384381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384420 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 1, 5]
def baseStart_3384420 : Nat := 118140960795 + 3384420 * 2 ^ 59
def prefixEnd_3384420 : Nat := 4983230072969 + 3 ^ 40 * 3384420 * 2
def baseEnd_3384420 : Nat := 1158556131126502449923561

theorem tailTrace_3384420 : CollatzResearch.WordTrace tailWord_3384420 prefixEnd_3384420 1158556131126502449923561 := by
  unfold tailWord_3384420
  simp only [CollatzResearch.WordTrace]
  refine ⟨61719969199415913881575357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82293292265887885175433809 61719969199415913881575357)
  ·
    refine ⟨23144988449780967705590759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61719969199415913881575357 23144988449780967705590759)
    ·
      refine ⟨34717482674671451558386139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23144988449780967705590759 34717482674671451558386139)
      ·
        refine ⟨52076224012007177337579209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34717482674671451558386139 52076224012007177337579209)
        ·
          refine ⟨39057168009005383003184407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52076224012007177337579209 39057168009005383003184407)
          ·
            refine ⟨58585752013508074504776611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39057168009005383003184407 58585752013508074504776611)
            ·
              refine ⟨87878628020262111757164917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58585752013508074504776611 87878628020262111757164917)
              ·
                refine ⟨8238621376899572977234211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87878628020262111757164917 8238621376899572977234211)
                ·
                  refine ⟨12357932065349359465851317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8238621376899572977234211 12357932065349359465851317)
                  ·
                    refine ⟨1158556131126502449923561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12357932065349359465851317 1158556131126502449923561)
                    ·
                      rfl

theorem cell22_3384420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_3384420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384420 prefixEnd_3384420 := by exact prefixLift 3384420
  have htrace : WordTrace (prefixWord ++ tailWord_3384420) baseStart_3384420 baseEnd_3384420 := by
    simpa [prefixWord, tailWord_3384420, baseEnd_3384420] using wordTrace_append hprefix tailTrace_3384420
  have hstable : (prefixWord ++ tailWord_3384420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384420).length < 2 ^ (prefixWord ++ tailWord_3384420).sum := by decide
  have hdescent : baseEnd_3384420 < baseStart_3384420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384424 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 3, 4]
def baseStart_3384424 : Nat := 118140960795 + 3384424 * 2 ^ 59
def prefixEnd_3384424 : Nat := 4983230072969 + 3 ^ 40 * 3384424 * 2
def baseEnd_3384424 : Nat := 1158557500408247772823549

theorem tailTrace_3384424 : CollatzResearch.WordTrace tailWord_3384424 prefixEnd_3384424 1158557500408247772823549 := by
  unfold tailWord_3384424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61720042145408668223148163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82293389527211557630864217 61720042145408668223148163)
  ·
    refine ⟨92580063218113002334722245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61720042145408668223148163 92580063218113002334722245)
    ·
      refine ⟨17358761853396187937760421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92580063218113002334722245 17358761853396187937760421)
      ·
        refine ⟨3254767847511785238330079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17358761853396187937760421 3254767847511785238330079)
        ·
          refine ⟨4882151771267677857495119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254767847511785238330079 4882151771267677857495119)
          ·
            refine ⟨7323227656901516786242679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882151771267677857495119 7323227656901516786242679)
            ·
              refine ⟨10984841485352275179364019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323227656901516786242679 10984841485352275179364019)
              ·
                refine ⟨16477262228028412769046029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10984841485352275179364019 16477262228028412769046029)
                ·
                  refine ⟨6178973335510654788392261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16477262228028412769046029 6178973335510654788392261)
                  ·
                    refine ⟨1158557500408247772823549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6178973335510654788392261 1158557500408247772823549)
                    ·
                      rfl

theorem cell22_3384424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_3384424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384424 prefixEnd_3384424 := by exact prefixLift 3384424
  have htrace : WordTrace (prefixWord ++ tailWord_3384424) baseStart_3384424 baseEnd_3384424 := by
    simpa [prefixWord, tailWord_3384424, baseEnd_3384424] using wordTrace_append hprefix tailTrace_3384424
  have hstable : (prefixWord ++ tailWord_3384424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384424).length < 2 ^ (prefixWord ++ tailWord_3384424).sum := by decide
  have hdescent : baseEnd_3384424 < baseStart_3384424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384452 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 2, 4]
def baseStart_3384452 : Nat := 118140960795 + 3384452 * 2 ^ 59
def prefixEnd_3384452 : Nat := 4983230072969 + 3 ^ 40 * 3384452 * 2
def baseEnd_3384452 : Nat := 1158567085380465033123463

theorem tailTrace_3384452 : CollatzResearch.WordTrace tailWord_3384452 prefixEnd_3384452 1158567085380465033123463 := by
  unfold tailWord_3384452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61720552767357948614157805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82294070356477264818877073 61720552767357948614157805)
  ·
    refine ⟨23145207287759230730309177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61720552767357948614157805 23145207287759230730309177)
    ·
      refine ⟨17358905465819423047731883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23145207287759230730309177 17358905465819423047731883)
      ·
        refine ⟨26038358198729134571597825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17358905465819423047731883 26038358198729134571597825)
        ·
          refine ⟨19528768649046850928698369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26038358198729134571597825 19528768649046850928698369)
          ·
            refine ⟨14646576486785138196523777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19528768649046850928698369 14646576486785138196523777)
            ·
              refine ⟨10984932365088853647392833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14646576486785138196523777 10984932365088853647392833)
              ·
                refine ⟨8238699273816640235544625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10984932365088853647392833 8238699273816640235544625)
                ·
                  refine ⟨6179024455362480176658469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8238699273816640235544625 6179024455362480176658469)
                  ·
                    refine ⟨1158567085380465033123463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179024455362480176658469 1158567085380465033123463)
                    ·
                      rfl

theorem cell22_3384452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_3384452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384452 prefixEnd_3384452 := by exact prefixLift 3384452
  have htrace : WordTrace (prefixWord ++ tailWord_3384452) baseStart_3384452 baseEnd_3384452 := by
    simpa [prefixWord, tailWord_3384452, baseEnd_3384452] using wordTrace_append hprefix tailTrace_3384452
  have hstable : (prefixWord ++ tailWord_3384452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384452).length < 2 ^ (prefixWord ++ tailWord_3384452).sum := by decide
  have hdescent : baseEnd_3384452 < baseStart_3384452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384480 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_3384480 : Nat := 118140960795 + 3384480 * 2 ^ 59
def prefixEnd_3384480 : Nat := 4983230072969 + 3 ^ 40 * 3384480 * 2
def baseEnd_3384480 : Nat := 1158576670352682293423377

theorem tailTrace_3384480 : CollatzResearch.WordTrace tailWord_3384480 prefixEnd_3384480 1158576670352682293423377 := by
  unfold tailWord_3384480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61721063389307229005167447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82294751185742972006889929 61721063389307229005167447)
  ·
    refine ⟨92581595083960843507751171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61721063389307229005167447 92581595083960843507751171)
    ·
      refine ⟨138872392625941265261626757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92581595083960843507751171 138872392625941265261626757)
      ·
        refine ⟨26038573617363987236555017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138872392625941265261626757 26038573617363987236555017)
        ·
          refine ⟨19528930213022990427416263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26038573617363987236555017 19528930213022990427416263)
          ·
            refine ⟨29293395319534485641124395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19528930213022990427416263 29293395319534485641124395)
            ·
              refine ⟨43940092979301728461686593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29293395319534485641124395 43940092979301728461686593)
              ·
                refine ⟨32955069734476296346264945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43940092979301728461686593 32955069734476296346264945)
                ·
                  refine ⟨24716302300857222259698709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32955069734476296346264945 24716302300857222259698709)
                  ·
                    refine ⟨1158576670352682293423377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24716302300857222259698709 1158576670352682293423377)
                    ·
                      rfl

theorem cell22_3384480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_3384480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384480 prefixEnd_3384480 := by exact prefixLift 3384480
  have htrace : WordTrace (prefixWord ++ tailWord_3384480) baseStart_3384480 baseEnd_3384480 := by
    simpa [prefixWord, tailWord_3384480, baseEnd_3384480] using wordTrace_append hprefix tailTrace_3384480
  have hstable : (prefixWord ++ tailWord_3384480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384480).length < 2 ^ (prefixWord ++ tailWord_3384480).sum := by decide
  have hdescent : baseEnd_3384480 < baseStart_3384480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384499 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 1, 3]
def baseStart_3384499 : Nat := 118140960795 + 3384499 * 2 ^ 59
def prefixEnd_3384499 : Nat := 4983230072969 + 3 ^ 40 * 3384499 * 2
def baseEnd_3384499 : Nat := 1158583174440972577198319

theorem tailTrace_3384499 : CollatzResearch.WordTrace tailWord_3384499 prefixEnd_3384499 1158583174440972577198319 := by
  unfold tailWord_3384499
  simp only [CollatzResearch.WordTrace]
  refine ⟨123442819765545624255276551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82295213177030416170184367 123442819765545624255276551)
  ·
    refine ⟨185164229648318436382914827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123442819765545624255276551 185164229648318436382914827)
    ·
      refine ⟨277746344472477654574372241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185164229648318436382914827 277746344472477654574372241)
      ·
        refine ⟨208309758354358240930779181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277746344472477654574372241 208309758354358240930779181)
        ·
          refine ⟨78116159382884340349042193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208309758354358240930779181 78116159382884340349042193)
          ·
            refine ⟨58587119537163255261781645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78116159382884340349042193 58587119537163255261781645)
            ·
              refine ⟨21970169826436220723168117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58587119537163255261781645 21970169826436220723168117)
              ·
                refine ⟨2059703421228395692797011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21970169826436220723168117 2059703421228395692797011)
                ·
                  refine ⟨3089555131842593539195517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2059703421228395692797011 3089555131842593539195517)
                  ·
                    refine ⟨1158583174440972577198319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089555131842593539195517 1158583174440972577198319)
                    ·
                      rfl

theorem cell22_3384499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 1, 3].length) (baseStart_3384499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384499 prefixEnd_3384499 := by exact prefixLift 3384499
  have htrace : WordTrace (prefixWord ++ tailWord_3384499) baseStart_3384499 baseEnd_3384499 := by
    simpa [prefixWord, tailWord_3384499, baseEnd_3384499] using wordTrace_append hprefix tailTrace_3384499
  have hstable : (prefixWord ++ tailWord_3384499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384499).length < 2 ^ (prefixWord ++ tailWord_3384499).sum := by decide
  have hdescent : baseEnd_3384499 < baseStart_3384499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384512 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 7]
def baseStart_3384512 : Nat := 118140960795 + 3384512 * 2 ^ 59
def prefixEnd_3384512 : Nat := 4983230072969 + 3 ^ 40 * 3384512 * 2
def baseEnd_3384512 : Nat := 386195874868881625541093

theorem tailTrace_3384512 : CollatzResearch.WordTrace tailWord_3384512 prefixEnd_3384512 386195874868881625541093 := by
  unfold tailWord_3384512
  simp only [CollatzResearch.WordTrace]
  refine ⟨61721646957249263737749895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82295529276332351650333193 61721646957249263737749895)
  ·
    refine ⟨92582470435873895606624843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61721646957249263737749895 92582470435873895606624843)
    ·
      refine ⟨138873705653810843409937265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92582470435873895606624843 138873705653810843409937265)
      ·
        refine ⟨104155279240358132557452949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138873705653810843409937265 104155279240358132557452949)
        ·
          refine ⟨4882278714391787463630607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104155279240358132557452949 4882278714391787463630607)
          ·
            refine ⟨7323418071587681195445911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882278714391787463630607 7323418071587681195445911)
            ·
              refine ⟨10985127107381521793168867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7323418071587681195445911 10985127107381521793168867)
              ·
                refine ⟨16477690661072282689753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10985127107381521793168867 16477690661072282689753301)
                ·
                  refine ⟨386195874868881625541093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16477690661072282689753301 386195874868881625541093)
                  ·
                    rfl

theorem cell22_3384512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 7].length) (baseStart_3384512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384512 prefixEnd_3384512 := by exact prefixLift 3384512
  have htrace : WordTrace (prefixWord ++ tailWord_3384512) baseStart_3384512 baseEnd_3384512 := by
    simpa [prefixWord, tailWord_3384512, baseEnd_3384512] using wordTrace_append hprefix tailTrace_3384512
  have hstable : (prefixWord ++ tailWord_3384512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384512).length < 2 ^ (prefixWord ++ tailWord_3384512).sum := by decide
  have hdescent : baseEnd_3384512 < baseStart_3384512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384516 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 3, 3]
def baseStart_3384516 : Nat := 118140960795 + 3384516 * 2 ^ 59
def prefixEnd_3384516 : Nat := 4983230072969 + 3 ^ 40 * 3384516 * 2
def baseEnd_3384516 : Nat := 1158588993888390199523267

theorem tailTrace_3384516 : CollatzResearch.WordTrace tailWord_3384516 prefixEnd_3384516 1158588993888390199523267 := by
  unfold tailWord_3384516
  simp only [CollatzResearch.WordTrace]
  refine ⟨61721719903242018079322701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82295626537656024105763601 61721719903242018079322701)
  ·
    refine ⟨23145644963715756779746013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61721719903242018079322701 23145644963715756779746013)
    ·
      refine ⟨8679616861393408792404755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23145644963715756779746013 8679616861393408792404755)
      ·
        refine ⟨13019425292090113188607133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8679616861393408792404755 13019425292090113188607133)
        ·
          refine ⟨4882284484533792445727675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13019425292090113188607133 4882284484533792445727675)
          ·
            refine ⟨7323426726800688668591513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882284484533792445727675 7323426726800688668591513)
            ·
              refine ⟨5492570045100516501443635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7323426726800688668591513 5492570045100516501443635)
              ·
                refine ⟨8238855067650774752165453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492570045100516501443635 8238855067650774752165453)
                ·
                  refine ⟨3089570650369040532062045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8238855067650774752165453 3089570650369040532062045)
                  ·
                    refine ⟨1158588993888390199523267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089570650369040532062045 1158588993888390199523267)
                    ·
                      rfl

theorem cell22_3384516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_3384516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384516 prefixEnd_3384516 := by exact prefixLift 3384516
  have htrace : WordTrace (prefixWord ++ tailWord_3384516) baseStart_3384516 baseEnd_3384516 := by
    simpa [prefixWord, tailWord_3384516, baseEnd_3384516] using wordTrace_append hprefix tailTrace_3384516
  have hstable : (prefixWord ++ tailWord_3384516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384516).length < 2 ^ (prefixWord ++ tailWord_3384516).sum := by decide
  have hdescent : baseEnd_3384516 < baseStart_3384516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384574 : List Nat := [4, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_3384574 : Nat := 118140960795 + 3384574 * 2 ^ 59
def prefixEnd_3384574 : Nat := 4983230072969 + 3 ^ 40 * 3384574 * 2
def baseEnd_3384574 : Nat := 386202949491232460524363

theorem tailTrace_3384574 : CollatzResearch.WordTrace tailWord_3384574 prefixEnd_3384574 386202949491232460524363 := by
  unfold tailWord_3384574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15430694405034239008032097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82297036826849274709504517 15430694405034239008032097)
  ·
    refine ⟨11573020803775679256024073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15430694405034239008032097 11573020803775679256024073)
    ·
      refine ⟨8679765602831759442018055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11573020803775679256024073 8679765602831759442018055)
      ·
        refine ⟨13019648404247639163027083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8679765602831759442018055 13019648404247639163027083)
        ·
          refine ⟨19529472606371458744540625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13019648404247639163027083 19529472606371458744540625)
          ·
            refine ⟨14647104454778594058405469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19529472606371458744540625 14647104454778594058405469)
            ·
              refine ⟨5492664170541972771902051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14647104454778594058405469 5492664170541972771902051)
              ·
                refine ⟨8238996255812959157853077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5492664170541972771902051 8238996255812959157853077)
                ·
                  refine ⟨386202949491232460524363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8238996255812959157853077 386202949491232460524363)
                  ·
                    rfl

theorem cell22_3384574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_3384574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384574 prefixEnd_3384574 := by exact prefixLift 3384574
  have htrace : WordTrace (prefixWord ++ tailWord_3384574) baseStart_3384574 baseEnd_3384574 := by
    simpa [prefixWord, tailWord_3384574, baseEnd_3384574] using wordTrace_append hprefix tailTrace_3384574
  have hstable : (prefixWord ++ tailWord_3384574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384574).length < 2 ^ (prefixWord ++ tailWord_3384574).sum := by decide
  have hdescent : baseEnd_3384574 < baseStart_3384574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384602 : List Nat := [3, 1, 1, 3, 3, 1, 2, 8]
def baseStart_3384602 : Nat := 118140960795 + 3384602 * 2 ^ 59
def prefixEnd_3384602 : Nat := 4983230072969 + 3 ^ 40 * 3384602 * 2
def baseEnd_3384602 : Nat := 128735381493990515763667

theorem tailTrace_3384602 : CollatzResearch.WordTrace tailWord_3384602 prefixEnd_3384602 128735381493990515763667 := by
  unfold tailWord_3384602
  simp only [CollatzResearch.WordTrace]
  refine ⟨30861644121043118211569015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82297717656114981897517373 30861644121043118211569015)
  ·
    refine ⟨46292466181564677317353523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30861644121043118211569015 46292466181564677317353523)
    ·
      refine ⟨69438699272347015976030285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46292466181564677317353523 69438699272347015976030285)
      ·
        refine ⟨26039512227130130991011357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69438699272347015976030285 26039512227130130991011357)
        ·
          refine ⟨9764817085173799121629259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26039512227130130991011357 9764817085173799121629259)
          ·
            refine ⟨14647225627760698682443889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764817085173799121629259 14647225627760698682443889)
            ·
              refine ⟨10985419220820524011832917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14647225627760698682443889 10985419220820524011832917)
              ·
                refine ⟨128735381493990515763667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10985419220820524011832917 128735381493990515763667)
                ·
                  rfl

theorem cell22_3384602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_3384602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384602 prefixEnd_3384602 := by exact prefixLift 3384602
  have htrace : WordTrace (prefixWord ++ tailWord_3384602) baseStart_3384602 baseEnd_3384602 := by
    simpa [prefixWord, tailWord_3384602, baseEnd_3384602] using wordTrace_append hprefix tailTrace_3384602
  have hstable : (prefixWord ++ tailWord_3384602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384602).length < 2 ^ (prefixWord ++ tailWord_3384602).sum := by decide
  have hdescent : baseEnd_3384602 < baseStart_3384602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384621 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3384621 : Nat := 118140960795 + 3384621 * 2 ^ 59
def prefixEnd_3384621 : Nat := 4983230072969 + 3 ^ 40 * 3384621 * 2
def baseEnd_3384621 : Nat := 1158624937534204925647945

theorem tailTrace_3384621 : CollatzResearch.WordTrace tailWord_3384621 prefixEnd_3384621 1158624937534204925647945 := by
  unfold tailWord_3384621
  simp only [CollatzResearch.WordTrace]
  refine ⟨123447269471103639091217717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82298179647402426060811811 123447269471103639091217717)
  ·
    refine ⟨11573181512915966164801661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123447269471103639091217717 11573181512915966164801661)
    ·
      refine ⟨4339943067343487311800623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11573181512915966164801661 4339943067343487311800623)
      ·
        refine ⟨6509914601015230967700935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339943067343487311800623 6509914601015230967700935)
        ·
          refine ⟨9764871901522846451551403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509914601015230967700935 9764871901522846451551403)
          ·
            refine ⟨14647307852284269677327105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764871901522846451551403 14647307852284269677327105)
            ·
              refine ⟨10985480889213202257995329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14647307852284269677327105 10985480889213202257995329)
              ·
                refine ⟨8239110666909901693496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985480889213202257995329 8239110666909901693496497)
                ·
                  refine ⟨6179333000182426270122373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239110666909901693496497 6179333000182426270122373)
                  ·
                    refine ⟨1158624937534204925647945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179333000182426270122373 1158624937534204925647945)
                    ·
                      rfl

theorem cell22_3384621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3384621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384621 prefixEnd_3384621 := by exact prefixLift 3384621
  have htrace : WordTrace (prefixWord ++ tailWord_3384621) baseStart_3384621 baseEnd_3384621 := by
    simpa [prefixWord, tailWord_3384621, baseEnd_3384621] using wordTrace_append hprefix tailTrace_3384621
  have hstable : (prefixWord ++ tailWord_3384621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384621).length < 2 ^ (prefixWord ++ tailWord_3384621).sum := by decide
  have hdescent : baseEnd_3384621 < baseStart_3384621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384634 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 3, 3]
def baseStart_3384634 : Nat := 118140960795 + 3384634 * 2 ^ 59
def prefixEnd_3384634 : Nat := 4983230072969 + 3 ^ 40 * 3384634 * 2
def baseEnd_3384634 : Nat := 1158629387699877225072905

theorem tailTrace_3384634 : CollatzResearch.WordTrace tailWord_3384634 prefixEnd_3384634 1158629387699877225072905 := by
  unfold tailWord_3384634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30861935905014135577860239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82298495746704361540960637 30861935905014135577860239)
  ·
    refine ⟨46292903857521203366790359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30861935905014135577860239 46292903857521203366790359)
    ·
      refine ⟨69439355786281805050185539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46292903857521203366790359 69439355786281805050185539)
      ·
        refine ⟨104159033679422707575278309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69439355786281805050185539 104159033679422707575278309)
        ·
          refine ⟨19529818814891757670364683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104159033679422707575278309 19529818814891757670364683)
          ·
            refine ⟨29294728222337636505547025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19529818814891757670364683 29294728222337636505547025)
            ·
              refine ⟨21971046166753227379160269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29294728222337636505547025 21971046166753227379160269)
              ·
                refine ⟨8239142312532460267185101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21971046166753227379160269 8239142312532460267185101)
                ·
                  refine ⟨3089678367199672600194413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8239142312532460267185101 3089678367199672600194413)
                  ·
                    refine ⟨1158629387699877225072905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3089678367199672600194413 1158629387699877225072905)
                    ·
                      rfl

theorem cell22_3384634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_3384634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384634 prefixEnd_3384634 := by exact prefixLift 3384634
  have htrace : WordTrace (prefixWord ++ tailWord_3384634) baseStart_3384634 baseEnd_3384634 := by
    simpa [prefixWord, tailWord_3384634, baseEnd_3384634] using wordTrace_append hprefix tailTrace_3384634
  have hstable : (prefixWord ++ tailWord_3384634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384634).length < 2 ^ (prefixWord ++ tailWord_3384634).sum := by decide
  have hdescent : baseEnd_3384634 < baseStart_3384634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384653 : List Nat := [1, 6, 1, 3, 1, 1, 3, 6]
def baseStart_3384653 : Nat := 118140960795 + 3384653 * 2 ^ 59
def prefixEnd_3384653 : Nat := 4983230072969 + 3 ^ 40 * 3384653 * 2
def baseEnd_3384653 : Nat := 128737321309796389871983

theorem tailTrace_3384653 : CollatzResearch.WordTrace tailWord_3384653 prefixEnd_3384653 128737321309796389871983 := by
  unfold tailWord_3384653
  simp only [CollatzResearch.WordTrace]
  refine ⟨123448436606987708556382613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82298957737991805704255075 123448436606987708556382613)
  ·
    refine ⟨5786645465952548838580435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123448436606987708556382613 5786645465952548838580435)
    ·
      refine ⟨8679968198928823257870653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5786645465952548838580435 8679968198928823257870653)
      ·
        refine ⟨3254988074598308721701495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8679968198928823257870653 3254988074598308721701495)
        ·
          refine ⟨4882482111897463082552243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3254988074598308721701495 4882482111897463082552243)
          ·
            refine ⟨7323723167846194623828365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4882482111897463082552243 7323723167846194623828365)
            ·
              refine ⟨2746396187942322983935637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7323723167846194623828365 2746396187942322983935637)
              ·
                refine ⟨128737321309796389871983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2746396187942322983935637 128737321309796389871983)
                ·
                  rfl

theorem cell22_3384653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 6].length) (baseStart_3384653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384653 prefixEnd_3384653 := by exact prefixLift 3384653
  have htrace : WordTrace (prefixWord ++ tailWord_3384653) baseStart_3384653 baseEnd_3384653 := by
    simpa [prefixWord, tailWord_3384653, baseEnd_3384653] using wordTrace_append hprefix tailTrace_3384653
  have hstable : (prefixWord ++ tailWord_3384653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384653).length < 2 ^ (prefixWord ++ tailWord_3384653).sum := by decide
  have hdescent : baseEnd_3384653 < baseStart_3384653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384711 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 1, 4]
def baseStart_3384711 : Nat := 118140960795 + 3384711 * 2 ^ 59
def prefixEnd_3384711 : Nat := 4983230072969 + 3 ^ 40 * 3384711 * 2
def baseEnd_3384711 : Nat := 1158655746373474690897669

theorem tailTrace_3384711 : CollatzResearch.WordTrace tailWord_3384711 prefixEnd_3384711 1158655746373474690897669 := by
  unfold tailWord_3384711
  simp only [CollatzResearch.WordTrace]
  refine ⟨123450552040777584461993987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82300368027185056307995991 123450552040777584461993987)
  ·
    refine ⟨185175828061166376692990981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123450552040777584461993987 185175828061166376692990981)
    ·
      refine ⟨34720467761468695629935809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185175828061166376692990981 34720467761468695629935809)
      ·
        refine ⟨26040350821101521722451857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34720467761468695629935809 26040350821101521722451857)
        ·
          refine ⟨19530263115826141291838893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26040350821101521722451857 19530263115826141291838893)
          ·
            refine ⟨7323848668434802984439585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19530263115826141291838893 7323848668434802984439585)
            ·
              refine ⟨5492886501326102238329689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7323848668434802984439585 5492886501326102238329689)
              ·
                refine ⟨4119664875994576678747267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5492886501326102238329689 4119664875994576678747267)
                ·
                  refine ⟨6179497313991865018120901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4119664875994576678747267 6179497313991865018120901)
                  ·
                    refine ⟨1158655746373474690897669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179497313991865018120901 1158655746373474690897669)
                    ·
                      rfl

theorem cell22_3384711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_3384711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384711 prefixEnd_3384711 := by exact prefixLift 3384711
  have htrace : WordTrace (prefixWord ++ tailWord_3384711) baseStart_3384711 baseEnd_3384711 := by
    simpa [prefixWord, tailWord_3384711, baseEnd_3384711] using wordTrace_append hprefix tailTrace_3384711
  have hstable : (prefixWord ++ tailWord_3384711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384711).length < 2 ^ (prefixWord ++ tailWord_3384711).sum := by decide
  have hdescent : baseEnd_3384711 < baseStart_3384711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384739 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 2, 4]
def baseStart_3384739 : Nat := 118140960795 + 3384739 * 2 ^ 59
def prefixEnd_3384739 : Nat := 4983230072969 + 3 ^ 40 * 3384739 * 2
def baseEnd_3384739 : Nat := 1158665331345691951197583

theorem tailTrace_3384739 : CollatzResearch.WordTrace tailWord_3384739 prefixEnd_3384739 1158665331345691951197583 := by
  unfold tailWord_3384739
  simp only [CollatzResearch.WordTrace]
  refine ⟨123451573284676145244013271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82301048856450763496008847 123451573284676145244013271)
  ·
    refine ⟨185177359927014217866019907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123451573284676145244013271 185177359927014217866019907)
    ·
      refine ⟨277766039890521326799029861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185177359927014217866019907 277766039890521326799029861)
      ·
        refine ⟨52081132479472748774818099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277766039890521326799029861 52081132479472748774818099)
        ·
          refine ⟨78121698719209123162227149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52081132479472748774818099 78121698719209123162227149)
          ·
            refine ⟨29295637019703421185835181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78121698719209123162227149 29295637019703421185835181)
            ·
              refine ⟨10985863882388782944688193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29295637019703421185835181 10985863882388782944688193)
              ·
                refine ⟨8239397911791587208516145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10985863882388782944688193 8239397911791587208516145)
                ·
                  refine ⟨6179548433843690406387109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8239397911791587208516145 6179548433843690406387109)
                  ·
                    refine ⟨1158665331345691951197583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6179548433843690406387109 1158665331345691951197583)
                    ·
                      rfl

theorem cell22_3384739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_3384739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384739 prefixEnd_3384739 := by exact prefixLift 3384739
  have htrace : WordTrace (prefixWord ++ tailWord_3384739) baseStart_3384739 baseEnd_3384739 := by
    simpa [prefixWord, tailWord_3384739, baseEnd_3384739] using wordTrace_append hprefix tailTrace_3384739
  have hstable : (prefixWord ++ tailWord_3384739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384739).length < 2 ^ (prefixWord ++ tailWord_3384739).sum := by decide
  have hdescent : baseEnd_3384739 < baseStart_3384739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384743 : List Nat := [1, 1, 6, 1, 1, 1, 5, 2, 4]
def baseStart_3384743 : Nat := 118140960795 + 3384743 * 2 ^ 59
def prefixEnd_3384743 : Nat := 4983230072969 + 3 ^ 40 * 3384743 * 2
def baseEnd_3384743 : Nat := 386222233542479091365857

theorem tailTrace_3384743 : CollatzResearch.WordTrace tailWord_3384743 prefixEnd_3384743 386222233542479091365857 := by
  unfold tailWord_3384743
  simp only [CollatzResearch.WordTrace]
  refine ⟨123451719176661653927158883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82301146117774435951439255 123451719176661653927158883)
  ·
    refine ⟨185177578764992480890738325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123451719176661653927158883 185177578764992480890738325)
    ·
      refine ⟨8680199004609022541753359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185177578764992480890738325 8680199004609022541753359)
      ·
        refine ⟨13020298506913533812630039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8680199004609022541753359 13020298506913533812630039)
        ·
          refine ⟨19530447760370300718945059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13020298506913533812630039 19530447760370300718945059)
          ·
            refine ⟨29295671640555451078417589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19530447760370300718945059 29295671640555451078417589)
            ·
              refine ⟨2746469216302073538601649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29295671640555451078417589 2746469216302073538601649)
              ·
                refine ⟨2059851912226555153951237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746469216302073538601649 2059851912226555153951237)
                ·
                  refine ⟨386222233542479091365857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2059851912226555153951237 386222233542479091365857)
                  ·
                    rfl

theorem cell22_3384743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2, 4].length) (baseStart_3384743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384743 prefixEnd_3384743 := by exact prefixLift 3384743
  have htrace : WordTrace (prefixWord ++ tailWord_3384743) baseStart_3384743 baseEnd_3384743 := by
    simpa [prefixWord, tailWord_3384743, baseEnd_3384743] using wordTrace_append hprefix tailTrace_3384743
  have hstable : (prefixWord ++ tailWord_3384743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384743).length < 2 ^ (prefixWord ++ tailWord_3384743).sum := by decide
  have hdescent : baseEnd_3384743 < baseStart_3384743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384752 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_3384752 : Nat := 118140960795 + 3384752 * 2 ^ 59
def prefixEnd_3384752 : Nat := 4983230072969 + 3 ^ 40 * 3384752 * 2
def baseEnd_3384752 : Nat := 1158669781511364250622543

theorem tailTrace_3384752 : CollatzResearch.WordTrace tailWord_3384752 prefixEnd_3384752 1158669781511364250622543 := by
  unfold tailWord_3384752
  simp only [CollatzResearch.WordTrace]
  refine ⟨61726023716814524232118255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82301364955752698976157673 61726023716814524232118255)
  ·
    refine ⟨92589035575221786348177383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61726023716814524232118255 92589035575221786348177383)
    ·
      refine ⟨138883553362832679522266075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92589035575221786348177383 138883553362832679522266075)
      ·
        refine ⟨208325330044249019283399113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138883553362832679522266075 208325330044249019283399113)
        ·
          refine ⟨156243997533186764462549335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208325330044249019283399113 156243997533186764462549335)
          ·
            refine ⟨234365996299780146693824003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156243997533186764462549335 234365996299780146693824003)
            ·
              refine ⟨351548994449670220040736005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234365996299780146693824003 351548994449670220040736005)
              ·
                refine ⟨65915436459313166257638001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351548994449670220040736005 65915436459313166257638001)
                ·
                  refine ⟨49436577344484874693228501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65915436459313166257638001 49436577344484874693228501)
                  ·
                    refine ⟨1158669781511364250622543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49436577344484874693228501 1158669781511364250622543)
                    ·
                      rfl

theorem cell22_3384752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_3384752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384752 prefixEnd_3384752 := by exact prefixLift 3384752
  have htrace : WordTrace (prefixWord ++ tailWord_3384752) baseStart_3384752 baseEnd_3384752 := by
    simpa [prefixWord, tailWord_3384752, baseEnd_3384752] using wordTrace_append hprefix tailTrace_3384752
  have hstable : (prefixWord ++ tailWord_3384752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384752).length < 2 ^ (prefixWord ++ tailWord_3384752).sum := by decide
  have hdescent : baseEnd_3384752 < baseStart_3384752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384861 : List Nat := [1, 4, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3384861 : Nat := 118140960795 + 3384861 * 2 ^ 59
def prefixEnd_3384861 : Nat := 4983230072969 + 3 ^ 40 * 3384861 * 2
def baseEnd_3384861 : Nat := 386235698146308099882403

theorem tailTrace_3384861 : CollatzResearch.WordTrace tailWord_3384861 prefixEnd_3384861 386235698146308099882403 := by
  unfold tailWord_3384861
  simp only [CollatzResearch.WordTrace]
  refine ⟨123456022990234160079954437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82304015326822773386636291 123456022990234160079954437)
  ·
    refine ⟨23148004310668905014991457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123456022990234160079954437 23148004310668905014991457)
    ·
      refine ⟨17361003233001678761243593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23148004310668905014991457 17361003233001678761243593)
      ·
        refine ⟨13020752424751259070932695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17361003233001678761243593 13020752424751259070932695)
        ·
          refine ⟨19531128637126888606399043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13020752424751259070932695 19531128637126888606399043)
          ·
            refine ⟨29296692955690332909598565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19531128637126888606399043 29296692955690332909598565)
            ·
              refine ⟨5493129929191937420549731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29296692955690332909598565 5493129929191937420549731)
              ·
                refine ⟨8239694893787906130824597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493129929191937420549731 8239694893787906130824597)
                ·
                  refine ⟨386235698146308099882403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8239694893787906130824597 386235698146308099882403)
                  ·
                    rfl

theorem cell22_3384861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3384861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384861 prefixEnd_3384861 := by exact prefixLift 3384861
  have htrace : WordTrace (prefixWord ++ tailWord_3384861) baseStart_3384861 baseEnd_3384861 := by
    simpa [prefixWord, tailWord_3384861, baseEnd_3384861] using wordTrace_append hprefix tailTrace_3384861
  have hstable : (prefixWord ++ tailWord_3384861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384861).length < 2 ^ (prefixWord ++ tailWord_3384861).sum := by decide
  have hdescent : baseEnd_3384861 < baseStart_3384861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3384996 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 8]
def baseStart_3384996 : Nat := 118140960795 + 3384996 * 2 ^ 59
def prefixEnd_3384996 : Nat := 4983230072969 + 3 ^ 40 * 3384996 * 2
def baseEnd_3384996 : Nat := 386251102565942982507265

theorem tailTrace_3384996 : CollatzResearch.WordTrace tailWord_3384996 prefixEnd_3384996 386251102565942982507265 := by
  unfold tailWord_3384996
  simp only [CollatzResearch.WordTrace]
  refine ⟨61730473422372539068059421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82307297896496718757412561 61730473422372539068059421)
  ·
    refine ⟨23148927533389702150522283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61730473422372539068059421 23148927533389702150522283)
    ·
      refine ⟨34723391300084553225783425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23148927533389702150522283 34723391300084553225783425)
      ·
        refine ⟨26042543475063414919337569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34723391300084553225783425 26042543475063414919337569)
        ·
          refine ⟨19531907606297561189503177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26042543475063414919337569 19531907606297561189503177)
          ·
            refine ⟨14648930704723170892127383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19531907606297561189503177 14648930704723170892127383)
            ·
              refine ⟨21973396057084756338191075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14648930704723170892127383 21973396057084756338191075)
              ·
                refine ⟨32960094085627134507286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21973396057084756338191075 32960094085627134507286613)
                ·
                  refine ⟨386251102565942982507265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32960094085627134507286613 386251102565942982507265)
                  ·
                    rfl

theorem cell22_3384996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_3384996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3384996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3384996 prefixEnd_3384996 := by exact prefixLift 3384996
  have htrace : WordTrace (prefixWord ++ tailWord_3384996) baseStart_3384996 baseEnd_3384996 := by
    simpa [prefixWord, tailWord_3384996, baseEnd_3384996] using wordTrace_append hprefix tailTrace_3384996
  have hstable : (prefixWord ++ tailWord_3384996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3384996).length < 2 ^ (prefixWord ++ tailWord_3384996).sum := by decide
  have hdescent : baseEnd_3384996 < baseStart_3384996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3384996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385011 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 1, 5]
def baseStart_3385011 : Nat := 118140960795 + 3385011 * 2 ^ 59
def prefixEnd_3385011 : Nat := 4983230072969 + 3 ^ 40 * 3385011 * 2
def baseEnd_3385011 : Nat := 1158758442504373908396749

theorem tailTrace_3385011 : CollatzResearch.WordTrace tailWord_3385011 prefixEnd_3385011 1158758442504373908396749 := by
  unfold tailWord_3385011
  simp only [CollatzResearch.WordTrace]
  refine ⟨123461493939690735697914887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82307662626460490465276591 123461493939690735697914887)
  ·
    refine ⟨185192240909536103546872331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123461493939690735697914887 185192240909536103546872331)
    ·
      refine ⟨277788361364304155320308497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185192240909536103546872331 277788361364304155320308497)
      ·
        refine ⟨208341271023228116490231373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277788361364304155320308497 208341271023228116490231373)
        ·
          refine ⟨78127976633710543683836765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208341271023228116490231373 78127976633710543683836765)
          ·
            refine ⟨29297991237641453881438787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78127976633710543683836765 29297991237641453881438787)
            ·
              refine ⟨43946986856462180822158181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29297991237641453881438787 43946986856462180822158181)
              ·
                refine ⟨8240060035586658904154659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43946986856462180822158181 8240060035586658904154659)
                ·
                  refine ⟨12360090053379988356231989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8240060035586658904154659 12360090053379988356231989)
                  ·
                    refine ⟨1158758442504373908396749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12360090053379988356231989 1158758442504373908396749)
                    ·
                      rfl

theorem cell22_3385011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_3385011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385011 prefixEnd_3385011 := by exact prefixLift 3385011
  have htrace : WordTrace (prefixWord ++ tailWord_3385011) baseStart_3385011 baseEnd_3385011 := by
    simpa [prefixWord, tailWord_3385011, baseEnd_3385011] using wordTrace_append hprefix tailTrace_3385011
  have hstable : (prefixWord ++ tailWord_3385011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385011).length < 2 ^ (prefixWord ++ tailWord_3385011).sum := by decide
  have hdescent : baseEnd_3385011 < baseStart_3385011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385015 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 1, 4]
def baseStart_3385015 : Nat := 118140960795 + 3385015 * 2 ^ 59
def prefixEnd_3385015 : Nat := 4983230072969 + 3 ^ 40 * 3385015 * 2
def baseEnd_3385015 : Nat := 1158759811786119231296737

theorem tailTrace_3385015 : CollatzResearch.WordTrace tailWord_3385015 prefixEnd_3385015 1158759811786119231296737 := by
  unfold tailWord_3385015
  simp only [CollatzResearch.WordTrace]
  refine ⟨123461639831676244381060499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82307759887784162920706999 123461639831676244381060499)
  ·
    refine ⟨185192459747514366571590749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123461639831676244381060499 185192459747514366571590749)
    ·
      refine ⟨69447172405317887464346531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185192459747514366571590749 69447172405317887464346531)
      ·
        refine ⟨104170758607976831196519797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69447172405317887464346531 104170758607976831196519797)
        ·
          refine ⟨9766008619497827924673731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104170758607976831196519797 9766008619497827924673731)
          ·
            refine ⟨14649012929246741887010597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766008619497827924673731 14649012929246741887010597)
            ·
              refine ⟨2746689924233764103814487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14649012929246741887010597 2746689924233764103814487)
              ·
                refine ⟨4120034886350646155721731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746689924233764103814487 4120034886350646155721731)
                ·
                  refine ⟨6180052329525969233582597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120034886350646155721731 6180052329525969233582597)
                  ·
                    refine ⟨1158759811786119231296737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180052329525969233582597 1158759811786119231296737)
                    ·
                      rfl

theorem cell22_3385015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_3385015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385015 prefixEnd_3385015 := by exact prefixLift 3385015
  have htrace : WordTrace (prefixWord ++ tailWord_3385015) baseStart_3385015 baseEnd_3385015 := by
    simpa [prefixWord, tailWord_3385015, baseEnd_3385015] using wordTrace_append hprefix tailTrace_3385015
  have hstable : (prefixWord ++ tailWord_3385015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385015).length < 2 ^ (prefixWord ++ tailWord_3385015).sum := by decide
  have hdescent : baseEnd_3385015 < baseStart_3385015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385141 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3385141 : Nat := 118140960795 + 3385141 * 2 ^ 59
def prefixEnd_3385141 : Nat := 4983230072969 + 3 ^ 40 * 3385141 * 2
def baseEnd_3385141 : Nat := 1158802944161096902646351

theorem tailTrace_3385141 : CollatzResearch.WordTrace tailWord_3385141 prefixEnd_3385141 1158802944161096902646351 := by
  unfold tailWord_3385141
  simp only [CollatzResearch.WordTrace]
  refine ⟨123466235429219767900147277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82310823619479845266764851 123466235429219767900147277)
  ·
    refine ⟨46299838285957412962555229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123466235429219767900147277 46299838285957412962555229)
    ·
      refine ⟨17362439357234029860958211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46299838285957412962555229 17362439357234029860958211)
      ·
        refine ⟨26043659035851044791437317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362439357234029860958211 26043659035851044791437317)
        ·
          refine ⟨4883186069222070898394497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26043659035851044791437317 4883186069222070898394497)
          ·
            refine ⟨3662389551916553173795873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883186069222070898394497 3662389551916553173795873)
            ·
              refine ⟨2746792163937414880346905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662389551916553173795873 2746792163937414880346905)
              ·
                refine ⟨2060094122953061160260179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2746792163937414880346905 2060094122953061160260179)
                ·
                  refine ⟨3090141184429591740390269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060094122953061160260179 3090141184429591740390269)
                  ·
                    refine ⟨1158802944161096902646351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090141184429591740390269 1158802944161096902646351)
                    ·
                      rfl

theorem cell22_3385141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3385141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385141 prefixEnd_3385141 := by exact prefixLift 3385141
  have htrace : WordTrace (prefixWord ++ tailWord_3385141) baseStart_3385141 baseEnd_3385141 := by
    simpa [prefixWord, tailWord_3385141, baseEnd_3385141] using wordTrace_append hprefix tailTrace_3385141
  have hstable : (prefixWord ++ tailWord_3385141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385141).length < 2 ^ (prefixWord ++ tailWord_3385141).sum := by decide
  have hdescent : baseEnd_3385141 < baseStart_3385141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385150 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3385150 : Nat := 118140960795 + 3385150 * 2 ^ 59
def prefixEnd_3385150 : Nat := 4983230072969 + 3 ^ 40 * 3385150 * 2
def baseEnd_3385150 : Nat := 1158806025045023879171323

theorem tailTrace_3385150 : CollatzResearch.WordTrace tailWord_3385150 prefixEnd_3385150 1158806025045023879171323 := by
  unfold tailWord_3385150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433320460773395304653113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82311042457458108291483269 15433320460773395304653113)
  ·
    refine ⟨11574990345580046478489835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15433320460773395304653113 11574990345580046478489835)
    ·
      refine ⟨17362485518370069717734753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11574990345580046478489835 17362485518370069717734753)
      ·
        refine ⟨13021864138777552288301065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17362485518370069717734753 13021864138777552288301065)
        ·
          refine ⟨9766398104083164216225799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13021864138777552288301065 9766398104083164216225799)
          ·
            refine ⟨14649597156124746324338699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766398104083164216225799 14649597156124746324338699)
            ·
              refine ⟨21974395734187119486508049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14649597156124746324338699 21974395734187119486508049)
              ·
                refine ⟨16480796800640339614881037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21974395734187119486508049 16480796800640339614881037)
                ·
                  refine ⟨6180298800240127355580389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16480796800640339614881037 6180298800240127355580389)
                  ·
                    refine ⟨1158806025045023879171323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180298800240127355580389 1158806025045023879171323)
                    ·
                      rfl

theorem cell22_3385150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3385150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385150 prefixEnd_3385150 := by exact prefixLift 3385150
  have htrace : WordTrace (prefixWord ++ tailWord_3385150) baseStart_3385150 baseEnd_3385150 := by
    simpa [prefixWord, tailWord_3385150, baseEnd_3385150] using wordTrace_append hprefix tailTrace_3385150
  have hstable : (prefixWord ++ tailWord_3385150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385150).length < 2 ^ (prefixWord ++ tailWord_3385150).sum := by decide
  have hdescent : baseEnd_3385150 < baseStart_3385150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385165 : List Nat := [1, 6, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3385165 : Nat := 118140960795 + 3385165 * 2 ^ 59
def prefixEnd_3385165 : Nat := 4983230072969 + 3 ^ 40 * 3385165 * 2
def baseEnd_3385165 : Nat := 386270386617189613348759

theorem tailTrace_3385165 : CollatzResearch.WordTrace tailWord_3385165 prefixEnd_3385165 386270386617189613348759 := by
  unfold tailWord_3385165
  simp only [CollatzResearch.WordTrace]
  refine ⟨123467110781132819999020949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82311407187421879999347299 123467110781132819999020949)
  ·
    refine ⟨5787520817865600937454107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123467110781132819999020949 5787520817865600937454107)
    ·
      refine ⟨8681281226798401406181161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787520817865600937454107 8681281226798401406181161)
      ·
        refine ⟨6510960920098801054635871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8681281226798401406181161 6510960920098801054635871)
        ·
          refine ⟨9766441380148201581953807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6510960920098801054635871 9766441380148201581953807)
          ·
            refine ⟨14649662070222302372930711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766441380148201581953807 14649662070222302372930711)
            ·
              refine ⟨21974493105333453559396067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14649662070222302372930711 21974493105333453559396067)
              ·
                refine ⟨32961739658000180339094101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21974493105333453559396067 32961739658000180339094101)
                ·
                  refine ⟨386270386617189613348759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32961739658000180339094101 386270386617189613348759)
                  ·
                    rfl

theorem cell22_3385165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3385165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385165 prefixEnd_3385165 := by exact prefixLift 3385165
  have htrace : WordTrace (prefixWord ++ tailWord_3385165) baseStart_3385165 baseEnd_3385165 := by
    simpa [prefixWord, tailWord_3385165, baseEnd_3385165] using wordTrace_append hprefix tailTrace_3385165
  have hstable : (prefixWord ++ tailWord_3385165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385165).length < 2 ^ (prefixWord ++ tailWord_3385165).sum := by decide
  have hdescent : baseEnd_3385165 < baseStart_3385165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385178 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_3385178 : Nat := 118140960795 + 3385178 * 2 ^ 59
def prefixEnd_3385178 : Nat := 4983230072969 + 3 ^ 40 * 3385178 * 2
def baseEnd_3385178 : Nat := 1158815610017241139471237

theorem tailTrace_3385178 : CollatzResearch.WordTrace tailWord_3385178 prefixEnd_3385178 1158815610017241139471237 := by
  unfold tailWord_3385178
  simp only [CollatzResearch.WordTrace]
  refine ⟨30866896232521430804811047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82311723286723815479496125 30866896232521430804811047)
  ·
    refine ⟨46300344348782146207216571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30866896232521430804811047 46300344348782146207216571)
    ·
      refine ⟨69450516523173219310824857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46300344348782146207216571 69450516523173219310824857)
      ·
        refine ⟨52087887392379914483118643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69450516523173219310824857 52087887392379914483118643)
        ·
          refine ⟨78131831088569871724677965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52087887392379914483118643 78131831088569871724677965)
          ·
            refine ⟨29299436658213701896754237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78131831088569871724677965 29299436658213701896754237)
            ·
              refine ⟨10987288746830138211282839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29299436658213701896754237 10987288746830138211282839)
              ·
                refine ⟨16480933120245207316924259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987288746830138211282839 16480933120245207316924259)
                ·
                  refine ⟨24721399680367810975386389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16480933120245207316924259 24721399680367810975386389)
                  ·
                    refine ⟨1158815610017241139471237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24721399680367810975386389 1158815610017241139471237)
                    ·
                      rfl

theorem cell22_3385178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_3385178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385178 prefixEnd_3385178 := by exact prefixLift 3385178
  have htrace : WordTrace (prefixWord ++ tailWord_3385178) baseStart_3385178 baseEnd_3385178 := by
    simpa [prefixWord, tailWord_3385178, baseEnd_3385178] using wordTrace_append hprefix tailTrace_3385178
  have hstable : (prefixWord ++ tailWord_3385178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385178).length < 2 ^ (prefixWord ++ tailWord_3385178).sum := by decide
  have hdescent : baseEnd_3385178 < baseStart_3385178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385197 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3385197 : Nat := 118140960795 + 3385197 * 2 ^ 59
def prefixEnd_3385197 : Nat := 4983230072969 + 3 ^ 40 * 3385197 * 2
def baseEnd_3385197 : Nat := 1158822114105531423246179

theorem tailTrace_3385197 : CollatzResearch.WordTrace tailWord_3385197 prefixEnd_3385197 1158822114105531423246179 := by
  unfold tailWord_3385197
  simp only [CollatzResearch.WordTrace]
  refine ⟨123468277917016889464185845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82312185278011259642790563 123468277917016889464185845)
  ·
    refine ⟨11575151054720333387267423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123468277917016889464185845 11575151054720333387267423)
    ·
      refine ⟨17362726582080500080901135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11575151054720333387267423 17362726582080500080901135)
      ·
        refine ⟨26044089873120750121351703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17362726582080500080901135 26044089873120750121351703)
        ·
          refine ⟨39066134809681125182027555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26044089873120750121351703 39066134809681125182027555)
          ·
            refine ⟨58599202214521687773041333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39066134809681125182027555 58599202214521687773041333)
            ·
              refine ⟨5493675207611408228722625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58599202214521687773041333 5493675207611408228722625)
              ·
                refine ⟨4120256405708556171541969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5493675207611408228722625 4120256405708556171541969)
                ·
                  refine ⟨3090192304281417128656477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4120256405708556171541969 3090192304281417128656477)
                  ·
                    refine ⟨1158822114105531423246179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090192304281417128656477 1158822114105531423246179)
                    ·
                      rfl

theorem cell22_3385197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3385197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385197 prefixEnd_3385197 := by exact prefixLift 3385197
  have htrace : WordTrace (prefixWord ++ tailWord_3385197) baseStart_3385197 baseEnd_3385197 := by
    simpa [prefixWord, tailWord_3385197, baseEnd_3385197] using wordTrace_append hprefix tailTrace_3385197
  have hstable : (prefixWord ++ tailWord_3385197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385197).length < 2 ^ (prefixWord ++ tailWord_3385197).sum := by decide
  have hdescent : baseEnd_3385197 < baseStart_3385197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385214 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 1, 5]
def baseStart_3385214 : Nat := 118140960795 + 3385214 * 2 ^ 59
def prefixEnd_3385214 : Nat := 4983230072969 + 3 ^ 40 * 3385214 * 2
def baseEnd_3385214 : Nat := 1158827933552949045571127

theorem tailTrace_3385214 : CollatzResearch.WordTrace tailWord_3385214 prefixEnd_3385214 1158827933552949045571127 := by
  unfold tailWord_3385214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15433612244744412670944337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82312598638636867578369797 15433612244744412670944337)
  ·
    refine ⟨11575209183558309503208253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15433612244744412670944337 11575209183558309503208253)
    ·
      refine ⟨4340703443834366063703095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11575209183558309503208253 4340703443834366063703095)
      ·
        refine ⟨6511055165751549095554643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340703443834366063703095 6511055165751549095554643)
        ·
          refine ⟨9766582748627323643331965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6511055165751549095554643 9766582748627323643331965)
          ·
            refine ⟨3662468530735246366249487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9766582748627323643331965 3662468530735246366249487)
            ·
              refine ⟨5493702796102869549374231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3662468530735246366249487 5493702796102869549374231)
              ·
                refine ⟨8240554194154304324061347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5493702796102869549374231 8240554194154304324061347)
                ·
                  refine ⟨12360831291231456486092021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8240554194154304324061347 12360831291231456486092021)
                  ·
                    refine ⟨1158827933552949045571127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12360831291231456486092021 1158827933552949045571127)
                    ·
                      rfl

theorem cell22_3385214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_3385214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385214 prefixEnd_3385214 := by exact prefixLift 3385214
  have htrace : WordTrace (prefixWord ++ tailWord_3385214) baseStart_3385214 baseEnd_3385214 := by
    simpa [prefixWord, tailWord_3385214, baseEnd_3385214] using wordTrace_append hprefix tailTrace_3385214
  have hstable : (prefixWord ++ tailWord_3385214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385214).length < 2 ^ (prefixWord ++ tailWord_3385214).sum := by decide
  have hdescent : baseEnd_3385214 < baseStart_3385214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385225 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_3385225 : Nat := 118140960795 + 3385225 * 2 ^ 59
def prefixEnd_3385225 : Nat := 4983230072969 + 3 ^ 40 * 3385225 * 2
def baseEnd_3385225 : Nat := 1158831699077748683546093

theorem tailTrace_3385225 : CollatzResearch.WordTrace tailWord_3385225 prefixEnd_3385225 1158831699077748683546093 := by
  unfold tailWord_3385225
  simp only [CollatzResearch.WordTrace]
  refine ⟨123469299160915450246205129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82312866107276966830803419 123469299160915450246205129)
  ·
    refine ⟨92601974370686587684653847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123469299160915450246205129 92601974370686587684653847)
    ·
      refine ⟨138902961556029881526980771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92601974370686587684653847 138902961556029881526980771)
      ·
        refine ⟨208354442334044822290471157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138902961556029881526980771 208354442334044822290471157)
        ·
          refine ⟨19533228968816702089731671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 208354442334044822290471157 19533228968816702089731671)
          ·
            refine ⟨29299843453225053134597507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19533228968816702089731671 29299843453225053134597507)
            ·
              refine ⟨43949765179837579701896261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29299843453225053134597507 43949765179837579701896261)
              ·
                refine ⟨8240580971219546194105549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43949765179837579701896261 8240580971219546194105549)
                ·
                  refine ⟨3090217864207329822789581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8240580971219546194105549 3090217864207329822789581)
                  ·
                    refine ⟨1158831699077748683546093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090217864207329822789581 1158831699077748683546093)
                    ·
                      rfl

theorem cell22_3385225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_3385225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385225 prefixEnd_3385225 := by exact prefixLift 3385225
  have htrace : WordTrace (prefixWord ++ tailWord_3385225) baseStart_3385225 baseEnd_3385225 := by
    simpa [prefixWord, tailWord_3385225, baseEnd_3385225] using wordTrace_append hprefix tailTrace_3385225
  have hstable : (prefixWord ++ tailWord_3385225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385225).length < 2 ^ (prefixWord ++ tailWord_3385225).sum := by decide
  have hdescent : baseEnd_3385225 < baseStart_3385225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385253 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_3385253 : Nat := 118140960795 + 3385253 * 2 ^ 59
def prefixEnd_3385253 : Nat := 4983230072969 + 3 ^ 40 * 3385253 * 2
def baseEnd_3385253 : Nat := 1158841284049965943846007

theorem tailTrace_3385253 : CollatzResearch.WordTrace tailWord_3385253 prefixEnd_3385253 1158841284049965943846007 := by
  unfold tailWord_3385253
  simp only [CollatzResearch.WordTrace]
  refine ⟨123470320404814011028224413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82313546936542674018816275 123470320404814011028224413)
  ·
    refine ⟨46301370151805254135584155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123470320404814011028224413 46301370151805254135584155)
    ·
      refine ⟨69452055227707881203376233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46301370151805254135584155 69452055227707881203376233)
      ·
        refine ⟨52089041420780910902532175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69452055227707881203376233 52089041420780910902532175)
        ·
          refine ⟨78133562131171366353798263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52089041420780910902532175 78133562131171366353798263)
          ·
            refine ⟨117200343196757049530697395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78133562131171366353798263 117200343196757049530697395)
            ·
              refine ⟨175800514795135574296046093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117200343196757049530697395 175800514795135574296046093)
              ·
                refine ⟨65925193048175840361017285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175800514795135574296046093 65925193048175840361017285)
                ·
                  refine ⟨12360973696532970067690741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65925193048175840361017285 12360973696532970067690741)
                  ·
                    refine ⟨1158841284049965943846007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12360973696532970067690741 1158841284049965943846007)
                    ·
                      rfl

theorem cell22_3385253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_3385253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385253 prefixEnd_3385253 := by exact prefixLift 3385253
  have htrace : WordTrace (prefixWord ++ tailWord_3385253) baseStart_3385253 baseEnd_3385253 := by
    simpa [prefixWord, tailWord_3385253, baseEnd_3385253] using wordTrace_append hprefix tailTrace_3385253
  have hstable : (prefixWord ++ tailWord_3385253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385253).length < 2 ^ (prefixWord ++ tailWord_3385253).sum := by decide
  have hdescent : baseEnd_3385253 < baseStart_3385253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385255 : List Nat := [1, 1, 6, 1, 2, 1, 2, 1, 7]
def baseStart_3385255 : Nat := 118140960795 + 3385255 * 2 ^ 59
def prefixEnd_3385255 : Nat := 4983230072969 + 3 ^ 40 * 3385255 * 2
def baseEnd_3385255 : Nat := 386280656230279535098667

theorem tailTrace_3385255 : CollatzResearch.WordTrace tailWord_3385255 prefixEnd_3385255 386280656230279535098667 := by
  unfold tailWord_3385255
  simp only [CollatzResearch.WordTrace]
  refine ⟨123470393350806765369797219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82313595567204510246531479 123470393350806765369797219)
  ·
    refine ⟨185205590026210148054695829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123470393350806765369797219 185205590026210148054695829)
    ·
      refine ⟨8681512032478600690063867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185205590026210148054695829 8681512032478600690063867)
      ·
        refine ⟨13022268048717901035095801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8681512032478600690063867 13022268048717901035095801)
        ·
          refine ⟨9766701036538425776321851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13022268048717901035095801 9766701036538425776321851)
          ·
            refine ⟨14650051554807638664482777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9766701036538425776321851 14650051554807638664482777)
            ·
              refine ⟨10987538666105728998362083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14650051554807638664482777 10987538666105728998362083)
              ·
                refine ⟨16481307999158593497543125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10987538666105728998362083 16481307999158593497543125)
                ·
                  refine ⟨386280656230279535098667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16481307999158593497543125 386280656230279535098667)
                  ·
                    rfl

theorem cell22_3385255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 7].length) (baseStart_3385255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385255 prefixEnd_3385255 := by exact prefixLift 3385255
  have htrace : WordTrace (prefixWord ++ tailWord_3385255) baseStart_3385255 baseEnd_3385255 := by
    simpa [prefixWord, tailWord_3385255, baseEnd_3385255] using wordTrace_append hprefix tailTrace_3385255
  have hstable : (prefixWord ++ tailWord_3385255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385255).length < 2 ^ (prefixWord ++ tailWord_3385255).sum := by decide
  have hdescent : baseEnd_3385255 < baseStart_3385255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385285 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3385285 : Nat := 118140960795 + 3385285 * 2 ^ 59
def prefixEnd_3385285 : Nat := 4983230072969 + 3 ^ 40 * 3385285 * 2
def baseEnd_3385285 : Nat := 1158852238303928527045909

theorem tailTrace_3385285 : CollatzResearch.WordTrace tailWord_3385285 prefixEnd_3385285 1158852238303928527045909 := by
  unfold tailWord_3385285
  simp only [CollatzResearch.WordTrace]
  refine ⟨123471487540698080493389309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82314325027132053662259539 123471487540698080493389309)
  ·
    refine ⟨46301807827761780185020991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123471487540698080493389309 46301807827761780185020991)
    ·
      refine ⟨69452711741642670277531487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46301807827761780185020991 69452711741642670277531487)
      ·
        refine ⟨104179067612464005416297231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69452711741642670277531487 104179067612464005416297231)
        ·
          refine ⟨156268601418696008124445847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104179067612464005416297231 156268601418696008124445847)
          ·
            refine ⟨234402902128044012186668771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156268601418696008124445847 234402902128044012186668771)
            ·
              refine ⟨351604353192066018280003157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234402902128044012186668771 351604353192066018280003157)
              ·
                refine ⟨4120363513969523651718787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 351604353192066018280003157 4120363513969523651718787)
                ·
                  refine ⟨6180545270954285477578181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4120363513969523651718787 6180545270954285477578181)
                  ·
                    refine ⟨1158852238303928527045909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6180545270954285477578181 1158852238303928527045909)
                    ·
                      rfl

theorem cell22_3385285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3385285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385285 prefixEnd_3385285 := by exact prefixLift 3385285
  have htrace : WordTrace (prefixWord ++ tailWord_3385285) baseStart_3385285 baseEnd_3385285 := by
    simpa [prefixWord, tailWord_3385285, baseEnd_3385285] using wordTrace_append hprefix tailTrace_3385285
  have hstable : (prefixWord ++ tailWord_3385285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385285).length < 2 ^ (prefixWord ++ tailWord_3385285).sum := by decide
  have hdescent : baseEnd_3385285 < baseStart_3385285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385383 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3385383 : Nat := 118140960795 + 3385383 * 2 ^ 59
def prefixEnd_3385383 : Nat := 4983230072969 + 3 ^ 40 * 3385383 * 2
def baseEnd_3385383 : Nat := 1158885785706688938095609

theorem tailTrace_3385383 : CollatzResearch.WordTrace tailWord_3385383 prefixEnd_3385383 1158885785706688938095609 := by
  unfold tailWord_3385383
  simp only [CollatzResearch.WordTrace]
  refine ⟨123475061894343043230456803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82316707929562028820304535 123475061894343043230456803)
  ·
    refine ⟨185212592841514564845685205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123475061894343043230456803 185212592841514564845685205)
    ·
      refine ⟨4340920144722997613570747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 185212592841514564845685205 4340920144722997613570747)
      ·
        refine ⟨6511380217084496420356121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4340920144722997613570747 6511380217084496420356121)
        ·
          refine ⟨4883535162813372315267091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511380217084496420356121 4883535162813372315267091)
          ·
            refine ⟨7325302744220058472900637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883535162813372315267091 7325302744220058472900637)
            ·
              refine ⟨2746988529082521927337739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7325302744220058472900637 2746988529082521927337739)
              ·
                refine ⟨4120482793623782891006609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2746988529082521927337739 4120482793623782891006609)
                ·
                  refine ⟨3090362095217837168254957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4120482793623782891006609 3090362095217837168254957)
                  ·
                    refine ⟨1158885785706688938095609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090362095217837168254957 1158885785706688938095609)
                    ·
                      rfl

theorem cell22_3385383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3385383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385383 prefixEnd_3385383 := by exact prefixLift 3385383
  have htrace : WordTrace (prefixWord ++ tailWord_3385383) baseStart_3385383 baseEnd_3385383 := by
    simpa [prefixWord, tailWord_3385383, baseEnd_3385383] using wordTrace_append hprefix tailTrace_3385383
  have hstable : (prefixWord ++ tailWord_3385383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385383).length < 2 ^ (prefixWord ++ tailWord_3385383).sum := by decide
  have hdescent : baseEnd_3385383 < baseStart_3385383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385396 : List Nat := [2, 5, 1, 2, 2, 2, 2, 6]
def baseStart_3385396 : Nat := 118140960795 + 3385396 * 2 ^ 59
def prefixEnd_3385396 : Nat := 4983230072969 + 3 ^ 40 * 3385396 * 2
def baseEnd_3385396 : Nat := 128765581763595693057841

theorem tailTrace_3385396 : CollatzResearch.WordTrace tailWord_3385396 prefixEnd_3385396 128765581763595693057841 := by
  unfold tailWord_3385396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61737768021647973225340021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82317024028863964300453361 61737768021647973225340021)
  ·
    refine ⟨5787915752029497489875627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61737768021647973225340021 5787915752029497489875627)
    ·
      refine ⟨8681873628044246234813441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5787915752029497489875627 8681873628044246234813441)
      ·
        refine ⟨6511405221033184676110081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8681873628044246234813441 6511405221033184676110081)
        ·
          refine ⟨4883553915774888507082561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6511405221033184676110081 4883553915774888507082561)
          ·
            refine ⟨3662665436831166380311921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4883553915774888507082561 3662665436831166380311921)
            ·
              refine ⟨2746999077623374785233941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3662665436831166380311921 2746999077623374785233941)
              ·
                refine ⟨128765581763595693057841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2746999077623374785233941 128765581763595693057841)
                ·
                  rfl

theorem cell22_3385396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 2, 6].length) (baseStart_3385396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385396 prefixEnd_3385396 := by exact prefixLift 3385396
  have htrace : WordTrace (prefixWord ++ tailWord_3385396) baseStart_3385396 baseEnd_3385396 := by
    simpa [prefixWord, tailWord_3385396, baseEnd_3385396] using wordTrace_append hprefix tailTrace_3385396
  have hstable : (prefixWord ++ tailWord_3385396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385396).length < 2 ^ (prefixWord ++ tailWord_3385396).sum := by decide
  have hdescent : baseEnd_3385396 < baseStart_3385396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385486 : List Nat := [4, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_3385486 : Nat := 118140960795 + 3385486 * 2 ^ 59
def prefixEnd_3385486 : Nat := 4983230072969 + 3 ^ 40 * 3385486 * 2
def baseEnd_3385486 : Nat := 386307014903877000923431

theorem tailTrace_3385486 : CollatzResearch.WordTrace tailWord_3385486 prefixEnd_3385486 386307014903877000923431 := by
  unfold tailWord_3385486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15434852326621236477682039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82319212408646594547637541 15434852326621236477682039)
  ·
    refine ⟨23152278489931854716523059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15434852326621236477682039 23152278489931854716523059)
    ·
      refine ⟨34728417734897782074784589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23152278489931854716523059 34728417734897782074784589)
      ·
        refine ⟨13023156650586668278044221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34728417734897782074784589 13023156650586668278044221)
        ·
          refine ⟨4883683743970000604266583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13023156650586668278044221 4883683743970000604266583)
          ·
            refine ⟨7325525615955000906399875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4883683743970000604266583 7325525615955000906399875)
            ·
              refine ⟨10988288423932501359599813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325525615955000906399875 10988288423932501359599813)
              ·
                refine ⟨2060304079487344004924965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10988288423932501359599813 2060304079487344004924965)
                ·
                  refine ⟨386307014903877000923431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060304079487344004924965 386307014903877000923431)
                  ·
                    rfl

theorem cell22_3385486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_3385486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385486 prefixEnd_3385486 := by exact prefixLift 3385486
  have htrace : WordTrace (prefixWord ++ tailWord_3385486) baseStart_3385486 baseEnd_3385486 := by
    simpa [prefixWord, tailWord_3385486, baseEnd_3385486] using wordTrace_append hprefix tailTrace_3385486
  have hstable : (prefixWord ++ tailWord_3385486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385486).length < 2 ^ (prefixWord ++ tailWord_3385486).sum := by decide
  have hdescent : baseEnd_3385486 < baseStart_3385486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385546 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 1, 3]
def baseStart_3385546 : Nat := 118140960795 + 3385546 * 2 ^ 59
def prefixEnd_3385546 : Nat := 4983230072969 + 3 ^ 40 * 3385546 * 2
def baseEnd_3385546 : Nat := 1158941583937810846270109

theorem tailTrace_3385546 : CollatzResearch.WordTrace tailWord_3385546 prefixEnd_3385546 1158941583937810846270109 := by
  unfold tailWord_3385546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30870251748188130517160123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82320671328501681379093661 30870251748188130517160123)
  ·
    refine ⟨46305377622282195775740185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30870251748188130517160123 46305377622282195775740185)
    ·
      refine ⟨34729033216711646831805139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46305377622282195775740185 34729033216711646831805139)
      ·
        refine ⟨52093549825067470247707709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34729033216711646831805139 52093549825067470247707709)
        ·
          refine ⟨19535081184400301342890391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52093549825067470247707709 19535081184400301342890391)
          ·
            refine ⟨29302621776600452014335587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19535081184400301342890391 29302621776600452014335587)
            ·
              refine ⟨43953932664900678021503381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29302621776600452014335587 43953932664900678021503381)
              ·
                refine ⟨2060340593667219282257971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43953932664900678021503381 2060340593667219282257971)
                ·
                  refine ⟨3090510890500828923386957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2060340593667219282257971 3090510890500828923386957)
                  ·
                    refine ⟨1158941583937810846270109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090510890500828923386957 1158941583937810846270109)
                    ·
                      rfl

theorem cell22_3385546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_3385546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385546 prefixEnd_3385546 := by exact prefixLift 3385546
  have htrace : WordTrace (prefixWord ++ tailWord_3385546) baseStart_3385546 baseEnd_3385546 := by
    simpa [prefixWord, tailWord_3385546, baseEnd_3385546] using wordTrace_append hprefix tailTrace_3385546
  have hstable : (prefixWord ++ tailWord_3385546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385546).length < 2 ^ (prefixWord ++ tailWord_3385546).sum := by decide
  have hdescent : baseEnd_3385546 < baseStart_3385546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385649 : List Nat := [1, 2, 2, 3, 5, 9]
def baseStart_3385649 : Nat := 118140960795 + 3385649 * 2 ^ 59
def prefixEnd_3385649 : Nat := 4983230072969 + 3 ^ 40 * 3385649 * 2
def baseEnd_3385649 : Nat := 14308356085712998900553

theorem tailTrace_3385649 : CollatzResearch.WordTrace tailWord_3385649 prefixEnd_3385649 14308356085712998900553 := by
  unfold tailWord_3385649
  simp only [CollatzResearch.WordTrace]
  refine ⟨123484763711379370659640001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82323175807586247106426667 123484763711379370659640001)
  ·
    refine ⟨92613572783534527994730001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123484763711379370659640001 92613572783534527994730001)
    ·
      refine ⟨69460179587650895996047501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92613572783534527994730001 69460179587650895996047501)
      ·
        refine ⟨26047567345369085998517813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69460179587650895996047501 26047567345369085998517813)
        ·
          refine ⟨2441959438628351812361045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26047567345369085998517813 2441959438628351812361045)
          ·
            refine ⟨14308356085712998900553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2441959438628351812361045 14308356085712998900553)
            ·
              rfl

theorem cell22_3385649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 9].length) (baseStart_3385649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385649 prefixEnd_3385649 := by exact prefixLift 3385649
  have htrace : WordTrace (prefixWord ++ tailWord_3385649) baseStart_3385649 baseEnd_3385649 := by
    simpa [prefixWord, tailWord_3385649, baseEnd_3385649] using wordTrace_append hprefix tailTrace_3385649
  have hstable : (prefixWord ++ tailWord_3385649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385649).length < 2 ^ (prefixWord ++ tailWord_3385649).sum := by decide
  have hdescent : baseEnd_3385649 < baseStart_3385649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385681 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_3385681 : Nat := 118140960795 + 3385681 * 2 ^ 59
def prefixEnd_3385681 : Nat := 4983230072969 + 3 ^ 40 * 3385681 * 2
def baseEnd_3385681 : Nat := 1158987797196715494144695

theorem tailTrace_3385681 : CollatzResearch.WordTrace tailWord_3385681 prefixEnd_3385681 1158987797196715494144695 := by
  unfold tailWord_3385681
  simp only [CollatzResearch.WordTrace]
  refine ⟨123485930847263440124804897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82323953898175626749869931 123485930847263440124804897)
  ·
    refine ⟨92614448135447580093603673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123485930847263440124804897 92614448135447580093603673)
    ·
      refine ⟨69460836101585685070202755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92614448135447580093603673 69460836101585685070202755)
      ·
        refine ⟨104191254152378527605304133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69460836101585685070202755 104191254152378527605304133)
        ·
          refine ⟨19535860153570973925994525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104191254152378527605304133 19535860153570973925994525)
          ·
            refine ⟨7325947557589115222247947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19535860153570973925994525 7325947557589115222247947)
            ·
              refine ⟨10988921336383672833371921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7325947557589115222247947 10988921336383672833371921)
              ·
                refine ⟨8241691002287754625028941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10988921336383672833371921 8241691002287754625028941)
                ·
                  refine ⟨3090634125857907984385853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8241691002287754625028941 3090634125857907984385853)
                  ·
                    refine ⟨1158987797196715494144695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3090634125857907984385853 1158987797196715494144695)
                    ·
                      rfl

theorem cell22_3385681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_3385681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385681 prefixEnd_3385681 := by exact prefixLift 3385681
  have htrace : WordTrace (prefixWord ++ tailWord_3385681) baseStart_3385681 baseEnd_3385681 := by
    simpa [prefixWord, tailWord_3385681, baseEnd_3385681] using wordTrace_append hprefix tailTrace_3385681
  have hstable : (prefixWord ++ tailWord_3385681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385681).length < 2 ^ (prefixWord ++ tailWord_3385681).sum := by decide
  have hdescent : baseEnd_3385681 < baseStart_3385681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385709 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3385709 : Nat := 118140960795 + 3385709 * 2 ^ 59
def prefixEnd_3385709 : Nat := 4983230072969 + 3 ^ 40 * 3385709 * 2
def baseEnd_3385709 : Nat := 1158997382168932754444609

theorem tailTrace_3385709 : CollatzResearch.WordTrace tailWord_3385709 prefixEnd_3385709 1158997382168932754444609 := by
  unfold tailWord_3385709
  simp only [CollatzResearch.WordTrace]
  refine ⟨123486952091162000906824181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82324634727441333937882787 123486952091162000906824181)
  ·
    refine ⟨11576901758546437585014767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123486952091162000906824181 11576901758546437585014767)
    ·
      refine ⟨17365352637819656377522151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11576901758546437585014767 17365352637819656377522151)
      ·
        refine ⟨26048028956729484566283227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17365352637819656377522151 26048028956729484566283227)
        ·
          refine ⟨39072043435094226849424841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26048028956729484566283227 39072043435094226849424841)
          ·
            refine ⟨29304032576320670137068631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39072043435094226849424841 29304032576320670137068631)
            ·
              refine ⟨43956048864481005205602947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29304032576320670137068631 43956048864481005205602947)
              ·
                refine ⟨65934073296721507808404421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43956048864481005205602947 65934073296721507808404421)
                ·
                  refine ⟨12362638743135282714075829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65934073296721507808404421 12362638743135282714075829)
                  ·
                    refine ⟨1158997382168932754444609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12362638743135282714075829 1158997382168932754444609)
                    ·
                      rfl

theorem cell22_3385709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3385709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385709 prefixEnd_3385709 := by exact prefixLift 3385709
  have htrace : WordTrace (prefixWord ++ tailWord_3385709) baseStart_3385709 baseEnd_3385709 := by
    simpa [prefixWord, tailWord_3385709, baseEnd_3385709] using wordTrace_append hprefix tailTrace_3385709
  have hstable : (prefixWord ++ tailWord_3385709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385709).length < 2 ^ (prefixWord ++ tailWord_3385709).sum := by decide
  have hdescent : baseEnd_3385709 < baseStart_3385709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385724 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3385724 : Nat := 118140960795 + 3385724 * 2 ^ 59
def prefixEnd_3385724 : Nat := 4983230072969 + 3 ^ 40 * 3385724 * 2
def baseEnd_3385724 : Nat := 1159002516975477715319563

theorem tailTrace_3385724 : CollatzResearch.WordTrace tailWord_3385724 prefixEnd_3385724 1159002516975477715319563 := by
  unfold tailWord_3385724
  simp only [CollatzResearch.WordTrace]
  refine ⟨61743749593053829234310113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82324999457405105645746817 61743749593053829234310113)
  ·
    refine ⟨46307812194790371925732585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61743749593053829234310113 46307812194790371925732585)
    ·
      refine ⟨34730859146092778944299439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46307812194790371925732585 34730859146092778944299439)
      ·
        refine ⟨52096288719139168416449159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34730859146092778944299439 52096288719139168416449159)
        ·
          refine ⟨78144433078708752624673739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52096288719139168416449159 78144433078708752624673739)
          ·
            refine ⟨117216649618063128937010609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78144433078708752624673739 117216649618063128937010609)
            ·
              refine ⟨87912487213547346702757957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117216649618063128937010609 87912487213547346702757957)
              ·
                refine ⟨16483591352540127506767117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87912487213547346702757957 16483591352540127506767117)
                ·
                  refine ⟨6181346757202547815037669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16483591352540127506767117 6181346757202547815037669)
                  ·
                    refine ⟨1159002516975477715319563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6181346757202547815037669 1159002516975477715319563)
                    ·
                      rfl

theorem cell22_3385724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3385724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385724 prefixEnd_3385724 := by exact prefixLift 3385724
  have htrace : WordTrace (prefixWord ++ tailWord_3385724) baseStart_3385724 baseEnd_3385724 := by
    simpa [prefixWord, tailWord_3385724, baseEnd_3385724] using wordTrace_append hprefix tailTrace_3385724
  have hstable : (prefixWord ++ tailWord_3385724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385724).length < 2 ^ (prefixWord ++ tailWord_3385724).sum := by decide
  have hdescent : baseEnd_3385724 < baseStart_3385724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385739 : List Nat := [1, 1, 1, 1, 4, 4, 2, 2, 6]
def baseStart_3385739 : Nat := 118140960795 + 3385739 * 2 ^ 59
def prefixEnd_3385739 : Nat := 4983230072969 + 3 ^ 40 * 3385739 * 2
def baseEnd_3385739 : Nat := 386335883927340892064839

theorem tailTrace_3385739 : CollatzResearch.WordTrace tailWord_3385739 prefixEnd_3385739 386335883927340892064839 := by
  unfold tailWord_3385739
  simp only [CollatzResearch.WordTrace]
  refine ⟨123488046281053316030416271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82325364187368877353610847 123488046281053316030416271)
  ·
    refine ⟨185232069421579974045624407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123488046281053316030416271 185232069421579974045624407)
    ·
      refine ⟨277848104132369961068436611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185232069421579974045624407 277848104132369961068436611)
      ·
        refine ⟨416772156198554941602654917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277848104132369961068436611 416772156198554941602654917)
        ·
          refine ⟨78144779287229051550497797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 416772156198554941602654917 78144779287229051550497797)
          ·
            refine ⟨14652146116355447165718337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78144779287229051550497797 14652146116355447165718337)
            ·
              refine ⟨10989109587266585374288753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14652146116355447165718337 10989109587266585374288753)
              ·
                refine ⟨8241832190449939030716565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10989109587266585374288753 8241832190449939030716565)
                ·
                  refine ⟨386335883927340892064839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8241832190449939030716565 386335883927340892064839)
                  ·
                    rfl

theorem cell22_3385739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 2, 6].length) (baseStart_3385739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385739 prefixEnd_3385739 := by exact prefixLift 3385739
  have htrace : WordTrace (prefixWord ++ tailWord_3385739) baseStart_3385739 baseEnd_3385739 := by
    simpa [prefixWord, tailWord_3385739, baseEnd_3385739] using wordTrace_append hprefix tailTrace_3385739
  have hstable : (prefixWord ++ tailWord_3385739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385739).length < 2 ^ (prefixWord ++ tailWord_3385739).sum := by decide
  have hdescent : baseEnd_3385739 < baseStart_3385739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385891 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 6]
def baseStart_3385891 : Nat := 118140960795 + 3385891 * 2 ^ 59
def prefixEnd_3385891 : Nat := 4983230072969 + 3 ^ 40 * 3385891 * 2
def baseEnd_3385891 : Nat := 386353228162781648798017

theorem tailTrace_3385891 : CollatzResearch.WordTrace tailWord_3385891 prefixEnd_3385891 386353228162781648798017 := by
  unfold tailWord_3385891
  simp only [CollatzResearch.WordTrace]
  refine ⟨123493590176502645989949527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82329060117668430659966351 123493590176502645989949527)
  ·
    refine ⟨185240385264753968984924291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123493590176502645989949527 185240385264753968984924291)
    ·
      refine ⟨277860577897130953477386437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185240385264753968984924291 277860577897130953477386437)
      ·
        refine ⟨52098858355712053777009957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277860577897130953477386437 52098858355712053777009957)
        ·
          refine ⟨9768535941696010083189367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52098858355712053777009957 9768535941696010083189367)
          ·
            refine ⟨14652803912544015124784051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768535941696010083189367 14652803912544015124784051)
            ·
              refine ⟨21979205868816022687176077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652803912544015124784051 21979205868816022687176077)
              ·
                refine ⟨8242202200806008507691029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21979205868816022687176077 8242202200806008507691029)
                ·
                  refine ⟨386353228162781648798017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8242202200806008507691029 386353228162781648798017)
                  ·
                    rfl

theorem cell22_3385891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 6].length) (baseStart_3385891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385891 prefixEnd_3385891 := by exact prefixLift 3385891
  have htrace : WordTrace (prefixWord ++ tailWord_3385891) baseStart_3385891 baseEnd_3385891 := by
    simpa [prefixWord, tailWord_3385891, baseEnd_3385891] using wordTrace_append hprefix tailTrace_3385891
  have hstable : (prefixWord ++ tailWord_3385891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385891).length < 2 ^ (prefixWord ++ tailWord_3385891).sum := by decide
  have hdescent : baseEnd_3385891 < baseStart_3385891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385910 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3385910 : Nat := 118140960795 + 3385910 * 2 ^ 59
def prefixEnd_3385910 : Nat := 4983230072969 + 3 ^ 40 * 3385910 * 2
def baseEnd_3385910 : Nat := 1159066188576635230168993

theorem tailTrace_3385910 : CollatzResearch.WordTrace tailWord_3385910 prefixEnd_3385910 1159066188576635230168993 := by
  unfold tailWord_3385910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718392697714613264680699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82329522108955874823260789 7718392697714613264680699)
  ·
    refine ⟨11577589046571919897021049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7718392697714613264680699 11577589046571919897021049)
    ·
      refine ⟨8683191784928939922765787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11577589046571919897021049 8683191784928939922765787)
      ·
        refine ⟨13024787677393409884148681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8683191784928939922765787 13024787677393409884148681)
        ·
          refine ⟨9768590758045057413111511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13024787677393409884148681 9768590758045057413111511)
          ·
            refine ⟨14652886137067586119667267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9768590758045057413111511 14652886137067586119667267)
            ·
              refine ⟨21979329205601379179500901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14652886137067586119667267 21979329205601379179500901)
              ·
                refine ⟨4121124226050258596156419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21979329205601379179500901 4121124226050258596156419)
                ·
                  refine ⟨6181686339075387894234629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121124226050258596156419 6181686339075387894234629)
                  ·
                    refine ⟨1159066188576635230168993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6181686339075387894234629 1159066188576635230168993)
                    ·
                      rfl

theorem cell22_3385910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3385910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385910 prefixEnd_3385910 := by exact prefixLift 3385910
  have htrace : WordTrace (prefixWord ++ tailWord_3385910) baseStart_3385910 baseEnd_3385910 := by
    simpa [prefixWord, tailWord_3385910, baseEnd_3385910] using wordTrace_append hprefix tailTrace_3385910
  have hstable : (prefixWord ++ tailWord_3385910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385910).length < 2 ^ (prefixWord ++ tailWord_3385910).sum := by decide
  have hdescent : baseEnd_3385910 < baseStart_3385910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385925 : List Nat := [1, 3, 1, 1, 1, 7, 1, 3, 4]
def baseStart_3385925 : Nat := 118140960795 + 3385925 * 2 ^ 59
def prefixEnd_3385925 : Nat := 4983230072969 + 3 ^ 40 * 3385925 * 2
def baseEnd_3385925 : Nat := 386357107794393397014649

theorem tailTrace_3385925 : CollatzResearch.WordTrace tailWord_3385925 prefixEnd_3385925 386357107794393397014649 := by
  unfold tailWord_3385925
  simp only [CollatzResearch.WordTrace]
  refine ⟨123494830258379469796687229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82329886838919646531124819 123494830258379469796687229)
  ·
    refine ⟨46310561346892301173757711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123494830258379469796687229 46310561346892301173757711)
    ·
      refine ⟨69465842020338451760636567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46310561346892301173757711 69465842020338451760636567)
      ·
        refine ⟨104198763030507677640954851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69465842020338451760636567 104198763030507677640954851)
        ·
          refine ⟨156298144545761516461432277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104198763030507677640954851 156298144545761516461432277)
          ·
            refine ⟨3663237762791285542064819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 156298144545761516461432277 3663237762791285542064819)
            ·
              refine ⟨5494856644186928313097229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663237762791285542064819 5494856644186928313097229)
              ·
                refine ⟨2060571241570098117411461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5494856644186928313097229 2060571241570098117411461)
                ·
                  refine ⟨386357107794393397014649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060571241570098117411461 386357107794393397014649)
                  ·
                    rfl

theorem cell22_3385925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_3385925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385925 prefixEnd_3385925 := by exact prefixLift 3385925
  have htrace : WordTrace (prefixWord ++ tailWord_3385925) baseStart_3385925 baseEnd_3385925 := by
    simpa [prefixWord, tailWord_3385925, baseEnd_3385925] using wordTrace_append hprefix tailTrace_3385925
  have hstable : (prefixWord ++ tailWord_3385925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385925).length < 2 ^ (prefixWord ++ tailWord_3385925).sum := by decide
  have hdescent : baseEnd_3385925 < baseStart_3385925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3385938 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_3385938 : Nat := 118140960795 + 3385938 * 2 ^ 59
def prefixEnd_3385938 : Nat := 4983230072969 + 3 ^ 40 * 3385938 * 2
def baseEnd_3385938 : Nat := 1159075773548852490468907

theorem tailTrace_3385938 : CollatzResearch.WordTrace tailWord_3385938 prefixEnd_3385938 1159075773548852490468907 := by
  unfold tailWord_3385938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30873826101833093254227617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82330202938221582011273645 30873826101833093254227617)
  ·
    refine ⟨23155369576374819940670713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30873826101833093254227617 23155369576374819940670713)
    ·
      refine ⟨17366527182281114955503035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23155369576374819940670713 17366527182281114955503035)
      ·
        refine ⟨26049790773421672433254553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17366527182281114955503035 26049790773421672433254553)
        ·
          refine ⟨19537343080066254324940915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26049790773421672433254553 19537343080066254324940915)
          ·
            refine ⟨29306014620099381487411373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19537343080066254324940915 29306014620099381487411373)
            ·
              refine ⟨10989755482537268057779265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29306014620099381487411373 10989755482537268057779265)
              ·
                refine ⟨8242316611902951043334449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10989755482537268057779265 8242316611902951043334449)
                ·
                  refine ⟨6181737458927213282500837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8242316611902951043334449 6181737458927213282500837)
                  ·
                    refine ⟨1159075773548852490468907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6181737458927213282500837 1159075773548852490468907)
                    ·
                      rfl

theorem cell22_3385938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_3385938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3385938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3385938 prefixEnd_3385938 := by exact prefixLift 3385938
  have htrace : WordTrace (prefixWord ++ tailWord_3385938) baseStart_3385938 baseEnd_3385938 := by
    simpa [prefixWord, tailWord_3385938, baseEnd_3385938] using wordTrace_append hprefix tailTrace_3385938
  have hstable : (prefixWord ++ tailWord_3385938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3385938).length < 2 ^ (prefixWord ++ tailWord_3385938).sum := by decide
  have hdescent : baseEnd_3385938 < baseStart_3385938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3385938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386045 : List Nat := [1, 4, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_3386045 : Nat := 118140960795 + 3386045 * 2 ^ 59
def prefixEnd_3386045 : Nat := 4983230072969 + 3 ^ 40 * 3386045 * 2
def baseEnd_3386045 : Nat := 1159112401835539878043579

theorem tailTrace_3386045 : CollatzResearch.WordTrace tailWord_3386045 prefixEnd_3386045 1159112401835539878043579 := by
  unfold tailWord_3386045
  simp only [CollatzResearch.WordTrace]
  refine ⟨123499207017944730291055589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82332804678629820194037059 123499207017944730291055589)
  ·
    refine ⟨23156101315864636929572923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123499207017944730291055589 23156101315864636929572923)
    ·
      refine ⟨34734151973796955394359385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23156101315864636929572923 34734151973796955394359385)
      ·
        refine ⟨26050613980347716545769539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34734151973796955394359385 26050613980347716545769539)
        ·
          refine ⟨39075920970521574818654309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26050613980347716545769539 39075920970521574818654309)
          ·
            refine ⟨7326735181972795278497683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39075920970521574818654309 7326735181972795278497683)
            ·
              refine ⟨10990102772959192917746525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7326735181972795278497683 10990102772959192917746525)
              ·
                refine ⟨4121288539859697344154947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10990102772959192917746525 4121288539859697344154947)
                ·
                  refine ⟨6181932809789546016232421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4121288539859697344154947 6181932809789546016232421)
                  ·
                    refine ⟨1159112401835539878043579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6181932809789546016232421 1159112401835539878043579)
                    ·
                      rfl

theorem cell22_3386045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_3386045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386045 prefixEnd_3386045 := by exact prefixLift 3386045
  have htrace : WordTrace (prefixWord ++ tailWord_3386045) baseStart_3386045 baseEnd_3386045 := by
    simpa [prefixWord, tailWord_3386045, baseEnd_3386045] using wordTrace_append hprefix tailTrace_3386045
  have hstable : (prefixWord ++ tailWord_3386045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386045).length < 2 ^ (prefixWord ++ tailWord_3386045).sum := by decide
  have hdescent : baseEnd_3386045 < baseStart_3386045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386049 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 5]
def baseStart_3386049 : Nat := 118140960795 + 3386049 * 2 ^ 59
def prefixEnd_3386049 : Nat := 4983230072969 + 3 ^ 40 * 3386049 * 2
def baseEnd_3386049 : Nat := 386371257039095066981189

theorem tailTrace_3386049 : CollatzResearch.WordTrace tailWord_3386049 prefixEnd_3386049 386371257039095066981189 := by
  unfold tailWord_3386049
  simp only [CollatzResearch.WordTrace]
  refine ⟨123499352909930238974201201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82332901939953492649467467 123499352909930238974201201)
  ·
    refine ⟨92624514682447679230650901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123499352909930238974201201 92624514682447679230650901)
    ·
      refine ⟨4341774125739734963936761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92624514682447679230650901 4341774125739734963936761)
      ·
        refine ⟨3256330594304801222952571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4341774125739734963936761 3256330594304801222952571)
        ·
          refine ⟨4884495891457201834428857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256330594304801222952571 4884495891457201834428857)
          ·
            refine ⟨3663371918592901375821643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4884495891457201834428857 3663371918592901375821643)
            ·
              refine ⟨5495057877889352063732465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663371918592901375821643 5495057877889352063732465)
              ·
                refine ⟨4121293408417014047799349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495057877889352063732465 4121293408417014047799349)
                ·
                  refine ⟨386371257039095066981189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121293408417014047799349 386371257039095066981189)
                  ·
                    rfl

theorem cell22_3386049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_3386049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386049 prefixEnd_3386049 := by exact prefixLift 3386049
  have htrace : WordTrace (prefixWord ++ tailWord_3386049) baseStart_3386049 baseEnd_3386049 := by
    simpa [prefixWord, tailWord_3386049, baseEnd_3386049] using wordTrace_append hprefix tailTrace_3386049
  have hstable : (prefixWord ++ tailWord_3386049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386049).length < 2 ^ (prefixWord ++ tailWord_3386049).sum := by decide
  have hdescent : baseEnd_3386049 < baseStart_3386049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386060 : List Nat := [2, 2, 1, 5, 1, 2, 2, 1, 6]
def baseStart_3386060 : Nat := 118140960795 + 3386060 * 2 ^ 59
def prefixEnd_3386060 : Nat := 4983230072969 + 3 ^ 40 * 3386060 * 2
def baseEnd_3386060 : Nat := 386372512214028279639511

theorem tailTrace_3386060 : CollatzResearch.WordTrace tailWord_3386060 prefixEnd_3386060 386372512214028279639511 := by
  unfold tailWord_3386060
  simp only [CollatzResearch.WordTrace]
  refine ⟨61749877056445193926425817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82333169408593591901901089 61749877056445193926425817)
  ·
    refine ⟨46312407792333895444819363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61749877056445193926425817 46312407792333895444819363)
    ·
      refine ⟨69468611688500843167229045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46312407792333895444819363 69468611688500843167229045)
      ·
        refine ⟨6512682345796954046927723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69468611688500843167229045 6512682345796954046927723)
        ·
          refine ⟨9769023518695431070391585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6512682345796954046927723 9769023518695431070391585)
          ·
            refine ⟨7326767639021573302793689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9769023518695431070391585 7326767639021573302793689)
            ·
              refine ⟨5495075729266179977095267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7326767639021573302793689 5495075729266179977095267)
              ·
                refine ⟨8242613593899269965642901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495075729266179977095267 8242613593899269965642901)
                ·
                  refine ⟨386372512214028279639511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8242613593899269965642901 386372512214028279639511)
                  ·
                    rfl

theorem cell22_3386060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_3386060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386060 prefixEnd_3386060 := by exact prefixLift 3386060
  have htrace : WordTrace (prefixWord ++ tailWord_3386060) baseStart_3386060 baseEnd_3386060 := by
    simpa [prefixWord, tailWord_3386060, baseEnd_3386060] using wordTrace_append hprefix tailTrace_3386060
  have hstable : (prefixWord ++ tailWord_3386060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386060).length < 2 ^ (prefixWord ++ tailWord_3386060).sum := by decide
  have hdescent : baseEnd_3386060 < baseStart_3386060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386212 : List Nat := [2, 3, 1, 1, 4, 1, 1, 5, 4]
def baseStart_3386212 : Nat := 118140960795 + 3386212 * 2 ^ 59
def prefixEnd_3386212 : Nat := 4983230072969 + 3 ^ 40 * 3386212 * 2
def baseEnd_3386212 : Nat := 386389856449469036372689

theorem tailTrace_3386212 : CollatzResearch.WordTrace tailWord_3386212 prefixEnd_3386212 386389856449469036372689 := by
  unfold tailWord_3386212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61752649004169858906192445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82336865338893145208256593 61752649004169858906192445)
  ·
    refine ⟨23157243376563697089822167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61752649004169858906192445 23157243376563697089822167)
    ·
      refine ⟨34735865064845545634733251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23157243376563697089822167 34735865064845545634733251)
      ·
        refine ⟨52103797597268318452099877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34735865064845545634733251 52103797597268318452099877)
        ·
          refine ⟨9769462049487809709768727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52103797597268318452099877 9769462049487809709768727)
          ·
            refine ⟨14654193074231714564653091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9769462049487809709768727 14654193074231714564653091)
            ·
              refine ⟨21981289611347571846979637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14654193074231714564653091 21981289611347571846979637)
              ·
                refine ⟨2060745901063834860654341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21981289611347571846979637 2060745901063834860654341)
                ·
                  refine ⟨386389856449469036372689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060745901063834860654341 386389856449469036372689)
                  ·
                    rfl

theorem cell22_3386212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_3386212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386212 prefixEnd_3386212 := by exact prefixLift 3386212
  have htrace : WordTrace (prefixWord ++ tailWord_3386212) baseStart_3386212 baseEnd_3386212 := by
    simpa [prefixWord, tailWord_3386212, baseEnd_3386212] using wordTrace_append hprefix tailTrace_3386212
  have hstable : (prefixWord ++ tailWord_3386212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386212).length < 2 ^ (prefixWord ++ tailWord_3386212).sum := by decide
  have hdescent : baseEnd_3386212 < baseStart_3386212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386227 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 2, 3]
def baseStart_3386227 : Nat := 118140960795 + 3386227 * 2 ^ 59
def prefixEnd_3386227 : Nat := 4983230072969 + 3 ^ 40 * 3386227 * 2
def baseEnd_3386227 : Nat := 1159174704154952069993021

theorem tailTrace_3386227 : CollatzResearch.WordTrace tailWord_3386227 prefixEnd_3386227 1159174704154952069993021 := by
  unfold tailWord_3386227
  simp only [CollatzResearch.WordTrace]
  refine ⟨123505845103285375374180935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82337230068856916916120623 123505845103285375374180935)
  ·
    refine ⟨185258767654928063061271403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123505845103285375374180935 185258767654928063061271403)
    ·
      refine ⟨277888151482392094591907105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185258767654928063061271403 277888151482392094591907105)
      ·
        refine ⟨208416113611794070943930329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277888151482392094591907105 208416113611794070943930329)
        ·
          refine ⟨156312085208845553207947747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208416113611794070943930329 156312085208845553207947747)
          ·
            refine ⟨234468127813268329811921621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156312085208845553207947747 234468127813268329811921621)
            ·
              refine ⟨5495346745623476479966913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 234468127813268329811921621 5495346745623476479966913)
              ·
                refine ⟨4121510059217607359975185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5495346745623476479966913 4121510059217607359975185)
                ·
                  refine ⟨3091132544413205519981389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121510059217607359975185 3091132544413205519981389)
                  ·
                    refine ⟨1159174704154952069993021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091132544413205519981389 1159174704154952069993021)
                    ·
                      rfl

theorem cell22_3386227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 3].length) (baseStart_3386227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386227 prefixEnd_3386227 := by exact prefixLift 3386227
  have htrace : WordTrace (prefixWord ++ tailWord_3386227) baseStart_3386227 baseEnd_3386227 := by
    simpa [prefixWord, tailWord_3386227, baseEnd_3386227] using wordTrace_append hprefix tailTrace_3386227
  have hstable : (prefixWord ++ tailWord_3386227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386227).length < 2 ^ (prefixWord ++ tailWord_3386227).sum := by decide
  have hdescent : baseEnd_3386227 < baseStart_3386227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386302 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_3386302 : Nat := 118140960795 + 3386302 * 2 ^ 59
def prefixEnd_3386302 : Nat := 4983230072969 + 3 ^ 40 * 3386302 * 2
def baseEnd_3386302 : Nat := 386400126062558958122597

theorem tailTrace_3386302 : CollatzResearch.WordTrace tailWord_3386302 prefixEnd_3386302 386400126062558958122597 := by
  unfold tailWord_3386302
  simp only [CollatzResearch.WordTrace]
  refine ⟨15438572572251707897895145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82339053718675775455440773 15438572572251707897895145)
  ·
    refine ⟨11578929429188780923421359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15438572572251707897895145 11578929429188780923421359)
    ·
      refine ⟨17368394143783171385132039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11578929429188780923421359 17368394143783171385132039)
      ·
        refine ⟨26052591215674757077698059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17368394143783171385132039 26052591215674757077698059)
        ·
          refine ⟨39078886823512135616547089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26052591215674757077698059 39078886823512135616547089)
          ·
            refine ⟨29309165117634101712410317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39078886823512135616547089 29309165117634101712410317)
            ·
              refine ⟨10990936919112788142153869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29309165117634101712410317 10990936919112788142153869)
              ·
                refine ⟨4121601344667295553307701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10990936919112788142153869 4121601344667295553307701)
                ·
                  refine ⟨386400126062558958122597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121601344667295553307701 386400126062558958122597)
                  ·
                    rfl

theorem cell22_3386302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_3386302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386302 prefixEnd_3386302 := by exact prefixLift 3386302
  have htrace : WordTrace (prefixWord ++ tailWord_3386302) baseStart_3386302 baseEnd_3386302 := by
    simpa [prefixWord, tailWord_3386302, baseEnd_3386302] using wordTrace_append hprefix tailTrace_3386302
  have hstable : (prefixWord ++ tailWord_3386302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386302).length < 2 ^ (prefixWord ++ tailWord_3386302).sum := by decide
  have hdescent : baseEnd_3386302 < baseStart_3386302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386310 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3386310 : Nat := 118140960795 + 3386310 * 2 ^ 59
def prefixEnd_3386310 : Nat := 4983230072969 + 3 ^ 40 * 3386310 * 2
def baseEnd_3386310 : Nat := 1159203116751167520167767

theorem tailTrace_3386310 : CollatzResearch.WordTrace tailWord_3386310 prefixEnd_3386310 1159203116751167520167767 := by
  unfold tailWord_3386310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3859652261312021267170387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82339248241323120366301589 3859652261312021267170387)
  ·
    refine ⟨5789478391968031900755581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3859652261312021267170387 5789478391968031900755581)
    ·
      refine ⟨2171054396988011962783343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5789478391968031900755581 2171054396988011962783343)
      ·
        refine ⟨3256581595482017944175015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171054396988011962783343 3256581595482017944175015)
        ·
          refine ⟨4884872393223026916262523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256581595482017944175015 4884872393223026916262523)
          ·
            refine ⟨7327308589834540374393785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4884872393223026916262523 7327308589834540374393785)
            ·
              refine ⟨5495481442375905280795339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7327308589834540374393785 5495481442375905280795339)
              ·
                refine ⟨8243222163563857921193009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495481442375905280795339 8243222163563857921193009)
                ·
                  refine ⟨6182416622672893440894757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243222163563857921193009 6182416622672893440894757)
                  ·
                    refine ⟨1159203116751167520167767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182416622672893440894757 1159203116751167520167767)
                    ·
                      rfl

theorem cell22_3386310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3386310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386310 prefixEnd_3386310 := by exact prefixLift 3386310
  have htrace : WordTrace (prefixWord ++ tailWord_3386310) baseStart_3386310 baseEnd_3386310 := by
    simpa [prefixWord, tailWord_3386310, baseEnd_3386310] using wordTrace_append hprefix tailTrace_3386310
  have hstable : (prefixWord ++ tailWord_3386310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386310).length < 2 ^ (prefixWord ++ tailWord_3386310).sum := by decide
  have hdescent : baseEnd_3386310 < baseStart_3386310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386360 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 6]
def baseStart_3386360 : Nat := 118140960795 + 3386360 * 2 ^ 59
def prefixEnd_3386360 : Nat := 4983230072969 + 3 ^ 40 * 3386360 * 2
def baseEnd_3386360 : Nat := 1159220232772984056417613

theorem tailTrace_3386360 : CollatzResearch.WordTrace tailWord_3386360 prefixEnd_3386360 1159220232772984056417613 := by
  unfold tailWord_3386360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61755348005901769544386267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82340464007869026059181689 61755348005901769544386267)
  ·
    refine ⟨92633022008852654316579401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61755348005901769544386267 92633022008852654316579401)
    ·
      refine ⟨69474766506639490737434551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92633022008852654316579401 69474766506639490737434551)
      ·
        refine ⟨104212149759959236106151827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69474766506639490737434551 104212149759959236106151827)
        ·
          refine ⟨156318224639938854159227741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104212149759959236106151827 156318224639938854159227741)
          ·
            refine ⟨58619334239977070309710403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156318224639938854159227741 58619334239977070309710403)
            ·
              refine ⟨87929001359965605464565605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58619334239977070309710403 87929001359965605464565605)
              ·
                refine ⟨16486687754993551024606051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87929001359965605464565605 16486687754993551024606051)
                ·
                  refine ⟨24730031632490326536909077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16486687754993551024606051 24730031632490326536909077)
                  ·
                    refine ⟨1159220232772984056417613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24730031632490326536909077 1159220232772984056417613)
                    ·
                      rfl

theorem cell22_3386360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_3386360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386360 prefixEnd_3386360 := by exact prefixLift 3386360
  have htrace : WordTrace (prefixWord ++ tailWord_3386360) baseStart_3386360 baseEnd_3386360 := by
    simpa [prefixWord, tailWord_3386360, baseEnd_3386360] using wordTrace_append hprefix tailTrace_3386360
  have hstable : (prefixWord ++ tailWord_3386360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386360).length < 2 ^ (prefixWord ++ tailWord_3386360).sum := by decide
  have hdescent : baseEnd_3386360 < baseStart_3386360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386424 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 3, 3]
def baseStart_3386424 : Nat := 118140960795 + 3386424 * 2 ^ 59
def prefixEnd_3386424 : Nat := 4983230072969 + 3 ^ 40 * 3386424 * 2
def baseEnd_3386424 : Nat := 1159242141280909222817417

theorem tailTrace_3386424 : CollatzResearch.WordTrace tailWord_3386424 prefixEnd_3386424 1159242141280909222817417 := by
  unfold tailWord_3386424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61756515141785839009551163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82342020189047785346068217 61756515141785839009551163)
  ·
    refine ⟨92634772712678758514326745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61756515141785839009551163 92634772712678758514326745)
    ·
      refine ⟨69476079534509068885745059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92634772712678758514326745 69476079534509068885745059)
      ·
        refine ⟨104214119301763603328617589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69476079534509068885745059 104214119301763603328617589)
        ·
          refine ⟨9770073684540337812057899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104214119301763603328617589 9770073684540337812057899)
          ·
            refine ⟨14655110526810506718086849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770073684540337812057899 14655110526810506718086849)
            ·
              refine ⟨10991332895107880038565137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14655110526810506718086849 10991332895107880038565137)
              ·
                refine ⟨8243499671330910028923853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10991332895107880038565137 8243499671330910028923853)
                ·
                  refine ⟨3091312376749091260846445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8243499671330910028923853 3091312376749091260846445)
                  ·
                    refine ⟨1159242141280909222817417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091312376749091260846445 1159242141280909222817417)
                    ·
                      rfl

theorem cell22_3386424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 3].length) (baseStart_3386424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386424 prefixEnd_3386424 := by exact prefixLift 3386424
  have htrace : WordTrace (prefixWord ++ tailWord_3386424) baseStart_3386424 baseEnd_3386424 := by
    simpa [prefixWord, tailWord_3386424, baseEnd_3386424] using wordTrace_append hprefix tailTrace_3386424
  have hstable : (prefixWord ++ tailWord_3386424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386424).length < 2 ^ (prefixWord ++ tailWord_3386424).sum := by decide
  have hdescent : baseEnd_3386424 < baseStart_3386424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386452 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3386452 : Nat := 118140960795 + 3386452 * 2 ^ 59
def prefixEnd_3386452 : Nat := 4983230072969 + 3 ^ 40 * 3386452 * 2
def baseEnd_3386452 : Nat := 1159251726253126483117331

theorem tailTrace_3386452 : CollatzResearch.WordTrace tailWord_3386452 prefixEnd_3386452 1159251726253126483117331 := by
  unfold tailWord_3386452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61757025763735119400560805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82342701018313492534081073 61757025763735119400560805)
  ·
    refine ⟨11579442330700334887605151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61757025763735119400560805 11579442330700334887605151)
    ·
      refine ⟨17369163496050502331407727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11579442330700334887605151 17369163496050502331407727)
      ·
        refine ⟨26053745244075753497111591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17369163496050502331407727 26053745244075753497111591)
        ·
          refine ⟨39080617866113630245667387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26053745244075753497111591 39080617866113630245667387)
          ·
            refine ⟨58620926799170445368501081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39080617866113630245667387 58620926799170445368501081)
            ·
              refine ⟨43965695099377834026375811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58620926799170445368501081 43965695099377834026375811)
              ·
                refine ⟨65948542649066751039563717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43965695099377834026375811 65948542649066751039563717)
                ·
                  refine ⟨12365351746700015819918197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65948542649066751039563717 12365351746700015819918197)
                  ·
                    refine ⟨1159251726253126483117331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12365351746700015819918197 1159251726253126483117331)
                    ·
                      rfl

theorem cell22_3386452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3386452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386452 prefixEnd_3386452 := by exact prefixLift 3386452
  have htrace : WordTrace (prefixWord ++ tailWord_3386452) baseStart_3386452 baseEnd_3386452 := by
    simpa [prefixWord, tailWord_3386452, baseEnd_3386452] using wordTrace_append hprefix tailTrace_3386452
  have hstable : (prefixWord ++ tailWord_3386452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386452).length < 2 ^ (prefixWord ++ tailWord_3386452).sum := by decide
  have hdescent : baseEnd_3386452 < baseStart_3386452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386467 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 3, 4]
def baseStart_3386467 : Nat := 118140960795 + 3386467 * 2 ^ 59
def prefixEnd_3386467 : Nat := 4983230072969 + 3 ^ 40 * 3386467 * 2
def baseEnd_3386467 : Nat := 1159256861059671443992285

theorem tailTrace_3386467 : CollatzResearch.WordTrace tailWord_3386467 prefixEnd_3386467 1159256861059671443992285 := by
  unfold tailWord_3386467
  simp only [CollatzResearch.WordTrace]
  refine ⟨123514598622415896362917655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82343065748277264241945103 123514598622415896362917655)
  ·
    refine ⟨185271897933623844544376483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123514598622415896362917655 185271897933623844544376483)
    ·
      refine ⟨277907846900435766816564725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185271897933623844544376483 277907846900435766816564725)
      ·
        refine ⟨26053860646915853139052943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277907846900435766816564725 26053860646915853139052943)
        ·
          refine ⟨39080790970373779708579415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26053860646915853139052943 39080790970373779708579415)
          ·
            refine ⟨58621186455560669562869123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39080790970373779708579415 58621186455560669562869123)
            ·
              refine ⟨87931779683341004344303685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58621186455560669562869123 87931779683341004344303685)
              ·
                refine ⟨16487208690626438314556941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87931779683341004344303685 16487208690626438314556941)
                ·
                  refine ⟨6182703258984914367958853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16487208690626438314556941 6182703258984914367958853)
                  ·
                    refine ⟨1159256861059671443992285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182703258984914367958853 1159256861059671443992285)
                    ·
                      rfl

theorem cell22_3386467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_3386467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386467 prefixEnd_3386467 := by exact prefixLift 3386467
  have htrace : WordTrace (prefixWord ++ tailWord_3386467) baseStart_3386467 baseEnd_3386467 := by
    simpa [prefixWord, tailWord_3386467, baseEnd_3386467] using wordTrace_append hprefix tailTrace_3386467
  have hstable : (prefixWord ++ tailWord_3386467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386467).length < 2 ^ (prefixWord ++ tailWord_3386467).sum := by decide
  have hdescent : baseEnd_3386467 < baseStart_3386467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386471 : List Nat := [1, 1, 5, 1, 1, 5, 2, 1, 5]
def baseStart_3386471 : Nat := 118140960795 + 3386471 * 2 ^ 59
def prefixEnd_3386471 : Nat := 4983230072969 + 3 ^ 40 * 3386471 * 2
def baseEnd_3386471 : Nat := 386419410113805588964091

theorem tailTrace_3386471 : CollatzResearch.WordTrace tailWord_3386471 prefixEnd_3386471 386419410113805588964091 := by
  unfold tailWord_3386471
  simp only [CollatzResearch.WordTrace]
  refine ⟨123514744514401405046063267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82343163009600936697375511 123514744514401405046063267)
  ·
    refine ⟨185272116771602107569094901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123514744514401405046063267 185272116771602107569094901)
    ·
      refine ⟨17369260947337697584602647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185272116771602107569094901 17369260947337697584602647)
      ·
        refine ⟨26053891421006546376903971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17369260947337697584602647 26053891421006546376903971)
        ·
          refine ⟨39080837131509819565355957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26053891421006546376903971 39080837131509819565355957)
          ·
            refine ⟨3663828481079045584252121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39080837131509819565355957 3663828481079045584252121)
            ·
              refine ⟨2747871360809284188189091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3663828481079045584252121 2747871360809284188189091)
              ·
                refine ⟨4121807041213926282283637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747871360809284188189091 4121807041213926282283637)
                ·
                  refine ⟨386419410113805588964091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4121807041213926282283637 386419410113805588964091)
                  ·
                    rfl

theorem cell22_3386471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 2, 1, 5].length) (baseStart_3386471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386471 prefixEnd_3386471 := by exact prefixLift 3386471
  have htrace : WordTrace (prefixWord ++ tailWord_3386471) baseStart_3386471 baseEnd_3386471 := by
    simpa [prefixWord, tailWord_3386471, baseEnd_3386471] using wordTrace_append hprefix tailTrace_3386471
  have hstable : (prefixWord ++ tailWord_3386471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386471).length < 2 ^ (prefixWord ++ tailWord_3386471).sum := by decide
  have hdescent : baseEnd_3386471 < baseStart_3386471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386482 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_3386482 : Nat := 118140960795 + 3386482 * 2 ^ 59
def prefixEnd_3386482 : Nat := 4983230072969 + 3 ^ 40 * 3386482 * 2
def baseEnd_3386482 : Nat := 386420665288738801622413

theorem tailTrace_3386482 : CollatzResearch.WordTrace tailWord_3386482 prefixEnd_3386482 386420665288738801622413 := by
  unfold tailWord_3386482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30878786429340388481178425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82343430478241035949809133 30878786429340388481178425)
  ·
    refine ⟨23159089822005291360883819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30878786429340388481178425 23159089822005291360883819)
    ·
      refine ⟨34738634733007937041325729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23159089822005291360883819 34738634733007937041325729)
      ·
        refine ⟨26053976049755952780994297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34738634733007937041325729 26053976049755952780994297)
        ·
          refine ⟨19540482037316964585745723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26053976049755952780994297 19540482037316964585745723)
          ·
            refine ⟨29310723055975446878618585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19540482037316964585745723 29310723055975446878618585)
            ·
              refine ⟨21983042291981585158963939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29310723055975446878618585 21983042291981585158963939)
              ·
                refine ⟨32974563437972377738445909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21983042291981585158963939 32974563437972377738445909)
                ·
                  refine ⟨386420665288738801622413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32974563437972377738445909 386420665288738801622413)
                  ·
                    rfl

theorem cell22_3386482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_3386482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386482 prefixEnd_3386482 := by exact prefixLift 3386482
  have htrace : WordTrace (prefixWord ++ tailWord_3386482) baseStart_3386482 baseEnd_3386482 := by
    simpa [prefixWord, tailWord_3386482, baseEnd_3386482] using wordTrace_append hprefix tailTrace_3386482
  have hstable : (prefixWord ++ tailWord_3386482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386482).length < 2 ^ (prefixWord ++ tailWord_3386482).sum := by decide
  have hdescent : baseEnd_3386482 < baseStart_3386482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386499 : List Nat := [1, 1, 1, 3, 3, 2, 2, 5, 4]
def baseStart_3386499 : Nat := 118140960795 + 3386499 * 2 ^ 59
def prefixEnd_3386499 : Nat := 4983230072969 + 3 ^ 40 * 3386499 * 2
def baseEnd_3386499 : Nat := 386422605104544675730729

theorem tailTrace_3386499 : CollatzResearch.WordTrace tailWord_3386499 prefixEnd_3386499 386422605104544675730729 := by
  unfold tailWord_3386499
  simp only [CollatzResearch.WordTrace]
  refine ⟨123515765758299965828082551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82343843838866643885388367 123515765758299965828082551)
  ·
    refine ⟨185273648637449948742123827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123515765758299965828082551 185273648637449948742123827)
    ·
      refine ⟨277910472956174923113185741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185273648637449948742123827 277910472956174923113185741)
      ·
        refine ⟨104216427358565596167444653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277910472956174923113185741 104216427358565596167444653)
        ·
          refine ⟨39081160259462098562791745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104216427358565596167444653 39081160259462098562791745)
          ·
            refine ⟨29310870194596573922093809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39081160259462098562791745 29310870194596573922093809)
            ·
              refine ⟨21983152645947430441570357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29310870194596573922093809 21983152645947430441570357)
              ·
                refine ⟨2060920560557571603897221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21983152645947430441570357 2060920560557571603897221)
                ·
                  refine ⟨386422605104544675730729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2060920560557571603897221 386422605104544675730729)
                  ·
                    rfl

theorem cell22_3386499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 4].length) (baseStart_3386499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386499 prefixEnd_3386499 := by exact prefixLift 3386499
  have htrace : WordTrace (prefixWord ++ tailWord_3386499) baseStart_3386499 baseEnd_3386499 := by
    simpa [prefixWord, tailWord_3386499, baseEnd_3386499] using wordTrace_append hprefix tailTrace_3386499
  have hstable : (prefixWord ++ tailWord_3386499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386499).length < 2 ^ (prefixWord ++ tailWord_3386499).sum := by decide
  have hdescent : baseEnd_3386499 < baseStart_3386499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386512 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_3386512 : Nat := 118140960795 + 3386512 * 2 ^ 59
def prefixEnd_3386512 : Nat := 4983230072969 + 3 ^ 40 * 3386512 * 2
def baseEnd_3386512 : Nat := 1159272265479306326617147

theorem tailTrace_3386512 : CollatzResearch.WordTrace tailWord_3386512 prefixEnd_3386512 1159272265479306326617147 := by
  unfold tailWord_3386512
  simp only [CollatzResearch.WordTrace]
  refine ⟨61758119953626434524152895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82344159938168579365537193 61758119953626434524152895)
  ·
    refine ⟨92637179930439651786229343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61758119953626434524152895 92637179930439651786229343)
    ·
      refine ⟨138955769895659477679344015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92637179930439651786229343 138955769895659477679344015)
      ·
        refine ⟨208433654843489216519016023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138955769895659477679344015 208433654843489216519016023)
        ·
          refine ⟨312650482265233824778524035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208433654843489216519016023 312650482265233824778524035)
          ·
            refine ⟨468975723397850737167786053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312650482265233824778524035 468975723397850737167786053)
            ·
              refine ⟨87932948137097013218959885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 468975723397850737167786053 87932948137097013218959885)
              ·
                refine ⟨32974855551411379957109957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87932948137097013218959885 32974855551411379957109957)
                ·
                  refine ⟨6182785415889633741958117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32974855551411379957109957 6182785415889633741958117)
                  ·
                    refine ⟨1159272265479306326617147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182785415889633741958117 1159272265479306326617147)
                    ·
                      rfl

theorem cell22_3386512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_3386512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386512 prefixEnd_3386512 := by exact prefixLift 3386512
  have htrace : WordTrace (prefixWord ++ tailWord_3386512) baseStart_3386512 baseEnd_3386512 := by
    simpa [prefixWord, tailWord_3386512, baseEnd_3386512] using wordTrace_append hprefix tailTrace_3386512
  have hstable : (prefixWord ++ tailWord_3386512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386512).length < 2 ^ (prefixWord ++ tailWord_3386512).sum := by decide
  have hdescent : baseEnd_3386512 < baseStart_3386512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386546 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 2, 4]
def baseStart_3386546 : Nat := 118140960795 + 3386546 * 2 ^ 59
def prefixEnd_3386546 : Nat := 4983230072969 + 3 ^ 40 * 3386546 * 2
def baseEnd_3386546 : Nat := 1159283904374141571267043

theorem tailTrace_3386546 : CollatzResearch.WordTrace tailWord_3386546 prefixEnd_3386546 1159283904374141571267043 := by
  unfold tailWord_3386546
  simp only [CollatzResearch.WordTrace]
  refine ⟨30879369997282423213760873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82344986659419795236695661 30879369997282423213760873)
  ·
    refine ⟨23159527497961817410320655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30879369997282423213760873 23159527497961817410320655)
    ·
      refine ⟨34739291246942726115480983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23159527497961817410320655 34739291246942726115480983)
      ·
        refine ⟨52108936870414089173221475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34739291246942726115480983 52108936870414089173221475)
        ·
          refine ⟨78163405305621133759832213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52108936870414089173221475 78163405305621133759832213)
          ·
            refine ⟨3663909623700990644992135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78163405305621133759832213 3663909623700990644992135)
            ·
              refine ⟨5495864435551485967488203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3663909623700990644992135 5495864435551485967488203)
              ·
                refine ⟨8243796653327228951232305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5495864435551485967488203 8243796653327228951232305)
                ·
                  refine ⟨6182847489995421713424229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8243796653327228951232305 6182847489995421713424229)
                  ·
                    refine ⟨1159283904374141571267043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6182847489995421713424229 1159283904374141571267043)
                    ·
                      rfl

theorem cell22_3386546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_3386546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386546 prefixEnd_3386546 := by exact prefixLift 3386546
  have htrace : WordTrace (prefixWord ++ tailWord_3386546) baseStart_3386546 baseEnd_3386546 := by
    simpa [prefixWord, tailWord_3386546, baseEnd_3386546] using wordTrace_append hprefix tailTrace_3386546
  have hstable : (prefixWord ++ tailWord_3386546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386546).length < 2 ^ (prefixWord ++ tailWord_3386546).sum := by decide
  have hdescent : baseEnd_3386546 < baseStart_3386546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386582 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3386582 : Nat := 118140960795 + 3386582 * 2 ^ 59
def prefixEnd_3386582 : Nat := 4983230072969 + 3 ^ 40 * 3386582 * 2
def baseEnd_3386582 : Nat := 1159296227909849477366933

theorem tailTrace_3386582 : CollatzResearch.WordTrace tailWord_3386582 prefixEnd_3386582 1159296227909849477366933 := by
  unfold tailWord_3386582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7719924563562454437709625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82345862011332847335569333 7719924563562454437709625)
  ·
    refine ⟨5789943422671840828282219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7719924563562454437709625 5789943422671840828282219)
    ·
      refine ⟨8684915134007761242423329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5789943422671840828282219 8684915134007761242423329)
      ·
        refine ⟨6513686350505820931817497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8684915134007761242423329 6513686350505820931817497)
        ·
          refine ⟨4885264762879365698863123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6513686350505820931817497 4885264762879365698863123)
          ·
            refine ⟨7327897144319048548294685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885264762879365698863123 7327897144319048548294685)
            ·
              refine ⟨2747961429119643205610507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7327897144319048548294685 2747961429119643205610507)
              ·
                refine ⟨4121942143679464808415761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2747961429119643205610507 4121942143679464808415761)
                ·
                  refine ⟨3091456607759598606311821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4121942143679464808415761 3091456607759598606311821)
                  ·
                    refine ⟨1159296227909849477366933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091456607759598606311821 1159296227909849477366933)
                    ·
                      rfl

theorem cell22_3386582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3386582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386582 prefixEnd_3386582 := by exact prefixLift 3386582
  have htrace : WordTrace (prefixWord ++ tailWord_3386582) baseStart_3386582 baseEnd_3386582 := by
    simpa [prefixWord, tailWord_3386582, baseEnd_3386582] using wordTrace_append hprefix tailTrace_3386582
  have hstable : (prefixWord ++ tailWord_3386582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386582).length < 2 ^ (prefixWord ++ tailWord_3386582).sum := by decide
  have hdescent : baseEnd_3386582 < baseStart_3386582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386587 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_3386587 : Nat := 118140960795 + 3386587 * 2 ^ 59
def prefixEnd_3386587 : Nat := 4983230072969 + 3 ^ 40 * 3386587 * 2
def baseEnd_3386587 : Nat := 1159297939512031130991917

theorem tailTrace_3386587 : CollatzResearch.WordTrace tailWord_3386587 prefixEnd_3386587 1159297939512031130991917 := by
  unfold tailWord_3386587
  simp only [CollatzResearch.WordTrace]
  refine ⟨123518975381981156857286015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82345983587987437904857343 123518975381981156857286015)
  ·
    refine ⟨185278463072971735285929023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123518975381981156857286015 185278463072971735285929023)
    ·
      refine ⟨277917694609457602928893535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185278463072971735285929023 277917694609457602928893535)
      ·
        refine ⟨416876541914186404393340303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277917694609457602928893535 416876541914186404393340303)
        ·
          refine ⟨625314812871279606590010455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416876541914186404393340303 625314812871279606590010455)
          ·
            refine ⟨937972219306919409885015683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625314812871279606590010455 937972219306919409885015683)
            ·
              refine ⟨1406958328960379114827523525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937972219306919409885015683 1406958328960379114827523525)
              ·
                refine ⟨263804686680071084030160661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1406958328960379114827523525 263804686680071084030160661)
                ·
                  refine ⟨12365844688128332063913781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 263804686680071084030160661 12365844688128332063913781)
                  ·
                    refine ⟨1159297939512031130991917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12365844688128332063913781 1159297939512031130991917)
                    ·
                      rfl

theorem cell22_3386587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_3386587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386587 prefixEnd_3386587 := by exact prefixLift 3386587
  have htrace : WordTrace (prefixWord ++ tailWord_3386587) baseStart_3386587 baseEnd_3386587 := by
    simpa [prefixWord, tailWord_3386587, baseEnd_3386587] using wordTrace_append hprefix tailTrace_3386587
  have hstable : (prefixWord ++ tailWord_3386587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386587).length < 2 ^ (prefixWord ++ tailWord_3386587).sum := by decide
  have hdescent : baseEnd_3386587 < baseStart_3386587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386653 : List Nat := [1, 4, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_3386653 : Nat := 118140960795 + 3386653 * 2 ^ 59
def prefixEnd_3386653 : Nat := 4983230072969 + 3 ^ 40 * 3386653 * 2
def baseEnd_3386653 : Nat := 1159320532660828958841715

theorem tailTrace_3386653 : CollatzResearch.WordTrace tailWord_3386653 prefixEnd_3386653 1159320532660828958841715 := by
  unfold tailWord_3386653
  simp only [CollatzResearch.WordTrace]
  refine ⟨123521382599742050129188613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82347588399828033419459075 123521382599742050129188613)
  ·
    refine ⟨23160259237451634399222865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123521382599742050129188613 23160259237451634399222865)
    ·
      refine ⟨17370194428088725799417149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23160259237451634399222865 17370194428088725799417149)
      ·
        refine ⟨6513822910533272174781431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17370194428088725799417149 6513822910533272174781431)
        ·
          refine ⟨9770734365799908262172147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513822910533272174781431 9770734365799908262172147)
          ·
            refine ⟨14656101548699862393258221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770734365799908262172147 14656101548699862393258221)
            ·
              refine ⟨5496038080762448397471833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14656101548699862393258221 5496038080762448397471833)
              ·
                refine ⟨4122028560571836298103875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496038080762448397471833 4122028560571836298103875)
                ·
                  refine ⟨6183042840857754447155813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122028560571836298103875 6183042840857754447155813)
                  ·
                    refine ⟨1159320532660828958841715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6183042840857754447155813 1159320532660828958841715)
                    ·
                      rfl

theorem cell22_3386653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_3386653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386653 prefixEnd_3386653 := by exact prefixLift 3386653
  have htrace : WordTrace (prefixWord ++ tailWord_3386653) baseStart_3386653 baseEnd_3386653 := by
    simpa [prefixWord, tailWord_3386653, baseEnd_3386653] using wordTrace_append hprefix tailTrace_3386653
  have hstable : (prefixWord ++ tailWord_3386653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386653).length < 2 ^ (prefixWord ++ tailWord_3386653).sum := by decide
  have hdescent : baseEnd_3386653 < baseStart_3386653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386666 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3386666 : Nat := 118140960795 + 3386666 * 2 ^ 59
def prefixEnd_3386666 : Nat := 4983230072969 + 3 ^ 40 * 3386666 * 2
def baseEnd_3386666 : Nat := 1159324982826501258266675

theorem tailTrace_3386666 : CollatzResearch.WordTrace tailWord_3386666 prefixEnd_3386666 1159324982826501258266675 := by
  unfold tailWord_3386666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30880464187173738337352963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82347904499129968899607901 30880464187173738337352963)
  ·
    refine ⟨46320696280760607506029445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30880464187173738337352963 46320696280760607506029445)
    ·
      refine ⟨8685130552642613907380521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46320696280760607506029445 8685130552642613907380521)
      ·
        refine ⟨6513847914481960430535391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8685130552642613907380521 6513847914481960430535391)
        ·
          refine ⟨9770771871722940645803087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6513847914481960430535391 9770771871722940645803087)
          ·
            refine ⟨14656157807584410968704631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9770771871722940645803087 14656157807584410968704631)
            ·
              refine ⟨21984236711376616453056947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656157807584410968704631 21984236711376616453056947)
              ·
                refine ⟨32976355067064924679585421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21984236711376616453056947 32976355067064924679585421)
                ·
                  refine ⟨12366133150149346754844533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32976355067064924679585421 12366133150149346754844533)
                  ·
                    refine ⟨1159324982826501258266675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12366133150149346754844533 1159324982826501258266675)
                    ·
                      rfl

theorem cell22_3386666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3386666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386666 prefixEnd_3386666 := by exact prefixLift 3386666
  have htrace : WordTrace (prefixWord ++ tailWord_3386666) baseStart_3386666 baseEnd_3386666 := by
    simpa [prefixWord, tailWord_3386666, baseEnd_3386666] using wordTrace_append hprefix tailTrace_3386666
  have hstable : (prefixWord ++ tailWord_3386666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386666).length < 2 ^ (prefixWord ++ tailWord_3386666).sum := by decide
  have hdescent : baseEnd_3386666 < baseStart_3386666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386685 : List Nat := [1, 4, 1, 5, 1, 1, 1, 4, 4]
def baseStart_3386685 : Nat := 118140960795 + 3386685 * 2 ^ 59
def prefixEnd_3386685 : Nat := 4983230072969 + 3 ^ 40 * 3386685 * 2
def baseEnd_3386685 : Nat := 386443828971597180680539

theorem tailTrace_3386685 : CollatzResearch.WordTrace tailWord_3386685 prefixEnd_3386685 386443828971597180680539 := by
  unfold tailWord_3386685
  simp only [CollatzResearch.WordTrace]
  refine ⟨123522549735626119594353509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82348366490417413062902339 123522549735626119594353509)
  ·
    refine ⟨23160478075429897423941283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123522549735626119594353509 23160478075429897423941283)
    ·
      refine ⟨34740717113144846135911925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23160478075429897423941283 34740717113144846135911925)
      ·
        refine ⟨3256942229357329325241743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34740717113144846135911925 3256942229357329325241743)
        ·
          refine ⟨4885413344035993987862615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3256942229357329325241743 4885413344035993987862615)
          ·
            refine ⟨7328120016053990981793923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4885413344035993987862615 7328120016053990981793923)
            ·
              refine ⟨10992180024080986472690885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7328120016053990981793923 10992180024080986472690885)
              ·
                refine ⟨2061033754515184963629541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10992180024080986472690885 2061033754515184963629541)
                ·
                  refine ⟨386443828971597180680539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2061033754515184963629541 386443828971597180680539)
                  ·
                    rfl

theorem cell22_3386685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_3386685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386685 prefixEnd_3386685 := by exact prefixLift 3386685
  have htrace : WordTrace (prefixWord ++ tailWord_3386685) baseStart_3386685 baseEnd_3386685 := by
    simpa [prefixWord, tailWord_3386685, baseEnd_3386685] using wordTrace_append hprefix tailTrace_3386685
  have hstable : (prefixWord ++ tailWord_3386685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386685).length < 2 ^ (prefixWord ++ tailWord_3386685).sum := by decide
  have hdescent : baseEnd_3386685 < baseStart_3386685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386711 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 5, 3]
def baseStart_3386711 : Nat := 118140960795 + 3386711 * 2 ^ 59
def prefixEnd_3386711 : Nat := 4983230072969 + 3 ^ 40 * 3386711 * 2
def baseEnd_3386711 : Nat := 1159340387246136140891537

theorem tailTrace_3386711 : CollatzResearch.WordTrace tailWord_3386711 prefixEnd_3386711 1159340387246136140891537 := by
  unfold tailWord_3386711
  simp only [CollatzResearch.WordTrace]
  refine ⟨123523498033531926034799987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82348998689021284023199991 123523498033531926034799987)
  ·
    refine ⟨185285247050297889052199981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123523498033531926034799987 185285247050297889052199981)
    ·
      refine ⟨69481967643861708394574993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185285247050297889052199981 69481967643861708394574993)
      ·
        refine ⟨52111475732896281295931245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69481967643861708394574993 52111475732896281295931245)
        ·
          refine ⟨19541803399836105485974217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52111475732896281295931245 19541803399836105485974217)
          ·
            refine ⟨14656352549877079114480663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19541803399836105485974217 14656352549877079114480663)
            ·
              refine ⟨21984528824815618671720995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14656352549877079114480663 21984528824815618671720995)
              ·
                refine ⟨32976793237223428007581493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21984528824815618671720995 32976793237223428007581493)
                ·
                  refine ⟨3091574365989696375710765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32976793237223428007581493 3091574365989696375710765)
                  ·
                    refine ⟨1159340387246136140891537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091574365989696375710765 1159340387246136140891537)
                    ·
                      rfl

theorem cell22_3386711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 3].length) (baseStart_3386711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386711 prefixEnd_3386711 := by exact prefixLift 3386711
  have htrace : WordTrace (prefixWord ++ tailWord_3386711) baseStart_3386711 baseEnd_3386711 := by
    simpa [prefixWord, tailWord_3386711, baseEnd_3386711] using wordTrace_append hprefix tailTrace_3386711
  have hstable : (prefixWord ++ tailWord_3386711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386711).length < 2 ^ (prefixWord ++ tailWord_3386711).sum := by decide
  have hdescent : baseEnd_3386711 < baseStart_3386711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386734 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3386734 : Nat := 118140960795 + 3386734 * 2 ^ 59
def prefixEnd_3386734 : Nat := 4983230072969 + 3 ^ 40 * 3386734 * 2
def baseEnd_3386734 : Nat := 1159348260616171747566467

theorem tailTrace_3386734 : CollatzResearch.WordTrace tailWord_3386734 prefixEnd_3386734 1159348260616171747566467 := by
  unfold tailWord_3386734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15440542114056075120360907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82349557941632400641924837 15440542114056075120360907)
  ·
    refine ⟨23160813171084112680541361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15440542114056075120360907 23160813171084112680541361)
    ·
      refine ⟨17370609878313084510406021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23160813171084112680541361 17370609878313084510406021)
      ·
        refine ⟨3256989352183703345701129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17370609878313084510406021 3256989352183703345701129)
        ·
          refine ⟨2442742014137777509275847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3256989352183703345701129 2442742014137777509275847)
          ·
            refine ⟨3664113021206666263913771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2442742014137777509275847 3664113021206666263913771)
            ·
              refine ⟨5496169531809999395870657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664113021206666263913771 5496169531809999395870657)
              ·
                refine ⟨4122127148857499546902993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5496169531809999395870657 4122127148857499546902993)
                ·
                  refine ⟨3091595361643124660177245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4122127148857499546902993 3091595361643124660177245)
                  ·
                    refine ⟨1159348260616171747566467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3091595361643124660177245 1159348260616171747566467)
                    ·
                      rfl

theorem cell22_3386734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3386734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386734 prefixEnd_3386734 := by exact prefixLift 3386734
  have htrace : WordTrace (prefixWord ++ tailWord_3386734) baseStart_3386734 baseEnd_3386734 := by
    simpa [prefixWord, tailWord_3386734, baseEnd_3386734] using wordTrace_append hprefix tailTrace_3386734
  have hstable : (prefixWord ++ tailWord_3386734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386734).length < 2 ^ (prefixWord ++ tailWord_3386734).sum := by decide
  have hdescent : baseEnd_3386734 < baseStart_3386734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3386756 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3386756 : Nat := 118140960795 + 3386756 * 2 ^ 59
def prefixEnd_3386756 : Nat := 4983230072969 + 3 ^ 40 * 3386756 * 2
def baseEnd_3386756 : Nat := 1159355791665771023516399

theorem tailTrace_3386756 : CollatzResearch.WordTrace tailWord_3386756 prefixEnd_3386756 1159355791665771023516399 := by
  unfold tailWord_3386756
  simp only [CollatzResearch.WordTrace]
  refine ⟨61762569659184449360094061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82350092878912599146792081 61762569659184449360094061)
  ·
    refine ⟨23160963622194168510035273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61762569659184449360094061 23160963622194168510035273)
    ·
      refine ⟨17370722716645626382526455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23160963622194168510035273 17370722716645626382526455)
      ·
        refine ⟨26056084074968439573789683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17370722716645626382526455 26056084074968439573789683)
        ·
          refine ⟨39084126112452659360684525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26056084074968439573789683 39084126112452659360684525)
          ·
            refine ⟨14656547292169747260256697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39084126112452659360684525 14656547292169747260256697)
            ·
              refine ⟨10992410469127310445192523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14656547292169747260256697 10992410469127310445192523)
              ·
                refine ⟨16488615703690965667788785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10992410469127310445192523 16488615703690965667788785)
                ·
                  refine ⟨12366461777768224250841589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16488615703690965667788785 12366461777768224250841589)
                  ·
                    refine ⟨1159355791665771023516399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12366461777768224250841589 1159355791665771023516399)
                    ·
                      rfl

theorem cell22_3386756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3386756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3386756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3386756 prefixEnd_3386756 := by exact prefixLift 3386756
  have htrace : WordTrace (prefixWord ++ tailWord_3386756) baseStart_3386756 baseEnd_3386756 := by
    simpa [prefixWord, tailWord_3386756, baseEnd_3386756] using wordTrace_append hprefix tailTrace_3386756
  have hstable : (prefixWord ++ tailWord_3386756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3386756).length < 2 ^ (prefixWord ++ tailWord_3386756).sum := by decide
  have hdescent : baseEnd_3386756 < baseStart_3386756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3386756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387043 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 2, 5]
def baseStart_3387043 : Nat := 118140960795 + 3387043 * 2 ^ 59
def prefixEnd_3387043 : Nat := 4983230072969 + 3 ^ 40 * 3387043 * 2
def baseEnd_3387043 : Nat := 1159454037630997941590519

theorem tailTrace_3387043 : CollatzResearch.WordTrace tailWord_3387043 prefixEnd_3387043 1159454037630997941590519 := by
  unfold tailWord_3387043
  simp only [CollatzResearch.WordTrace]
  refine ⟨123535607068329146735885783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82357071378886097823923855 123535607068329146735885783)
  ·
    refine ⟨185303410602493720103828675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123535607068329146735885783 185303410602493720103828675)
    ·
      refine ⟨277955115903740580155743013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185303410602493720103828675 277955115903740580155743013)
      ·
        refine ⟨52116584231951358779201815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277955115903740580155743013 52116584231951358779201815)
        ·
          refine ⟨78174876347927038168802723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52116584231951358779201815 78174876347927038168802723)
          ·
            refine ⟨117262314521890557253204085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78174876347927038168802723 117262314521890557253204085)
            ·
              refine ⟨10993341986427239742487883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117262314521890557253204085 10993341986427239742487883)
              ·
                refine ⟨16490012979640859613731825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993341986427239742487883 16490012979640859613731825)
                ·
                  refine ⟨12367509734730644710298869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16490012979640859613731825 12367509734730644710298869)
                  ·
                    refine ⟨1159454037630997941590519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12367509734730644710298869 1159454037630997941590519)
                    ·
                      rfl

theorem cell22_3387043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_3387043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387043 prefixEnd_3387043 := by exact prefixLift 3387043
  have htrace : WordTrace (prefixWord ++ tailWord_3387043) baseStart_3387043 baseEnd_3387043 := by
    simpa [prefixWord, tailWord_3387043, baseEnd_3387043] using wordTrace_append hprefix tailTrace_3387043
  have hstable : (prefixWord ++ tailWord_3387043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387043).length < 2 ^ (prefixWord ++ tailWord_3387043).sum := by decide
  have hdescent : baseEnd_3387043 < baseStart_3387043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387090 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_3387090 : Nat := 118140960795 + 3387090 * 2 ^ 59
def prefixEnd_3387090 : Nat := 4983230072969 + 3 ^ 40 * 3387090 * 2
def baseEnd_3387090 : Nat := 386490042230501828555125

theorem tailTrace_3387090 : CollatzResearch.WordTrace tailWord_3387090 prefixEnd_3387090 386490042230501828555125 := by
  unfold tailWord_3387090
  simp only [CollatzResearch.WordTrace]
  refine ⟨30884330324789718440711681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82358214199439249175231149 30884330324789718440711681)
  ·
    refine ⟨23163247743592288830533761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30884330324789718440711681 23163247743592288830533761)
    ·
      refine ⟨17372435807694216622900321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23163247743592288830533761 17372435807694216622900321)
      ·
        refine ⟨13029326855770662467175241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17372435807694216622900321 13029326855770662467175241)
        ·
          refine ⟨9771995141827996850381431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13029326855770662467175241 9771995141827996850381431)
          ·
            refine ⟨14657992712741995275572147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9771995141827996850381431 14657992712741995275572147)
            ·
              refine ⟨21986989069112992913358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14657992712741995275572147 21986989069112992913358221)
              ·
                refine ⟨8245120900917372342509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21986989069112992913358221 8245120900917372342509333)
                ·
                  refine ⟨386490042230501828555125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8245120900917372342509333 386490042230501828555125)
                  ·
                    rfl

theorem cell22_3387090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_3387090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387090 prefixEnd_3387090 := by exact prefixLift 3387090
  have htrace : WordTrace (prefixWord ++ tailWord_3387090) baseStart_3387090 baseEnd_3387090 := by
    simpa [prefixWord, tailWord_3387090, baseEnd_3387090] using wordTrace_append hprefix tailTrace_3387090
  have hstable : (prefixWord ++ tailWord_3387090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387090).length < 2 ^ (prefixWord ++ tailWord_3387090).sum := by decide
  have hdescent : baseEnd_3387090 < baseStart_3387090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387103 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_3387103 : Nat := 118140960795 + 3387103 * 2 ^ 59
def prefixEnd_3387103 : Nat := 4983230072969 + 3 ^ 40 * 3387103 * 2
def baseEnd_3387103 : Nat := 1159474576857177785090335

theorem tailTrace_3387103 : CollatzResearch.WordTrace tailWord_3387103 prefixEnd_3387103 1159474576857177785090335 := by
  unfold tailWord_3387103
  simp only [CollatzResearch.WordTrace]
  refine ⟨123537795448111776983069963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82358530298741184655379975 123537795448111776983069963)
  ·
    refine ⟨185306693172167665474604945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123537795448111776983069963 185306693172167665474604945)
    ·
      refine ⟨138980019879125749105953709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185306693172167665474604945 138980019879125749105953709)
      ·
        refine ⟨52117507454672155914732641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138980019879125749105953709 52117507454672155914732641)
        ·
          refine ⟨39088130591004116936049481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52117507454672155914732641 39088130591004116936049481)
          ·
            refine ⟨29316097943253087702037111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39088130591004116936049481 29316097943253087702037111)
            ·
              refine ⟨43974146914879631553055667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29316097943253087702037111 43974146914879631553055667)
              ·
                refine ⟨65961220372319447329583501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43974146914879631553055667 65961220372319447329583501)
                ·
                  refine ⟨24735457639619792748593813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65961220372319447329583501 24735457639619792748593813)
                  ·
                    refine ⟨1159474576857177785090335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24735457639619792748593813 1159474576857177785090335)
                    ·
                      rfl

theorem cell22_3387103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_3387103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387103 prefixEnd_3387103 := by exact prefixLift 3387103
  have htrace : WordTrace (prefixWord ++ tailWord_3387103) baseStart_3387103 baseEnd_3387103 := by
    simpa [prefixWord, tailWord_3387103, baseEnd_3387103] using wordTrace_append hprefix tailTrace_3387103
  have hstable : (prefixWord ++ tailWord_3387103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387103).length < 2 ^ (prefixWord ++ tailWord_3387103).sum := by decide
  have hdescent : baseEnd_3387103 < baseStart_3387103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387197 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 5]
def baseStart_3387197 : Nat := 118140960795 + 3387197 * 2 ^ 59
def prefixEnd_3387197 : Nat := 4983230072969 + 3 ^ 40 * 3387197 * 2
def baseEnd_3387197 : Nat := 386502251659397624413349

theorem tailTrace_3387197 : CollatzResearch.WordTrace tailWord_3387197 prefixEnd_3387197 386502251659397624413349 := by
  unfold tailWord_3387197
  simp only [CollatzResearch.WordTrace]
  refine ⟨123541223909771231036991845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82360815939847487357994563 123541223909771231036991845)
  ·
    refine ⟨23163979483082105819435971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123541223909771231036991845 23163979483082105819435971)
    ·
      refine ⟨34745969224623158729153957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23163979483082105819435971 34745969224623158729153957)
      ·
        refine ⟨6514869229616842261716367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34745969224623158729153957 6514869229616842261716367)
        ·
          refine ⟨9772303844425263392574551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6514869229616842261716367 9772303844425263392574551)
          ·
            refine ⟨14658455766637895088861827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9772303844425263392574551 14658455766637895088861827)
            ·
              refine ⟨21987683649956842633292741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14658455766637895088861827 21987683649956842633292741)
              ·
                refine ⟨4122690684366907993742389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21987683649956842633292741 4122690684366907993742389)
                ·
                  refine ⟨386502251659397624413349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4122690684366907993742389 386502251659397624413349)
                  ·
                    rfl

theorem cell22_3387197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_3387197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387197 prefixEnd_3387197 := by exact prefixLift 3387197
  have htrace : WordTrace (prefixWord ++ tailWord_3387197) baseStart_3387197 baseEnd_3387197 := by
    simpa [prefixWord, tailWord_3387197, baseEnd_3387197] using wordTrace_append hprefix tailTrace_3387197
  have hstable : (prefixWord ++ tailWord_3387197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387197).length < 2 ^ (prefixWord ++ tailWord_3387197).sum := by decide
  have hdescent : baseEnd_3387197 < baseStart_3387197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387210 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 5, 4]
def baseStart_3387210 : Nat := 118140960795 + 3387210 * 2 ^ 59
def prefixEnd_3387210 : Nat := 4983230072969 + 3 ^ 40 * 3387210 * 2
def baseEnd_3387210 : Nat := 1159511205143865172665007

theorem tailTrace_3387210 : CollatzResearch.WordTrace tailWord_3387210 prefixEnd_3387210 1159511205143865172665007 := by
  unfold tailWord_3387210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30885424514681033564303771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82361132039149422838143389 30885424514681033564303771)
  ·
    refine ⟨46328136772021550346455657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30885424514681033564303771 46328136772021550346455657)
    ·
      refine ⟨34746102579016162759841743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46328136772021550346455657 34746102579016162759841743)
      ·
        refine ⟨52119153868524244139762615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34746102579016162759841743 52119153868524244139762615)
        ·
          refine ⟨78178730802786366209643923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52119153868524244139762615 78178730802786366209643923)
          ·
            refine ⟨117268096204179549314465885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78178730802786366209643923 117268096204179549314465885)
            ·
              refine ⟨43975536076567330992924707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117268096204179549314465885 43975536076567330992924707)
              ·
                refine ⟨65963304114850996489387061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43975536076567330992924707 65963304114850996489387061)
                ·
                  refine ⟨6184059760767280920880037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65963304114850996489387061 6184059760767280920880037)
                  ·
                    refine ⟨1159511205143865172665007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184059760767280920880037 1159511205143865172665007)
                    ·
                      rfl

theorem cell22_3387210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_3387210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387210 prefixEnd_3387210 := by exact prefixLift 3387210
  have htrace : WordTrace (prefixWord ++ tailWord_3387210) baseStart_3387210 baseEnd_3387210 := by
    simpa [prefixWord, tailWord_3387210, baseEnd_3387210] using wordTrace_append hprefix tailTrace_3387210
  have hstable : (prefixWord ++ tailWord_3387210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387210).length < 2 ^ (prefixWord ++ tailWord_3387210).sum := by decide
  have hdescent : baseEnd_3387210 < baseStart_3387210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387212 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_3387212 : Nat := 118140960795 + 3387212 * 2 ^ 59
def prefixEnd_3387212 : Nat := 4983230072969 + 3 ^ 40 * 3387212 * 2
def baseEnd_3387212 : Nat := 1159511889784737834115001

theorem tailTrace_3387212 : CollatzResearch.WordTrace tailWord_3387212 prefixEnd_3387212 1159511889784737834115001 := by
  unfold tailWord_3387212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61770885502358444299393945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82361180669811259065858593 61770885502358444299393945)
  ·
    refine ⟨46328164126768833224545459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61770885502358444299393945 46328164126768833224545459)
    ·
      refine ⟨69492246190153249836818189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46328164126768833224545459 69492246190153249836818189)
      ·
        refine ⟨26059592321307468688806821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69492246190153249836818189 26059592321307468688806821)
        ·
          refine ⟨4886173560245150379151279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26059592321307468688806821 4886173560245150379151279)
          ·
            refine ⟨7329260340367725568726919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886173560245150379151279 7329260340367725568726919)
            ·
              refine ⟨10993890510551588353090379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7329260340367725568726919 10993890510551588353090379)
              ·
                refine ⟨16490835765827382529635569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10993890510551588353090379 16490835765827382529635569)
                ·
                  refine ⟨12368126824370536897226677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16490835765827382529635569 12368126824370536897226677)
                  ·
                    refine ⟨1159511889784737834115001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12368126824370536897226677 1159511889784737834115001)
                    ·
                      rfl

theorem cell22_3387212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_3387212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387212 prefixEnd_3387212 := by exact prefixLift 3387212
  have htrace : WordTrace (prefixWord ++ tailWord_3387212) baseStart_3387212 baseEnd_3387212 := by
    simpa [prefixWord, tailWord_3387212, baseEnd_3387212] using wordTrace_append hprefix tailTrace_3387212
  have hstable : (prefixWord ++ tailWord_3387212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387212).length < 2 ^ (prefixWord ++ tailWord_3387212).sum := by decide
  have hdescent : baseEnd_3387212 < baseStart_3387212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387225 : List Nat := [1, 2, 1, 2, 2, 3, 3, 2, 6]
def baseStart_3387225 : Nat := 118140960795 + 3387225 * 2 ^ 59
def prefixEnd_3387225 : Nat := 4983230072969 + 3 ^ 40 * 3387225 * 2
def baseEnd_3387225 : Nat := 386505446650136711179987

theorem tailTrace_3387225 : CollatzResearch.WordTrace tailWord_3387225 prefixEnd_3387225 386505446650136711179987 := by
  unfold tailWord_3387225
  simp only [CollatzResearch.WordTrace]
  refine ⟨123542245153669791819011129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82361496769113194546007419 123542245153669791819011129)
  ·
    refine ⟨92656683865252343864258347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123542245153669791819011129 92656683865252343864258347)
    ·
      refine ⟨138985025797878515796387521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92656683865252343864258347 138985025797878515796387521)
      ·
        refine ⟨104238769348408886847290641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138985025797878515796387521 104238769348408886847290641)
        ·
          refine ⟨78179077011306665135467981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104238769348408886847290641 78179077011306665135467981)
          ·
            refine ⟨29317153879239999425800493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78179077011306665135467981 29317153879239999425800493)
            ·
              refine ⟨10993932704714999784675185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29317153879239999425800493 10993932704714999784675185)
              ·
                refine ⟨8245449528536249838506389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10993932704714999784675185 8245449528536249838506389)
                ·
                  refine ⟨386505446650136711179987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8245449528536249838506389 386505446650136711179987)
                  ·
                    rfl

theorem cell22_3387225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_3387225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387225 prefixEnd_3387225 := by exact prefixLift 3387225
  have htrace : WordTrace (prefixWord ++ tailWord_3387225) baseStart_3387225 baseEnd_3387225 := by
    simpa [prefixWord, tailWord_3387225, baseEnd_3387225] using wordTrace_append hprefix tailTrace_3387225
  have hstable : (prefixWord ++ tailWord_3387225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387225).length < 2 ^ (prefixWord ++ tailWord_3387225).sum := by decide
  have hdescent : baseEnd_3387225 < baseStart_3387225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387244 : List Nat := [2, 2, 1, 1, 4, 2, 4, 1, 1, 4]
def baseStart_3387244 : Nat := 118140960795 + 3387244 * 2 ^ 59
def prefixEnd_3387244 : Nat := 4983230072969 + 3 ^ 40 * 3387244 * 2
def baseEnd_3387244 : Nat := 1159522844038700417314903

theorem tailTrace_3387244 : CollatzResearch.WordTrace tailWord_3387244 prefixEnd_3387244 1159522844038700417314903 := by
  unfold tailWord_3387244
  simp only [CollatzResearch.WordTrace]
  refine ⟨61771469070300479031976393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82361958760400638709301857 61771469070300479031976393)
  ·
    refine ⟨46328601802725359273982295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61771469070300479031976393 46328601802725359273982295)
    ·
      refine ⟨69492902704088038910973443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46328601802725359273982295 69492902704088038910973443)
      ·
        refine ⟨104239354056132058366460165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69492902704088038910973443 104239354056132058366460165)
        ·
          refine ⟨19544878885524760943711281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104239354056132058366460165 19544878885524760943711281)
          ·
            refine ⟨14658659164143570707783461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19544878885524760943711281 14658659164143570707783461)
            ·
              refine ⟨2748498593276919507709399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14658659164143570707783461 2748498593276919507709399)
              ·
                refine ⟨4122747889915379261564099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748498593276919507709399 4122747889915379261564099)
                ·
                  refine ⟨6184121834873068892346149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122747889915379261564099 6184121834873068892346149)
                  ·
                    refine ⟨1159522844038700417314903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184121834873068892346149 1159522844038700417314903)
                    ·
                      rfl

theorem cell22_3387244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 4].length) (baseStart_3387244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387244 prefixEnd_3387244 := by exact prefixLift 3387244
  have htrace : WordTrace (prefixWord ++ tailWord_3387244) baseStart_3387244 baseEnd_3387244 := by
    simpa [prefixWord, tailWord_3387244, baseEnd_3387244] using wordTrace_append hprefix tailTrace_3387244
  have hstable : (prefixWord ++ tailWord_3387244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387244).length < 2 ^ (prefixWord ++ tailWord_3387244).sum := by decide
  have hdescent : baseEnd_3387244 < baseStart_3387244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387257 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_3387257 : Nat := 118140960795 + 3387257 * 2 ^ 59
def prefixEnd_3387257 : Nat := 4983230072969 + 3 ^ 40 * 3387257 * 2
def baseEnd_3387257 : Nat := 1159527294204372716739863

theorem tailTrace_3387257 : CollatzResearch.WordTrace tailWord_3387257 prefixEnd_3387257 1159527294204372716739863 := by
  unfold tailWord_3387257
  simp only [CollatzResearch.WordTrace]
  refine ⟨123543412289553861284176025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82362274859702574189450683 123543412289553861284176025)
  ·
    refine ⟨92657559217165395963132019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123543412289553861284176025 92657559217165395963132019)
    ·
      refine ⟨138986338825748093944698029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92657559217165395963132019 138986338825748093944698029)
      ·
        refine ⟨52119877059655535229261761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138986338825748093944698029 52119877059655535229261761)
        ·
          refine ⟨39089907794741651421946321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52119877059655535229261761 39089907794741651421946321)
          ·
            refine ⟨29317430846056238566459741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39089907794741651421946321 29317430846056238566459741)
            ·
              refine ⟨10994036567271089462422403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29317430846056238566459741 10994036567271089462422403)
              ·
                refine ⟨16491054850906634193633605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994036567271089462422403 16491054850906634193633605)
                ·
                  refine ⟨3092072784544993911306301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16491054850906634193633605 3092072784544993911306301)
                  ·
                    refine ⟨1159527294204372716739863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092072784544993911306301 1159527294204372716739863)
                    ·
                      rfl

theorem cell22_3387257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_3387257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387257 prefixEnd_3387257 := by exact prefixLift 3387257
  have htrace : WordTrace (prefixWord ++ tailWord_3387257) baseStart_3387257 baseEnd_3387257 := by
    simpa [prefixWord, tailWord_3387257, baseEnd_3387257] using wordTrace_append hprefix tailTrace_3387257
  have hstable : (prefixWord ++ tailWord_3387257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387257).length < 2 ^ (prefixWord ++ tailWord_3387257).sum := by decide
  have hdescent : baseEnd_3387257 < baseStart_3387257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387285 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3387285 : Nat := 118140960795 + 3387285 * 2 ^ 59
def prefixEnd_3387285 : Nat := 4983230072969 + 3 ^ 40 * 3387285 * 2
def baseEnd_3387285 : Nat := 1159536879176589977039777

theorem tailTrace_3387285 : CollatzResearch.WordTrace tailWord_3387285 prefixEnd_3387285 1159536879176589977039777 := by
  unfold tailWord_3387285
  simp only [CollatzResearch.WordTrace]
  refine ⟨123544433533452422066195309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82362955688968281377463539 123544433533452422066195309)
  ·
    refine ⟨46329162575044658274823241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123544433533452422066195309 46329162575044658274823241)
    ·
      refine ⟨34746871931283493706117431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46329162575044658274823241 34746871931283493706117431)
      ·
        refine ⟨52120307896925240559176147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34746871931283493706117431 52120307896925240559176147)
        ·
          refine ⟨78180461845387860838764221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52120307896925240559176147 78180461845387860838764221)
          ·
            refine ⟨29317673192020447814536583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78180461845387860838764221 29317673192020447814536583)
            ·
              refine ⟨43976509788030671721804875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29317673192020447814536583 43976509788030671721804875)
              ·
                refine ⟨65964764682046007582707313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43976509788030671721804875 65964764682046007582707313)
                ·
                  refine ⟨49473573511534505687030485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65964764682046007582707313 49473573511534505687030485)
                  ·
                    refine ⟨1159536879176589977039777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49473573511534505687030485 1159536879176589977039777)
                    ·
                      rfl

theorem cell22_3387285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3387285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387285 prefixEnd_3387285 := by exact prefixLift 3387285
  have htrace : WordTrace (prefixWord ++ tailWord_3387285) baseStart_3387285 baseEnd_3387285 := by
    simpa [prefixWord, tailWord_3387285, baseEnd_3387285] using wordTrace_append hprefix tailTrace_3387285
  have hstable : (prefixWord ++ tailWord_3387285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387285).length < 2 ^ (prefixWord ++ tailWord_3387285).sum := by decide
  have hdescent : baseEnd_3387285 < baseStart_3387285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387287 : List Nat := [1, 1, 3, 3, 1, 3, 4, 6]
def baseStart_3387287 : Nat := 118140960795 + 3387287 * 2 ^ 59
def prefixEnd_3387287 : Nat := 4983230072969 + 3 ^ 40 * 3387287 * 2
def baseEnd_3387287 : Nat := 128837507090829182054419

theorem tailTrace_3387287 : CollatzResearch.WordTrace tailWord_3387287 prefixEnd_3387287 128837507090829182054419 := by
  unfold tailWord_3387287
  simp only [CollatzResearch.WordTrace]
  refine ⟨123544506479445176407768115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82363004319630117605178743 123544506479445176407768115)
  ·
    refine ⟨185316759719167764611652173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123544506479445176407768115 185316759719167764611652173)
    ·
      refine ⟨69493784894687911729369565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185316759719167764611652173 69493784894687911729369565)
      ·
        refine ⟨26060169335507966898513587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69493784894687911729369565 26060169335507966898513587)
        ·
          refine ⟨39090254003261950347770381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26060169335507966898513587 39090254003261950347770381)
          ·
            refine ⟨14658845251223231380413893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39090254003261950347770381 14658845251223231380413893)
            ·
              refine ⟨2748533484604355883827605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14658845251223231380413893 2748533484604355883827605)
              ·
                refine ⟨128837507090829182054419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2748533484604355883827605 128837507090829182054419)
                ·
                  rfl

theorem cell22_3387287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 6].length) (baseStart_3387287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387287 prefixEnd_3387287 := by exact prefixLift 3387287
  have htrace : WordTrace (prefixWord ++ tailWord_3387287) baseStart_3387287 baseEnd_3387287 := by
    simpa [prefixWord, tailWord_3387287, baseEnd_3387287] using wordTrace_append hprefix tailTrace_3387287
  have hstable : (prefixWord ++ tailWord_3387287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387287).length < 2 ^ (prefixWord ++ tailWord_3387287).sum := by decide
  have hdescent : baseEnd_3387287 < baseStart_3387287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387310 : List Nat := [4, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_3387310 : Nat := 118140960795 + 3387310 * 2 ^ 59
def prefixEnd_3387310 : Nat := 4983230072969 + 3 ^ 40 * 3387310 * 2
def baseEnd_3387310 : Nat := 386515145729166081721567

theorem tailTrace_3387310 : CollatzResearch.WordTrace tailWord_3387310 prefixEnd_3387310 386515145729166081721567 := by
  unfold tailWord_3387310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15443168169795231416981923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82363563572241234223903589 15443168169795231416981923)
  ·
    refine ⟨23164752254692847125472885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15443168169795231416981923 23164752254692847125472885)
    ·
      refine ⟨2171695523877454418013083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23164752254692847125472885 2171695523877454418013083)
      ·
        refine ⟨3257543285816181627019625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2171695523877454418013083 3257543285816181627019625)
        ·
          refine ⟨2443157464362136220264719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257543285816181627019625 2443157464362136220264719)
          ·
            refine ⟨3664736196543204330397079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443157464362136220264719 3664736196543204330397079)
            ·
              refine ⟨5497104294814806495595619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664736196543204330397079 5497104294814806495595619)
              ·
                refine ⟨8245656442222209743393429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497104294814806495595619 8245656442222209743393429)
                ·
                  refine ⟨386515145729166081721567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8245656442222209743393429 386515145729166081721567)
                  ·
                    rfl

theorem cell22_3387310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_3387310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387310 prefixEnd_3387310 := by exact prefixLift 3387310
  have htrace : WordTrace (prefixWord ++ tailWord_3387310) baseStart_3387310 baseEnd_3387310 := by
    simpa [prefixWord, tailWord_3387310, baseEnd_3387310] using wordTrace_append hprefix tailTrace_3387310
  have hstable : (prefixWord ++ tailWord_3387310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387310).length < 2 ^ (prefixWord ++ tailWord_3387310).sum := by decide
  have hdescent : baseEnd_3387310 < baseStart_3387310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387315 : List Nat := [1, 1, 1, 2, 3, 1, 3, 3, 7]
def baseStart_3387315 : Nat := 118140960795 + 3387315 * 2 ^ 59
def prefixEnd_3387315 : Nat := 4983230072969 + 3 ^ 40 * 3387315 * 2
def baseEnd_3387315 : Nat := 386515716263226632929895

theorem tailTrace_3387315 : CollatzResearch.WordTrace tailWord_3387315 prefixEnd_3387315 386515716263226632929895 := by
  unfold tailWord_3387315
  simp only [CollatzResearch.WordTrace]
  refine ⟨123545527723343737189787399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82363685148895824793191599 123545527723343737189787399)
  ·
    refine ⟨185318291585015605784681099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123545527723343737189787399 185318291585015605784681099)
    ·
      refine ⟨277977437377523408677021649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185318291585015605784681099 277977437377523408677021649)
      ·
        refine ⟨208483078033142556507766237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277977437377523408677021649 208483078033142556507766237)
        ·
          refine ⟨78181154262428458690412339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208483078033142556507766237 78181154262428458690412339)
          ·
            refine ⟨117271731393642688035618509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78181154262428458690412339 117271731393642688035618509)
            ·
              refine ⟨43976899272616008013356941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117271731393642688035618509 43976899272616008013356941)
              ·
                refine ⟨16491337227231003005008853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43976899272616008013356941 16491337227231003005008853)
                ·
                  refine ⟨386515716263226632929895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16491337227231003005008853 386515716263226632929895)
                  ·
                    rfl

theorem cell22_3387315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_3387315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387315 prefixEnd_3387315 := by exact prefixLift 3387315
  have htrace : WordTrace (prefixWord ++ tailWord_3387315) baseStart_3387315 baseEnd_3387315 := by
    simpa [prefixWord, tailWord_3387315, baseEnd_3387315] using wordTrace_append hprefix tailTrace_3387315
  have hstable : (prefixWord ++ tailWord_3387315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387315).length < 2 ^ (prefixWord ++ tailWord_3387315).sum := by decide
  have hdescent : baseEnd_3387315 < baseStart_3387315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387413 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3387413 : Nat := 118140960795 + 3387413 * 2 ^ 59
def prefixEnd_3387413 : Nat := 4983230072969 + 3 ^ 40 * 3387413 * 2
def baseEnd_3387413 : Nat := 1159580696192440309839385

theorem tailTrace_3387413 : CollatzResearch.WordTrace tailWord_3387413 prefixEnd_3387413 1159580696192440309839385 := by
  unfold tailWord_3387413
  simp only [CollatzResearch.WordTrace]
  refine ⟨123549102076988699926854893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82366068051325799951236595 123549102076988699926854893)
  ·
    refine ⟨46330913278870762472570585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123549102076988699926854893 46330913278870762472570585)
    ·
      refine ⟨34748184959153071854427939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46330913278870762472570585 34748184959153071854427939)
      ·
        refine ⟨52122277438729607781641909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34748184959153071854427939 52122277438729607781641909)
        ·
          refine ⟨4886463509880900729528929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52122277438729607781641909 4886463509880900729528929)
          ·
            refine ⟨3664847632410675547146697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4886463509880900729528929 3664847632410675547146697)
            ·
              refine ⟨2748635724308006660360023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3664847632410675547146697 2748635724308006660360023)
              ·
                refine ⟨4122953586462009990540035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748635724308006660360023 4122953586462009990540035)
                ·
                  refine ⟨6184430379693014985810053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4122953586462009990540035 6184430379693014985810053)
                  ·
                    refine ⟨1159580696192440309839385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184430379693014985810053 1159580696192440309839385)
                    ·
                      rfl

theorem cell22_3387413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3387413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387413 prefixEnd_3387413 := by exact prefixLift 3387413
  have htrace : WordTrace (prefixWord ++ tailWord_3387413) baseStart_3387413 baseEnd_3387413 := by
    simpa [prefixWord, tailWord_3387413, baseEnd_3387413] using wordTrace_append hprefix tailTrace_3387413
  have hstable : (prefixWord ++ tailWord_3387413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387413).length < 2 ^ (prefixWord ++ tailWord_3387413).sum := by decide
  have hdescent : baseEnd_3387413 < baseStart_3387413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387484 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 7]
def baseStart_3387484 : Nat := 118140960795 + 3387484 * 2 ^ 59
def prefixEnd_3387484 : Nat := 4983230072969 + 3 ^ 40 * 3387484 * 2
def baseEnd_3387484 : Nat := 386535000314473263771389

theorem tailTrace_3387484 : CollatzResearch.WordTrace tailWord_3387484 prefixEnd_3387484 386535000314473263771389 := by
  unfold tailWord_3387484
  simp only [CollatzResearch.WordTrace]
  refine ⟨61775845829865739526344753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82367794439820986035126337 61775845829865739526344753)
  ·
    refine ⟨46331884372399304644758565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61775845829865739526344753 46331884372399304644758565)
    ·
      refine ⟨8687228319824869620892231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46331884372399304644758565 8687228319824869620892231)
      ·
        refine ⟨13030842479737304431338347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8687228319824869620892231 13030842479737304431338347)
        ·
          refine ⟨19546263719605956647007521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13030842479737304431338347 19546263719605956647007521)
          ·
            refine ⟨14659697789704467485255641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19546263719605956647007521 14659697789704467485255641)
            ·
              refine ⟨10994773342278350613941731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14659697789704467485255641 10994773342278350613941731)
              ·
                refine ⟨16492160013417525920912597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10994773342278350613941731 16492160013417525920912597)
                ·
                  refine ⟨386535000314473263771389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16492160013417525920912597 386535000314473263771389)
                  ·
                    rfl

theorem cell22_3387484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_3387484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387484 prefixEnd_3387484 := by exact prefixLift 3387484
  have htrace : WordTrace (prefixWord ++ tailWord_3387484) baseStart_3387484 baseEnd_3387484 := by
    simpa [prefixWord, tailWord_3387484, baseEnd_3387484] using wordTrace_append hprefix tailTrace_3387484
  have hstable : (prefixWord ++ tailWord_3387484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387484).length < 2 ^ (prefixWord ++ tailWord_3387484).sum := by decide
  have hdescent : baseEnd_3387484 < baseStart_3387484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387512 : List Nat := [2, 1, 2, 1, 1, 1, 3, 3, 8]
def baseStart_3387512 : Nat := 118140960795 + 3387512 * 2 ^ 59
def prefixEnd_3387512 : Nat := 4983230072969 + 3 ^ 40 * 3387512 * 2
def baseEnd_3387512 : Nat := 386538195305212350538027

theorem tailTrace_3387512 : CollatzResearch.WordTrace tailWord_3387512 prefixEnd_3387512 386538195305212350538027 := by
  unfold tailWord_3387512
  simp only [CollatzResearch.WordTrace]
  refine ⟨61776356451815019917354395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82368475269086693223139193 61776356451815019917354395)
  ·
    refine ⟨92664534677722529876031593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61776356451815019917354395 92664534677722529876031593)
    ·
      refine ⟨69498401008291897407023695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92664534677722529876031593 69498401008291897407023695)
      ·
        refine ⟨104247601512437846110535543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69498401008291897407023695 104247601512437846110535543)
        ·
          refine ⟨156371402268656769165803315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104247601512437846110535543 156371402268656769165803315)
          ·
            refine ⟨234557103402985153748704973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156371402268656769165803315 234557103402985153748704973)
            ·
              refine ⟨87958913776119432655764365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234557103402985153748704973 87958913776119432655764365)
              ·
                refine ⟨32984592666044787245911637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87958913776119432655764365 32984592666044787245911637)
                ·
                  refine ⟨386538195305212350538027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32984592666044787245911637 386538195305212350538027)
                  ·
                    rfl

theorem cell22_3387512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_3387512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387512 prefixEnd_3387512 := by exact prefixLift 3387512
  have htrace : WordTrace (prefixWord ++ tailWord_3387512) baseStart_3387512 baseEnd_3387512 := by
    simpa [prefixWord, tailWord_3387512, baseEnd_3387512] using wordTrace_append hprefix tailTrace_3387512
  have hstable : (prefixWord ++ tailWord_3387512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387512).length < 2 ^ (prefixWord ++ tailWord_3387512).sum := by decide
  have hdescent : baseEnd_3387512 < baseStart_3387512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387582 : List Nat := [4, 2, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_3387582 : Nat := 118140960795 + 3387582 * 2 ^ 59
def prefixEnd_3387582 : Nat := 4983230072969 + 3 ^ 40 * 3387582 * 2
def baseEnd_3387582 : Nat := 1159638548346180202363867

theorem tailTrace_3387582 : CollatzResearch.WordTrace tailWord_3387582 prefixEnd_3387582 1159638548346180202363867 := by
  unfold tailWord_3387582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15444408251672055223719625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82370177342250961193171333 15444408251672055223719625)
  ·
    refine ⟨11583306188754041417789719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15444408251672055223719625 11583306188754041417789719)
    ·
      refine ⟨17374959283131062126684579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11583306188754041417789719 17374959283131062126684579)
      ·
        refine ⟨26062438924696593190026869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17374959283131062126684579 26062438924696593190026869)
        ·
          refine ⟨2443353649190305611565019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26062438924696593190026869 2443353649190305611565019)
          ·
            refine ⟨3665030473785458417347529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443353649190305611565019 3665030473785458417347529)
            ·
              refine ⟨2748772855339093813010647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3665030473785458417347529 2748772855339093813010647)
              ·
                refine ⟨4123159283008640719515971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748772855339093813010647 4123159283008640719515971)
                ·
                  refine ⟨6184738924512961079273957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123159283008640719515971 6184738924512961079273957)
                  ·
                    refine ⟨1159638548346180202363867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184738924512961079273957 1159638548346180202363867)
                    ·
                      rfl

theorem cell22_3387582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_3387582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387582 prefixEnd_3387582 := by exact prefixLift 3387582
  have htrace : WordTrace (prefixWord ++ tailWord_3387582) baseStart_3387582 baseEnd_3387582 := by
    simpa [prefixWord, tailWord_3387582, baseEnd_3387582] using wordTrace_append hprefix tailTrace_3387582
  have hstable : (prefixWord ++ tailWord_3387582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387582).length < 2 ^ (prefixWord ++ tailWord_3387582).sum := by decide
  have hdescent : baseEnd_3387582 < baseStart_3387582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387612 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3387612 : Nat := 118140960795 + 3387612 * 2 ^ 59
def prefixEnd_3387612 : Nat := 4983230072969 + 3 ^ 40 * 3387612 * 2
def baseEnd_3387612 : Nat := 1159648817959270124113775

theorem tailTrace_3387612 : CollatzResearch.WordTrace tailWord_3387612 prefixEnd_3387612 1159648817959270124113775 := by
  unfold tailWord_3387612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61778180101633878456674545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82370906802178504608899393 61778180101633878456674545)
  ·
    refine ⟨46333635076225408842505909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61778180101633878456674545 46333635076225408842505909)
    ·
      refine ⟨4343778288396132078984929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46333635076225408842505909 4343778288396132078984929)
      ·
        refine ⟨3257833716297099059238697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4343778288396132078984929 3257833716297099059238697)
        ·
          refine ⟨2443375287222824294429023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3257833716297099059238697 2443375287222824294429023)
          ·
            refine ⟨3665062930834236441643535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443375287222824294429023 3665062930834236441643535)
            ·
              refine ⟨5497594396251354662465303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665062930834236441643535 5497594396251354662465303)
              ·
                refine ⟨8246391594377031993697955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497594396251354662465303 8246391594377031993697955)
                ·
                  refine ⟨12369587391565547990546933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8246391594377031993697955 12369587391565547990546933)
                  ·
                    refine ⟨1159648817959270124113775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12369587391565547990546933 1159648817959270124113775)
                    ·
                      rfl

theorem cell22_3387612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3387612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387612 prefixEnd_3387612 := by exact prefixLift 3387612
  have htrace : WordTrace (prefixWord ++ tailWord_3387612) baseStart_3387612 baseEnd_3387612 := by
    simpa [prefixWord, tailWord_3387612, baseEnd_3387612] using wordTrace_append hprefix tailTrace_3387612
  have hstable : (prefixWord ++ tailWord_3387612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387612).length < 2 ^ (prefixWord ++ tailWord_3387612).sum := by decide
  have hdescent : baseEnd_3387612 < baseStart_3387612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387623 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3387623 : Nat := 118140960795 + 3387623 * 2 ^ 59
def prefixEnd_3387623 : Nat := 4983230072969 + 3 ^ 40 * 3387623 * 2
def baseEnd_3387623 : Nat := 1159652583484069762088741

theorem tailTrace_3387623 : CollatzResearch.WordTrace tailWord_3387623 prefixEnd_3387623 1159652583484069762088741 := by
  unfold tailWord_3387623
  simp only [CollatzResearch.WordTrace]
  refine ⟨123556761406227905791999523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82371174270818603861333015 123556761406227905791999523)
  ·
    refine ⟨185335142109341858687999285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123556761406227905791999523 185335142109341858687999285)
    ·
      refine ⟨17375169572750799251999933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185335142109341858687999285 17375169572750799251999933)
      ·
        refine ⟨6515688589781549719499975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17375169572750799251999933 6515688589781549719499975)
        ·
          refine ⟨9773532884672324579249963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515688589781549719499975 9773532884672324579249963)
          ·
            refine ⟨14660299327008486868874945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9773532884672324579249963 14660299327008486868874945)
            ·
              refine ⟨10995224495256365151656209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14660299327008486868874945 10995224495256365151656209)
              ·
                refine ⟨8246418371442273863742157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10995224495256365151656209 8246418371442273863742157)
                ·
                  refine ⟨3092406889290852698903309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8246418371442273863742157 3092406889290852698903309)
                  ·
                    refine ⟨1159652583484069762088741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092406889290852698903309 1159652583484069762088741)
                    ·
                      rfl

theorem cell22_3387623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3387623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387623 prefixEnd_3387623 := by exact prefixLift 3387623
  have htrace : WordTrace (prefixWord ++ tailWord_3387623) baseStart_3387623 baseEnd_3387623 := by
    simpa [prefixWord, tailWord_3387623, baseEnd_3387623] using wordTrace_append hprefix tailTrace_3387623
  have hstable : (prefixWord ++ tailWord_3387623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387623).length < 2 ^ (prefixWord ++ tailWord_3387623).sum := by decide
  have hdescent : baseEnd_3387623 < baseStart_3387623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387696 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 4, 3]
def baseStart_3387696 : Nat := 118140960795 + 3387696 * 2 ^ 59
def prefixEnd_3387696 : Nat := 4983230072969 + 3 ^ 40 * 3387696 * 2
def baseEnd_3387696 : Nat := 1159677572875921905013517

theorem tailTrace_3387696 : CollatzResearch.WordTrace tailWord_3387696 prefixEnd_3387696 1159677572875921905013517 := by
  unfold tailWord_3387696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61779711967481719629703471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82372949289975626172937961 61779711967481719629703471)
  ·
    refine ⟨92669567951222579444555207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61779711967481719629703471 92669567951222579444555207)
    ·
      refine ⟨139004351926833869166832811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92669567951222579444555207 139004351926833869166832811)
      ·
        refine ⟨208506527890250803750249217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139004351926833869166832811 208506527890250803750249217)
        ·
          refine ⟨156379895917688102812686913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208506527890250803750249217 156379895917688102812686913)
          ·
            refine ⟨117284921938266077109515185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156379895917688102812686913 117284921938266077109515185)
            ·
              refine ⟨87963691453699557832136389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117284921938266077109515185 87963691453699557832136389)
              ·
                refine ⟨16493192147568667093525573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87963691453699557832136389 16493192147568667093525573)
                ·
                  refine ⟨3092473527669125080036045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16493192147568667093525573 3092473527669125080036045)
                  ·
                    refine ⟨1159677572875921905013517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092473527669125080036045 1159677572875921905013517)
                    ·
                      rfl

theorem cell22_3387696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 3].length) (baseStart_3387696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387696 prefixEnd_3387696 := by exact prefixLift 3387696
  have htrace : WordTrace (prefixWord ++ tailWord_3387696) baseStart_3387696 baseEnd_3387696 := by
    simpa [prefixWord, tailWord_3387696, baseEnd_3387696] using wordTrace_append hprefix tailTrace_3387696
  have hstable : (prefixWord ++ tailWord_3387696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387696).length < 2 ^ (prefixWord ++ tailWord_3387696).sum := by decide
  have hdescent : baseEnd_3387696 < baseStart_3387696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387709 : List Nat := [1, 4, 1, 16]
def baseStart_3387709 : Nat := 118140960795 + 3387709 * 2 ^ 59
def prefixEnd_3387709 : Nat := 4983230072969 + 3 ^ 40 * 3387709 * 2
def baseEnd_3387709 : Nat := 1590784668095465301013

theorem tailTrace_3387709 : CollatzResearch.WordTrace tailWord_3387709 prefixEnd_3387709 1590784668095465301013 := by
  unfold tailWord_3387709
  simp only [CollatzResearch.WordTrace]
  refine ⟨123559898083916342479630181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82373265389277561653086787 123559898083916342479630181)
  ·
    refine ⟨23167480890734314214930659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123559898083916342479630181 23167480890734314214930659)
    ·
      refine ⟨34751221336101471322395989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23167480890734314214930659 34751221336101471322395989)
      ·
        refine ⟨1590784668095465301013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 34751221336101471322395989 1590784668095465301013)
        ·
          rfl

theorem cell22_3387709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 16].length) (baseStart_3387709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387709 prefixEnd_3387709 := by exact prefixLift 3387709
  have htrace : WordTrace (prefixWord ++ tailWord_3387709) baseStart_3387709 baseEnd_3387709 := by
    simpa [prefixWord, tailWord_3387709, baseEnd_3387709] using wordTrace_append hprefix tailTrace_3387709
  have hstable : (prefixWord ++ tailWord_3387709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387709).length < 2 ^ (prefixWord ++ tailWord_3387709).sum := by decide
  have hdescent : baseEnd_3387709 < baseStart_3387709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387711 : List Nat := [1, 1, 2, 2, 4, 1, 1, 4, 2, 4]
def baseStart_3387711 : Nat := 118140960795 + 3387711 * 2 ^ 59
def prefixEnd_3387711 : Nat := 4983230072969 + 3 ^ 40 * 3387711 * 2
def baseEnd_3387711 : Nat := 1159682707682466865888471

theorem tailTrace_3387711 : CollatzResearch.WordTrace tailWord_3387711 prefixEnd_3387711 1159682707682466865888471 := by
  unfold tailWord_3387711
  simp only [CollatzResearch.WordTrace]
  refine ⟨123559971029909096821202987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82373314019939397880801991 123559971029909096821202987)
  ·
    refine ⟨185339956544863645231804481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123559971029909096821202987 185339956544863645231804481)
    ·
      refine ⟨139004967408647733923853361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185339956544863645231804481 139004967408647733923853361)
      ·
        refine ⟨104253725556485800442890021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139004967408647733923853361 104253725556485800442890021)
        ·
          refine ⟨19547573541841087583041879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104253725556485800442890021 19547573541841087583041879)
          ·
            refine ⟨29321360312761631374562819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19547573541841087583041879 29321360312761631374562819)
            ·
              refine ⟨43982040469142447061844229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29321360312761631374562819 43982040469142447061844229)
              ·
                refine ⟨8246632587964208824095793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43982040469142447061844229 8246632587964208824095793)
                ·
                  refine ⟨6184974440973156618071845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246632587964208824095793 6184974440973156618071845)
                  ·
                    refine ⟨1159682707682466865888471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6184974440973156618071845 1159682707682466865888471)
                    ·
                      rfl

theorem cell22_3387711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_3387711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387711 prefixEnd_3387711 := by exact prefixLift 3387711
  have htrace : WordTrace (prefixWord ++ tailWord_3387711) baseStart_3387711 baseEnd_3387711 := by
    simpa [prefixWord, tailWord_3387711, baseEnd_3387711] using wordTrace_append hprefix tailTrace_3387711
  have hstable : (prefixWord ++ tailWord_3387711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387711).length < 2 ^ (prefixWord ++ tailWord_3387711).sum := by decide
  have hdescent : baseEnd_3387711 < baseStart_3387711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387739 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_3387739 : Nat := 118140960795 + 3387739 * 2 ^ 59
def prefixEnd_3387739 : Nat := 4983230072969 + 3 ^ 40 * 3387739 * 2
def baseEnd_3387739 : Nat := 1159692292654684126188385

theorem tailTrace_3387739 : CollatzResearch.WordTrace tailWord_3387739 prefixEnd_3387739 1159692292654684126188385 := by
  unfold tailWord_3387739
  simp only [CollatzResearch.WordTrace]
  refine ⟨123560992273807657603222271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82373994849205105068814847 123560992273807657603222271)
  ·
    refine ⟨185341488410711486404833407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123560992273807657603222271 185341488410711486404833407)
    ·
      refine ⟨278012232616067229607250111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185341488410711486404833407 278012232616067229607250111)
      ·
        refine ⟨417018348924100844410875167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278012232616067229607250111 417018348924100844410875167)
        ·
          refine ⟨625527523386151266616312751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417018348924100844410875167 625527523386151266616312751)
          ·
            refine ⟨938291285079226899924469127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625527523386151266616312751 938291285079226899924469127)
            ·
              refine ⟨1407436927618840349886703691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938291285079226899924469127 1407436927618840349886703691)
              ·
                refine ⟨2111155391428260524830055537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407436927618840349886703691 2111155391428260524830055537)
                ·
                  refine ⟨1583366543571195393622541653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2111155391428260524830055537 1583366543571195393622541653)
                  ·
                    refine ⟨1159692292654684126188385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1583366543571195393622541653 1159692292654684126188385)
                    ·
                      rfl

theorem cell22_3387739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_3387739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387739 prefixEnd_3387739 := by exact prefixLift 3387739
  have htrace : WordTrace (prefixWord ++ tailWord_3387739) baseStart_3387739 baseEnd_3387739 := by
    simpa [prefixWord, tailWord_3387739, baseEnd_3387739] using wordTrace_append hprefix tailTrace_3387739
  have hstable : (prefixWord ++ tailWord_3387739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387739).length < 2 ^ (prefixWord ++ tailWord_3387739).sum := by decide
  have hdescent : baseEnd_3387739 < baseStart_3387739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387771 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 7]
def baseStart_3387771 : Nat := 118140960795 + 3387771 * 2 ^ 59
def prefixEnd_3387771 : Nat := 4983230072969 + 3 ^ 40 * 3387771 * 2
def baseEnd_3387771 : Nat := 386567748969548903129429

theorem tailTrace_3387771 : CollatzResearch.WordTrace tailWord_3387771 prefixEnd_3387771 386567748969548903129429 := by
  unfold tailWord_3387771
  simp only [CollatzResearch.WordTrace]
  refine ⟨123562159409691727068387167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82374772939794484712258111 123562159409691727068387167)
  ·
    refine ⟨185343239114537590602580751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123562159409691727068387167 185343239114537590602580751)
    ·
      refine ⟨278014858671806385903871127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185343239114537590602580751 278014858671806385903871127)
      ·
        refine ⟨417022288007709578855806691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278014858671806385903871127 417022288007709578855806691)
        ·
          refine ⟨625533432011564368283710037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417022288007709578855806691 625533432011564368283710037)
          ·
            refine ⟨7330469906385519940824727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 625533432011564368283710037 7330469906385519940824727)
            ·
              refine ⟨10995704859578279911237091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330469906385519940824727 10995704859578279911237091)
              ·
                refine ⟨16493557289367419866855637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10995704859578279911237091 16493557289367419866855637)
                ·
                  refine ⟨386567748969548903129429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16493557289367419866855637 386567748969548903129429)
                  ·
                    rfl

theorem cell22_3387771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 7].length) (baseStart_3387771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387771 prefixEnd_3387771 := by exact prefixLift 3387771
  have htrace : WordTrace (prefixWord ++ tailWord_3387771) baseStart_3387771 baseEnd_3387771 := by
    simpa [prefixWord, tailWord_3387771, baseEnd_3387771] using wordTrace_append hprefix tailTrace_3387771
  have hstable : (prefixWord ++ tailWord_3387771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387771).length < 2 ^ (prefixWord ++ tailWord_3387771).sum := by decide
  have hdescent : baseEnd_3387771 < baseStart_3387771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387833 : List Nat := [1, 2, 1, 4, 3, 1, 3, 1, 6]
def baseStart_3387833 : Nat := 118140960795 + 3387833 * 2 ^ 59
def prefixEnd_3387833 : Nat := 4983230072969 + 3 ^ 40 * 3387833 * 2
def baseEnd_3387833 : Nat := 386574823591899738112699

theorem tailTrace_3387833 : CollatzResearch.WordTrace tailWord_3387833 prefixEnd_3387833 386574823591899738112699 := by
  unfold tailWord_3387833
  simp only [CollatzResearch.WordTrace]
  refine ⟨123564420735467111657144153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82376280490311407771429435 123564420735467111657144153)
  ·
    refine ⟨92673315551600333742858115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123564420735467111657144153 92673315551600333742858115)
    ·
      refine ⟨139009973327400500614287173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92673315551600333742858115 139009973327400500614287173)
      ·
        refine ⟨26064369998887593865178845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139009973327400500614287173 26064369998887593865178845)
        ·
          refine ⟨9774138749582847699442067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26064369998887593865178845 9774138749582847699442067)
          ·
            refine ⟨14661208124374271549163101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774138749582847699442067 14661208124374271549163101)
            ·
              refine ⟨5497953046640351830936163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14661208124374271549163101 5497953046640351830936163)
              ·
                refine ⟨8246929569960527746404245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497953046640351830936163 8246929569960527746404245)
                ·
                  refine ⟨386574823591899738112699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8246929569960527746404245 386574823591899738112699)
                  ·
                    rfl

theorem cell22_3387833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_3387833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387833 prefixEnd_3387833 := by exact prefixLift 3387833
  have htrace : WordTrace (prefixWord ++ tailWord_3387833) baseStart_3387833 baseEnd_3387833 := by
    simpa [prefixWord, tailWord_3387833, baseEnd_3387833] using wordTrace_append hprefix tailTrace_3387833
  have hstable : (prefixWord ++ tailWord_3387833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387833).length < 2 ^ (prefixWord ++ tailWord_3387833).sum := by decide
  have hdescent : baseEnd_3387833 < baseStart_3387833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387852 : List Nat := [2, 2, 1, 4, 3, 2, 1, 2, 1, 4]
def baseStart_3387852 : Nat := 118140960795 + 3387852 * 2 ^ 59
def prefixEnd_3387852 : Nat := 4983230072969 + 3 ^ 40 * 3387852 * 2
def baseEnd_3387852 : Nat := 1159730974863989498113039

theorem tailTrace_3387852 : CollatzResearch.WordTrace tailWord_3387852 prefixEnd_3387852 1159730974863989498113039 := by
  unfold tailWord_3387852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61782556861199138951042905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82376742481598851934723873 61782556861199138951042905)
  ·
    refine ⟨46336917645899354213282179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61782556861199138951042905 46336917645899354213282179)
    ·
      refine ⟨69505376468849031319923269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46336917645899354213282179 69505376468849031319923269)
      ·
        refine ⟨13032258087909193372485613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69505376468849031319923269 13032258087909193372485613)
        ·
          refine ⟨4887096782965947514682105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13032258087909193372485613 4887096782965947514682105)
          ·
            refine ⟨3665322587224460636011579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4887096782965947514682105 3665322587224460636011579)
            ·
              refine ⟨5497983880836690954017369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665322587224460636011579 5497983880836690954017369)
              ·
                refine ⟨4123487910627518215513027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497983880836690954017369 4123487910627518215513027)
                ·
                  refine ⟨6185231865941277323269541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123487910627518215513027 6185231865941277323269541)
                  ·
                    refine ⟨1159730974863989498113039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185231865941277323269541 1159730974863989498113039)
                    ·
                      rfl

theorem cell22_3387852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 1, 4].length) (baseStart_3387852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387852 prefixEnd_3387852 := by exact prefixLift 3387852
  have htrace : WordTrace (prefixWord ++ tailWord_3387852) baseStart_3387852 baseEnd_3387852 := by
    simpa [prefixWord, tailWord_3387852, baseEnd_3387852] using wordTrace_append hprefix tailTrace_3387852
  have hstable : (prefixWord ++ tailWord_3387852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387852).length < 2 ^ (prefixWord ++ tailWord_3387852).sum := by decide
  have hdescent : baseEnd_3387852 < baseStart_3387852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387882 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3387882 : Nat := 118140960795 + 3387882 * 2 ^ 59
def prefixEnd_3387882 : Nat := 4983230072969 + 3 ^ 40 * 3387882 * 2
def baseEnd_3387882 : Nat := 1159741244477079419862947

theorem tailTrace_3387882 : CollatzResearch.WordTrace tailWord_3387882 prefixEnd_3387882 1159741244477079419862947 := by
  unfold tailWord_3387882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891551978072398256419475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82377471941526395350451933 30891551978072398256419475)
  ·
    refine ⟨46337327967108597384629213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30891551978072398256419475 46337327967108597384629213)
    ·
      refine ⟨17376497987665724019235955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46337327967108597384629213 17376497987665724019235955)
      ·
        refine ⟨26064746981498586028853933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376497987665724019235955 26064746981498586028853933)
        ·
          refine ⟨9774280118061969760820225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26064746981498586028853933 9774280118061969760820225)
          ·
            refine ⟨7330710088546477320615169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9774280118061969760820225 7330710088546477320615169)
            ·
              refine ⟨5498032566409857990461377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7330710088546477320615169 5498032566409857990461377)
              ·
                refine ⟨4123524424807393492846033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498032566409857990461377 4123524424807393492846033)
                ·
                  refine ⟨3092643318605545119634525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4123524424807393492846033 3092643318605545119634525)
                  ·
                    refine ⟨1159741244477079419862947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092643318605545119634525 1159741244477079419862947)
                    ·
                      rfl

theorem cell22_3387882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3387882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387882 prefixEnd_3387882 := by exact prefixLift 3387882
  have htrace : WordTrace (prefixWord ++ tailWord_3387882) baseStart_3387882 baseEnd_3387882 := by
    simpa [prefixWord, tailWord_3387882, baseEnd_3387882] using wordTrace_append hprefix tailTrace_3387882
  have hstable : (prefixWord ++ tailWord_3387882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387882).length < 2 ^ (prefixWord ++ tailWord_3387882).sum := by decide
  have hdescent : baseEnd_3387882 < baseStart_3387882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387891 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_3387891 : Nat := 118140960795 + 3387891 * 2 ^ 59
def prefixEnd_3387891 : Nat := 4983230072969 + 3 ^ 40 * 3387891 * 2
def baseEnd_3387891 : Nat := 1159744325361006396387919

theorem tailTrace_3387891 : CollatzResearch.WordTrace tailWord_3387891 prefixEnd_3387891 1159744325361006396387919 := by
  unfold tailWord_3387891
  simp only [CollatzResearch.WordTrace]
  refine ⟨123566536169256987562755527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82377690779504658375170351 123566536169256987562755527)
  ·
    refine ⟨185349804253885481344133291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123566536169256987562755527 185349804253885481344133291)
    ·
      refine ⟨278024706380828222016199937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185349804253885481344133291 278024706380828222016199937)
      ·
        refine ⟨208518529785621166512149953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278024706380828222016199937 208518529785621166512149953)
        ·
          refine ⟨156388897339215874884112465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208518529785621166512149953 156388897339215874884112465)
          ·
            refine ⟨117291673004411906163084349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156388897339215874884112465 117291673004411906163084349)
            ·
              refine ⟨43984377376654464811156631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117291673004411906163084349 43984377376654464811156631)
              ·
                refine ⟨65976566064981697216734947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43984377376654464811156631 65976566064981697216734947)
                ·
                  refine ⟨98964849097472545825102421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65976566064981697216734947 98964849097472545825102421)
                  ·
                    refine ⟨1159744325361006396387919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98964849097472545825102421 1159744325361006396387919)
                    ·
                      rfl

theorem cell22_3387891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_3387891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387891 prefixEnd_3387891 := by exact prefixLift 3387891
  have htrace : WordTrace (prefixWord ++ tailWord_3387891) baseStart_3387891 baseEnd_3387891 := by
    simpa [prefixWord, tailWord_3387891, baseEnd_3387891] using wordTrace_append hprefix tailTrace_3387891
  have hstable : (prefixWord ++ tailWord_3387891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387891).length < 2 ^ (prefixWord ++ tailWord_3387891).sum := by decide
  have hdescent : baseEnd_3387891 < baseStart_3387891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387944 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 1, 3]
def baseStart_3387944 : Nat := 118140960795 + 3387944 * 2 ^ 59
def prefixEnd_3387944 : Nat := 4983230072969 + 3 ^ 40 * 3387944 * 2
def baseEnd_3387944 : Nat := 1159762468344131924812757

theorem tailTrace_3387944 : CollatzResearch.WordTrace tailWord_3387944 prefixEnd_3387944 1159762468344131924812757 := by
  unfold tailWord_3387944
  simp only [CollatzResearch.WordTrace]
  refine ⟨61784234619032488807217443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82378979492043318409623257 61784234619032488807217443)
  ·
    refine ⟨92676351928548733210826165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61784234619032488807217443 92676351928548733210826165)
    ·
      refine ⟨8688407993301443738514953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92676351928548733210826165 8688407993301443738514953)
      ·
        refine ⟨6516305994976082803886215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8688407993301443738514953 6516305994976082803886215)
        ·
          refine ⟨9774458992464124205829323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516305994976082803886215 9774458992464124205829323)
          ·
            refine ⟨14661688488696186308743985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774458992464124205829323 14661688488696186308743985)
            ·
              refine ⟨10996266366522139731557989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14661688488696186308743985 10996266366522139731557989)
              ·
                refine ⟨2061799943722901199667123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10996266366522139731557989 2061799943722901199667123)
                ·
                  refine ⟨3092699915584351799500685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061799943722901199667123 3092699915584351799500685)
                  ·
                    refine ⟨1159762468344131924812757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092699915584351799500685 1159762468344131924812757)
                    ·
                      rfl

theorem cell22_3387944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_3387944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387944 prefixEnd_3387944 := by exact prefixLift 3387944
  have htrace : WordTrace (prefixWord ++ tailWord_3387944) baseStart_3387944 baseEnd_3387944 := by
    simpa [prefixWord, tailWord_3387944, baseEnd_3387944] using wordTrace_append hprefix tailTrace_3387944
  have hstable : (prefixWord ++ tailWord_3387944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387944).length < 2 ^ (prefixWord ++ tailWord_3387944).sum := by decide
  have hdescent : baseEnd_3387944 < baseStart_3387944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387953 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_3387953 : Nat := 118140960795 + 3387953 * 2 ^ 59
def prefixEnd_3387953 : Nat := 4983230072969 + 3 ^ 40 * 3387953 * 2
def baseEnd_3387953 : Nat := 1159765549228058901337729

theorem tailTrace_3387953 : CollatzResearch.WordTrace tailWord_3387953 prefixEnd_3387953 1159765549228058901337729 := by
  unfold tailWord_3387953
  simp only [CollatzResearch.WordTrace]
  refine ⟨123568797495032372151512513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82379198330021581434341675 123568797495032372151512513)
  ·
    refine ⟨92676598121274279113634385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123568797495032372151512513 92676598121274279113634385)
    ·
      refine ⟨69507448590955709335225789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92676598121274279113634385 69507448590955709335225789)
      ·
        refine ⟨26065293221608391000709671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69507448590955709335225789 26065293221608391000709671)
        ·
          refine ⟨39097939832412586501064507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26065293221608391000709671 39097939832412586501064507)
          ·
            refine ⟨58646909748618879751596761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39097939832412586501064507 58646909748618879751596761)
            ·
              refine ⟨43985182311464159813697571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58646909748618879751596761 43985182311464159813697571)
              ·
                refine ⟨65977773467196239720546357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43985182311464159813697571 65977773467196239720546357)
                ·
                  refine ⟨6185416262549647473801221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65977773467196239720546357 6185416262549647473801221)
                  ·
                    refine ⟨1159765549228058901337729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185416262549647473801221 1159765549228058901337729)
                    ·
                      rfl

theorem cell22_3387953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_3387953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387953 prefixEnd_3387953 := by exact prefixLift 3387953
  have htrace : WordTrace (prefixWord ++ tailWord_3387953) baseStart_3387953 baseEnd_3387953 := by
    simpa [prefixWord, tailWord_3387953, baseEnd_3387953] using wordTrace_append hprefix tailTrace_3387953
  have hstable : (prefixWord ++ tailWord_3387953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387953).length < 2 ^ (prefixWord ++ tailWord_3387953).sum := by decide
  have hdescent : baseEnd_3387953 < baseStart_3387953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387968 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 6]
def baseStart_3387968 : Nat := 118140960795 + 3387968 * 2 ^ 59
def prefixEnd_3387968 : Nat := 4983230072969 + 3 ^ 40 * 3387968 * 2
def baseEnd_3387968 : Nat := 386590228011534620737561

theorem tailTrace_3387968 : CollatzResearch.WordTrace tailWord_3387968 prefixEnd_3387968 386590228011534620737561 := by
  unfold tailWord_3387968
  simp only [CollatzResearch.WordTrace]
  refine ⟨61784672294989014856654279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82379563059985353142205705 61784672294989014856654279)
  ·
    refine ⟨92677008442483522284981419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61784672294989014856654279 92677008442483522284981419)
    ·
      refine ⟨139015512663725283427472129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92677008442483522284981419 139015512663725283427472129)
      ·
        refine ⟨104261634497793962570604097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139015512663725283427472129 104261634497793962570604097)
        ·
          refine ⟨78196225873345471927953073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104261634497793962570604097 78196225873345471927953073)
          ·
            refine ⟨58647169405009103945964805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78196225873345471927953073 58647169405009103945964805)
            ·
              refine ⟨10996344263439206989868401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58647169405009103945964805 10996344263439206989868401)
              ·
                refine ⟨8247258197579405242401301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996344263439206989868401 8247258197579405242401301)
                ·
                  refine ⟨386590228011534620737561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8247258197579405242401301 386590228011534620737561)
                  ·
                    rfl

theorem cell22_3387968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_3387968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387968 prefixEnd_3387968 := by exact prefixLift 3387968
  have htrace : WordTrace (prefixWord ++ tailWord_3387968) baseStart_3387968 baseEnd_3387968 := by
    simpa [prefixWord, tailWord_3387968, baseEnd_3387968] using wordTrace_append hprefix tailTrace_3387968
  have hstable : (prefixWord ++ tailWord_3387968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387968).length < 2 ^ (prefixWord ++ tailWord_3387968).sum := by decide
  have hdescent : baseEnd_3387968 < baseStart_3387968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387983 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 1, 5]
def baseStart_3387983 : Nat := 118140960795 + 3387983 * 2 ^ 59
def prefixEnd_3387983 : Nat := 4983230072969 + 3 ^ 40 * 3387983 * 2
def baseEnd_3387983 : Nat := 1159775818841148823087637

theorem tailTrace_3387983 : CollatzResearch.WordTrace tailWord_3387983 prefixEnd_3387983 1159775818841148823087637 := by
  unfold tailWord_3387983
  simp only [CollatzResearch.WordTrace]
  refine ⟨123569891684923687275104603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82379927789949124850069735 123569891684923687275104603)
  ·
    refine ⟨185354837527385530912656905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123569891684923687275104603 185354837527385530912656905)
    ·
      refine ⟨139016128145539148184492679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185354837527385530912656905 139016128145539148184492679)
      ·
        refine ⟨208524192218308722276739019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139016128145539148184492679 208524192218308722276739019)
        ·
          refine ⟨312786288327463083415108529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208524192218308722276739019 312786288327463083415108529)
          ·
            refine ⟨234589716245597312561331397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312786288327463083415108529 234589716245597312561331397)
            ·
              refine ⟨43985571796049496105249637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234589716245597312561331397 43985571796049496105249637)
              ·
                refine ⟨8247294711759280519734307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43985571796049496105249637 8247294711759280519734307)
                ·
                  refine ⟨12370942067638920779601461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8247294711759280519734307 12370942067638920779601461)
                  ·
                    refine ⟨1159775818841148823087637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12370942067638920779601461 1159775818841148823087637)
                    ·
                      rfl

theorem cell22_3387983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 5].length) (baseStart_3387983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3387983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3387983 prefixEnd_3387983 := by exact prefixLift 3387983
  have htrace : WordTrace (prefixWord ++ tailWord_3387983) baseStart_3387983 baseEnd_3387983 := by
    simpa [prefixWord, tailWord_3387983, baseEnd_3387983] using wordTrace_append hprefix tailTrace_3387983
  have hstable : (prefixWord ++ tailWord_3387983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387983).length < 2 ^ (prefixWord ++ tailWord_3387983).sum := by decide
  have hdescent : baseEnd_3387983 < baseStart_3387983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388000 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 4, 3]
def baseStart_3388000 : Nat := 118140960795 + 3388000 * 2 ^ 59
def prefixEnd_3388000 : Nat := 4983230072969 + 3 ^ 40 * 3388000 * 2
def baseEnd_3388000 : Nat := 1159781638288566445412585

theorem tailTrace_3388000 : CollatzResearch.WordTrace tailWord_3388000 prefixEnd_3388000 1159781638288566445412585 := by
  unfold tailWord_3388000
  simp only [CollatzResearch.WordTrace]
  refine ⟨61785255862931049589236727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82380341150574732785648969 61785255862931049589236727)
  ·
    refine ⟨92677883794396574383855091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61785255862931049589236727 92677883794396574383855091)
    ·
      refine ⟨139016825691594861575782637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92677883794396574383855091 139016825691594861575782637)
      ·
        refine ⟨52131309634348073090918489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139016825691594861575782637 52131309634348073090918489)
        ·
          refine ⟨39098482225761054818188867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52131309634348073090918489 39098482225761054818188867)
          ·
            refine ⟨58647723338641582227283301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39098482225761054818188867 58647723338641582227283301)
            ·
              refine ⟨10996448125995296667615619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58647723338641582227283301 10996448125995296667615619)
              ·
                refine ⟨16494672188992945001423429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10996448125995296667615619 16494672188992945001423429)
                ·
                  refine ⟨3092751035436177187766893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16494672188992945001423429 3092751035436177187766893)
                  ·
                    refine ⟨1159781638288566445412585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092751035436177187766893 1159781638288566445412585)
                    ·
                      rfl

theorem cell22_3388000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_3388000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388000 prefixEnd_3388000 := by exact prefixLift 3388000
  have htrace : WordTrace (prefixWord ++ tailWord_3388000) baseStart_3388000 baseEnd_3388000 := by
    simpa [prefixWord, tailWord_3388000, baseEnd_3388000] using wordTrace_append hprefix tailTrace_3388000
  have hstable : (prefixWord ++ tailWord_3388000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388000).length < 2 ^ (prefixWord ++ tailWord_3388000).sum := by decide
  have hdescent : baseEnd_3388000 < baseStart_3388000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388021 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3388021 : Nat := 118140960795 + 3388021 * 2 ^ 59
def prefixEnd_3388021 : Nat := 4983230072969 + 3 ^ 40 * 3388021 * 2
def baseEnd_3388021 : Nat := 1159788827017729390637521

theorem tailTrace_3388021 : CollatzResearch.WordTrace tailWord_3388021 prefixEnd_3388021 1159788827017729390637521 := by
  unfold tailWord_3388021
  simp only [CollatzResearch.WordTrace]
  refine ⟨123571277658786019764987917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82380851772524013176658611 123571277658786019764987917)
  ·
    refine ⟨46339229122044757411870469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123571277658786019764987917 46339229122044757411870469)
    ·
      refine ⟨8688605460383392014725713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46339229122044757411870469 8688605460383392014725713)
      ·
        refine ⟨6516454095287544011044285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8688605460383392014725713 6516454095287544011044285)
        ·
          refine ⟨2443670285732829004141607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6516454095287544011044285 2443670285732829004141607)
          ·
            refine ⟨3665505428599243506212411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2443670285732829004141607 3665505428599243506212411)
            ·
              refine ⟨5498258142898865259318617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665505428599243506212411 5498258142898865259318617)
              ·
                refine ⟨4123693607174148944488963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498258142898865259318617 4123693607174148944488963)
                ·
                  refine ⟨6185540410761223416733445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123693607174148944488963 6185540410761223416733445)
                  ·
                    refine ⟨1159788827017729390637521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185540410761223416733445 1159788827017729390637521)
                    ·
                      rfl

theorem cell22_3388021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3388021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388021 prefixEnd_3388021 := by exact prefixLift 3388021
  have htrace : WordTrace (prefixWord ++ tailWord_3388021) baseStart_3388021 baseEnd_3388021 := by
    simpa [prefixWord, tailWord_3388021, baseEnd_3388021] using wordTrace_append hprefix tailTrace_3388021
  have hstable : (prefixWord ++ tailWord_3388021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388021).length < 2 ^ (prefixWord ++ tailWord_3388021).sum := by decide
  have hdescent : baseEnd_3388021 < baseStart_3388021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388028 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3388028 : Nat := 118140960795 + 3388028 * 2 ^ 59
def prefixEnd_3388028 : Nat := 4983230072969 + 3 ^ 40 * 3388028 * 2
def baseEnd_3388028 : Nat := 1159791223260783705712499

theorem tailTrace_3388028 : CollatzResearch.WordTrace tailWord_3388028 prefixEnd_3388028 1159791223260783705712499 := by
  unfold tailWord_3388028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61785766484880329980246369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82381021979840439973661825 61785766484880329980246369)
  ·
    refine ⟨46339324863660247485184777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61785766484880329980246369 46339324863660247485184777)
    ·
      refine ⟨34754493647745185613888583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46339324863660247485184777 34754493647745185613888583)
      ·
        refine ⟨52131740471617778420832875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34754493647745185613888583 52131740471617778420832875)
        ·
          refine ⟨78197610707426667631249313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52131740471617778420832875 78197610707426667631249313)
          ·
            refine ⟨58648208030570000723436985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78197610707426667631249313 58648208030570000723436985)
            ·
              refine ⟨43986156022927500542577739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58648208030570000723436985 43986156022927500542577739)
              ·
                refine ⟨65979234034391250813866609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43986156022927500542577739 65979234034391250813866609)
                ·
                  refine ⟨49484425525793438110399957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65979234034391250813866609 49484425525793438110399957)
                  ·
                    refine ⟨1159791223260783705712499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49484425525793438110399957 1159791223260783705712499)
                    ·
                      rfl

theorem cell22_3388028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3388028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388028 prefixEnd_3388028 := by exact prefixLift 3388028
  have htrace : WordTrace (prefixWord ++ tailWord_3388028) baseStart_3388028 baseEnd_3388028 := by
    simpa [prefixWord, tailWord_3388028, baseEnd_3388028] using wordTrace_append hprefix tailTrace_3388028
  have hstable : (prefixWord ++ tailWord_3388028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388028).length < 2 ^ (prefixWord ++ tailWord_3388028).sum := by decide
  have hdescent : baseEnd_3388028 < baseStart_3388028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388060 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3388060 : Nat := 118140960795 + 3388060 * 2 ^ 59
def prefixEnd_3388060 : Nat := 4983230072969 + 3 ^ 40 * 3388060 * 2
def baseEnd_3388060 : Nat := 1159802177514746288912401

theorem tailTrace_3388060 : CollatzResearch.WordTrace tailWord_3388060 prefixEnd_3388060 1159802177514746288912401 := by
  unfold tailWord_3388060
  simp only [CollatzResearch.WordTrace]
  refine ⟨61786350052822364712828817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82381800070429819617105089 61786350052822364712828817)
  ·
    refine ⟨46339762539616773534621613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61786350052822364712828817 46339762539616773534621613)
    ·
      refine ⟨17377410952356290075483105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46339762539616773534621613 17377410952356290075483105)
      ·
        refine ⟨13033058214267217556612329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17377410952356290075483105 13033058214267217556612329)
        ·
          refine ⟨9774793660700413167459247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13033058214267217556612329 9774793660700413167459247)
          ·
            refine ⟨14662190491050619751188871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774793660700413167459247 14662190491050619751188871)
            ·
              refine ⟨21993285736575929626783307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662190491050619751188871 21993285736575929626783307)
              ·
                refine ⟨32989928604863894440174961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21993285736575929626783307 32989928604863894440174961)
                ·
                  refine ⟨24742446453647920830131221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32989928604863894440174961 24742446453647920830131221)
                  ·
                    refine ⟨1159802177514746288912401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24742446453647920830131221 1159802177514746288912401)
                    ·
                      rfl

theorem cell22_3388060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3388060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388060 prefixEnd_3388060 := by exact prefixLift 3388060
  have htrace : WordTrace (prefixWord ++ tailWord_3388060) baseStart_3388060 baseEnd_3388060 := by
    simpa [prefixWord, tailWord_3388060, baseEnd_3388060] using wordTrace_append hprefix tailTrace_3388060
  have hstable : (prefixWord ++ tailWord_3388060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388060).length < 2 ^ (prefixWord ++ tailWord_3388060).sum := by decide
  have hdescent : baseEnd_3388060 < baseStart_3388060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388073 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_3388073 : Nat := 118140960795 + 3388073 * 2 ^ 59
def prefixEnd_3388073 : Nat := 4983230072969 + 3 ^ 40 * 3388073 * 2
def baseEnd_3388073 : Nat := 1159806627680418588337361

theorem tailTrace_3388073 : CollatzResearch.WordTrace tailWord_3388073 prefixEnd_3388073 1159806627680418588337361 := by
  unfold tailWord_3388073
  simp only [CollatzResearch.WordTrace]
  refine ⟨123573174254597632645880873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82382116169731755097253915 123573174254597632645880873)
  ·
    refine ⟨92679880690948224484410655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123573174254597632645880873 92679880690948224484410655)
    ·
      refine ⟨139019821036422336726615983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92679880690948224484410655 139019821036422336726615983)
      ·
        refine ⟨208529731554633505089923975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139019821036422336726615983 208529731554633505089923975)
        ·
          refine ⟨312794597331950257634885963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208529731554633505089923975 312794597331950257634885963)
          ·
            refine ⟨469191895997925386452328945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312794597331950257634885963 469191895997925386452328945)
            ·
              refine ⟨351893921998444039839246709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469191895997925386452328945 351893921998444039839246709)
              ·
                refine ⟨32990055187354128734929379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 351893921998444039839246709 32990055187354128734929379)
                ·
                  refine ⟨49485082781031193102394069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32990055187354128734929379 49485082781031193102394069)
                  ·
                    refine ⟨1159806627680418588337361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49485082781031193102394069 1159806627680418588337361)
                    ·
                      rfl

theorem cell22_3388073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_3388073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388073 prefixEnd_3388073 := by exact prefixLift 3388073
  have htrace : WordTrace (prefixWord ++ tailWord_3388073) baseStart_3388073 baseEnd_3388073 := by
    simpa [prefixWord, tailWord_3388073, baseEnd_3388073] using wordTrace_append hprefix tailTrace_3388073
  have hstable : (prefixWord ++ tailWord_3388073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388073).length < 2 ^ (prefixWord ++ tailWord_3388073).sum := by decide
  have hdescent : baseEnd_3388073 < baseStart_3388073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388109 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 7]
def baseStart_3388109 : Nat := 118140960795 + 3388109 * 2 ^ 59
def prefixEnd_3388109 : Nat := 4983230072969 + 3 ^ 40 * 3388109 * 2
def baseEnd_3388109 : Nat := 386606317072042164812417

theorem tailTrace_3388109 : CollatzResearch.WordTrace tailWord_3388109 prefixEnd_3388109 386606317072042164812417 := by
  unfold tailWord_3388109
  simp only [CollatzResearch.WordTrace]
  refine ⟨123574487282467210794191381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82382991521644807196127587 123574487282467210794191381)
  ·
    refine ⟨5792554091365650505977721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 123574487282467210794191381 5792554091365650505977721)
    ·
      refine ⟨4344415568524237879483291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5792554091365650505977721 4344415568524237879483291)
      ·
        refine ⟨6516623352786356819224937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344415568524237879483291 6516623352786356819224937)
        ·
          refine ⟨4887467514589767614418703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516623352786356819224937 4887467514589767614418703)
          ·
            refine ⟨7331201271884651421628055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887467514589767614418703 7331201271884651421628055)
            ·
              refine ⟨10996801907826977132442083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331201271884651421628055 10996801907826977132442083)
              ·
                refine ⟨16495202861740465698663125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10996801907826977132442083 16495202861740465698663125)
                ·
                  refine ⟨386606317072042164812417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16495202861740465698663125 386606317072042164812417)
                  ·
                    rfl

theorem cell22_3388109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_3388109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388109 prefixEnd_3388109 := by exact prefixLift 3388109
  have htrace : WordTrace (prefixWord ++ tailWord_3388109) baseStart_3388109 baseEnd_3388109 := by
    simpa [prefixWord, tailWord_3388109, baseEnd_3388109] using wordTrace_append hprefix tailTrace_3388109
  have hstable : (prefixWord ++ tailWord_3388109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388109).length < 2 ^ (prefixWord ++ tailWord_3388109).sum := by decide
  have hdescent : baseEnd_3388109 < baseStart_3388109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388120 : List Nat := [2, 1, 2, 2, 3, 2, 1, 3, 6]
def baseStart_3388120 : Nat := 118140960795 + 3388120 * 2 ^ 59
def prefixEnd_3388120 : Nat := 4983230072969 + 3 ^ 40 * 3388120 * 2
def baseEnd_3388120 : Nat := 386607572246975377470739

theorem tailTrace_3388120 : CollatzResearch.WordTrace tailWord_3388120 prefixEnd_3388120 386607572246975377470739 := by
  unfold tailWord_3388120
  simp only [CollatzResearch.WordTrace]
  refine ⟨61787444242713679836420907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82383258990284906448561209 61787444242713679836420907)
  ·
    refine ⟨92681166364070519754631361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61787444242713679836420907 92681166364070519754631361)
    ·
      refine ⟨69510874773052889815973521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92681166364070519754631361 69510874773052889815973521)
      ·
        refine ⟨52133156079789667361980141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69510874773052889815973521 52133156079789667361980141)
        ·
          refine ⟨19549933529921125260742553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52133156079789667361980141 19549933529921125260742553)
          ·
            refine ⟨14662450147440843945556915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19549933529921125260742553 14662450147440843945556915)
            ·
              refine ⟨21993675221161265918335373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662450147440843945556915 21993675221161265918335373)
              ·
                refine ⟨8247628207935474719375765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21993675221161265918335373 8247628207935474719375765)
                ·
                  refine ⟨386607572246975377470739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8247628207935474719375765 386607572246975377470739)
                  ·
                    rfl

theorem cell22_3388120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_3388120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388120 prefixEnd_3388120 := by exact prefixLift 3388120
  have htrace : WordTrace (prefixWord ++ tailWord_3388120) baseStart_3388120 baseEnd_3388120 := by
    simpa [prefixWord, tailWord_3388120, baseEnd_3388120] using wordTrace_append hprefix tailTrace_3388120
  have hstable : (prefixWord ++ tailWord_3388120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388120).length < 2 ^ (prefixWord ++ tailWord_3388120).sum := by decide
  have hdescent : baseEnd_3388120 < baseStart_3388120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388167 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 4, 4]
def baseStart_3388167 : Nat := 118140960795 + 3388167 * 2 ^ 59
def prefixEnd_3388167 : Nat := 4983230072969 + 3 ^ 40 * 3388167 * 2
def baseEnd_3388167 : Nat := 1159838805801433676487073

theorem tailTrace_3388167 : CollatzResearch.WordTrace tailWord_3388167 prefixEnd_3388167 1159838805801433676487073 := by
  unfold tailWord_3388167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123576602716257086699802755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82384401810838057799868503 123576602716257086699802755)
  ·
    refine ⟨185364904074385630049704133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123576602716257086699802755 185364904074385630049704133)
    ·
      refine ⟨34755919513947305634319525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185364904074385630049704133 34755919513947305634319525)
      ·
        refine ⟨6516734908865119806434911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34755919513947305634319525 6516734908865119806434911)
        ·
          refine ⟨9775102363297679709652367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516734908865119806434911 9775102363297679709652367)
          ·
            refine ⟨14662653544946519564478551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775102363297679709652367 14662653544946519564478551)
            ·
              refine ⟨21993980317419779346717827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662653544946519564478551 21993980317419779346717827)
              ·
                refine ⟨32990970476129669020076741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21993980317419779346717827 32990970476129669020076741)
                ·
                  refine ⟨6185806964274312941264389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32990970476129669020076741 6185806964274312941264389)
                  ·
                    refine ⟨1159838805801433676487073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6185806964274312941264389 1159838805801433676487073)
                    ·
                      rfl

theorem cell22_3388167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_3388167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388167 prefixEnd_3388167 := by exact prefixLift 3388167
  have htrace : WordTrace (prefixWord ++ tailWord_3388167) baseStart_3388167 baseEnd_3388167 := by
    simpa [prefixWord, tailWord_3388167, baseEnd_3388167] using wordTrace_append hprefix tailTrace_3388167
  have hstable : (prefixWord ++ tailWord_3388167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388167).length < 2 ^ (prefixWord ++ tailWord_3388167).sum := by decide
  have hdescent : baseEnd_3388167 < baseStart_3388167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388197 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_3388197 : Nat := 118140960795 + 3388197 * 2 ^ 59
def prefixEnd_3388197 : Nat := 4983230072969 + 3 ^ 40 * 3388197 * 2
def baseEnd_3388197 : Nat := 1159849075414523598236981

theorem tailTrace_3388197 : CollatzResearch.WordTrace tailWord_3388197 prefixEnd_3388197 1159849075414523598236981 := by
  unfold tailWord_3388197
  simp only [CollatzResearch.WordTrace]
  refine ⟨123577696906148401823394845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82385131270765601215596563 123577696906148401823394845)
  ·
    refine ⟨46341636339805650683773067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123577696906148401823394845 46341636339805650683773067)
    ·
      refine ⟨69512454509708476025659601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46341636339805650683773067 69512454509708476025659601)
      ·
        refine ⟨52134340882281357019244701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69512454509708476025659601 52134340882281357019244701)
        ·
          refine ⟨19550377830855508882216763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52134340882281357019244701 19550377830855508882216763)
          ·
            refine ⟨29325566746283263323325145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19550377830855508882216763 29325566746283263323325145)
            ·
              refine ⟨21994175059712447492493859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29325566746283263323325145 21994175059712447492493859)
              ·
                refine ⟨32991262589568671238740789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994175059712447492493859 32991262589568671238740789)
                ·
                  refine ⟨3092930867772062928631949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32991262589568671238740789 3092930867772062928631949)
                  ·
                    refine ⟨1159849075414523598236981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3092930867772062928631949 1159849075414523598236981)
                    ·
                      rfl

theorem cell22_3388197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_3388197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388197 prefixEnd_3388197 := by exact prefixLift 3388197
  have htrace : WordTrace (prefixWord ++ tailWord_3388197) baseStart_3388197 baseEnd_3388197 := by
    simpa [prefixWord, tailWord_3388197, baseEnd_3388197] using wordTrace_append hprefix tailTrace_3388197
  have hstable : (prefixWord ++ tailWord_3388197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388197).length < 2 ^ (prefixWord ++ tailWord_3388197).sum := by decide
  have hdescent : baseEnd_3388197 < baseStart_3388197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388227 : List Nat := [1, 1, 1, 3, 1, 4, 4, 2, 5]
def baseStart_3388227 : Nat := 118140960795 + 3388227 * 2 ^ 59
def prefixEnd_3388227 : Nat := 4983230072969 + 3 ^ 40 * 3388227 * 2
def baseEnd_3388227 : Nat := 386619781675871173328963

theorem tailTrace_3388227 : CollatzResearch.WordTrace tailWord_3388227 prefixEnd_3388227 386619781675871173328963 := by
  unfold tailWord_3388227
  simp only [CollatzResearch.WordTrace]
  refine ⟨123578791096039716946986935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82385860730693144631324623 123578791096039716946986935)
  ·
    refine ⟨185368186644059575420480403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123578791096039716946986935 185368186644059575420480403)
    ·
      refine ⟨278052279966089363130720605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185368186644059575420480403 278052279966089363130720605)
      ·
        refine ⟨104269604987283511174020227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278052279966089363130720605 104269604987283511174020227)
        ·
          refine ⟨156404407480925266761030341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104269604987283511174020227 156404407480925266761030341)
          ·
            refine ⟨29325826402673487517693189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156404407480925266761030341 29325826402673487517693189)
            ·
              refine ⟨5498592450501278909567473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29325826402673487517693189 5498592450501278909567473)
              ·
                refine ⟨4123944337875959182175605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498592450501278909567473 4123944337875959182175605)
                ·
                  refine ⟨386619781675871173328963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4123944337875959182175605 386619781675871173328963)
                  ·
                    rfl

theorem cell22_3388227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 2, 5].length) (baseStart_3388227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388227 prefixEnd_3388227 := by exact prefixLift 3388227
  have htrace : WordTrace (prefixWord ++ tailWord_3388227) baseStart_3388227 baseEnd_3388227 := by
    simpa [prefixWord, tailWord_3388227, baseEnd_3388227] using wordTrace_append hprefix tailTrace_3388227
  have hstable : (prefixWord ++ tailWord_3388227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388227).length < 2 ^ (prefixWord ++ tailWord_3388227).sum := by decide
  have hdescent : baseEnd_3388227 < baseStart_3388227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388242 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 2, 5]
def baseStart_3388242 : Nat := 118140960795 + 3388242 * 2 ^ 59
def prefixEnd_3388242 : Nat := 4983230072969 + 3 ^ 40 * 3388242 * 2
def baseEnd_3388242 : Nat := 1159864479834158480861843

theorem tailTrace_3388242 : CollatzResearch.WordTrace tailWord_3388242 prefixEnd_3388242 1159864479834158480861843 := by
  unfold tailWord_3388242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30894834547746343627195745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82386225460656916339188653 30894834547746343627195745)
  ·
    refine ⟨23171125910809757720396809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30894834547746343627195745 23171125910809757720396809)
    ·
      refine ⟨17378344433107318290297607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23171125910809757720396809 17378344433107318290297607)
      ·
        refine ⟨26067516649660977435446411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17378344433107318290297607 26067516649660977435446411)
        ·
          refine ⟨39101274974491466153169617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26067516649660977435446411 39101274974491466153169617)
          ·
            refine ⟨29325956230868599614877213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39101274974491466153169617 29325956230868599614877213)
            ·
              refine ⟨10997233586575724855578955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29325956230868599614877213 10997233586575724855578955)
              ·
                refine ⟨16495850379863587283368433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10997233586575724855578955 16495850379863587283368433)
                ·
                  refine ⟨12371887784897690462526325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16495850379863587283368433 12371887784897690462526325)
                  ·
                    refine ⟨1159864479834158480861843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12371887784897690462526325 1159864479834158480861843)
                    ·
                      rfl

theorem cell22_3388242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_3388242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388242 prefixEnd_3388242 := by exact prefixLift 3388242
  have htrace : WordTrace (prefixWord ++ tailWord_3388242) baseStart_3388242 baseEnd_3388242 := by
    simpa [prefixWord, tailWord_3388242, baseEnd_3388242] using wordTrace_append hprefix tailTrace_3388242
  have hstable : (prefixWord ++ tailWord_3388242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388242).length < 2 ^ (prefixWord ++ tailWord_3388242).sum := by decide
  have hdescent : baseEnd_3388242 < baseStart_3388242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388317 : List Nat := [1, 4, 2, 1, 2, 1, 3, 8]
def baseStart_3388317 : Nat := 118140960795 + 3388317 * 2 ^ 59
def prefixEnd_3388317 : Nat := 4983230072969 + 3 ^ 40 * 3388317 * 2
def baseEnd_3388317 : Nat := 128876683762987031692957

theorem tailTrace_3388317 : CollatzResearch.WordTrace tailWord_3388317 prefixEnd_3388317 128876683762987031692957 := by
  unfold tailWord_3388317
  simp only [CollatzResearch.WordTrace]
  refine ⟨123582073665713662317763205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82388049110475774878508803 123582073665713662317763205)
  ·
    refine ⟨23171638812321311684580601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123582073665713662317763205 23171638812321311684580601)
    ·
      refine ⟨17378729109240983763435451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23171638812321311684580601 17378729109240983763435451)
      ·
        refine ⟨26068093663861475645153177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17378729109240983763435451 26068093663861475645153177)
        ·
          refine ⟨19551070247896106733864883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26068093663861475645153177 19551070247896106733864883)
          ·
            refine ⟨29326605371844160100797325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19551070247896106733864883 29326605371844160100797325)
            ·
              refine ⟨10997477014441560037798997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29326605371844160100797325 10997477014441560037798997)
              ·
                refine ⟨128876683762987031692957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10997477014441560037798997 128876683762987031692957)
                ·
                  rfl

theorem cell22_3388317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 8].length) (baseStart_3388317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388317 prefixEnd_3388317 := by exact prefixLift 3388317
  have htrace : WordTrace (prefixWord ++ tailWord_3388317) baseStart_3388317 baseEnd_3388317 := by
    simpa [prefixWord, tailWord_3388317, baseEnd_3388317] using wordTrace_append hprefix tailTrace_3388317
  have hstable : (prefixWord ++ tailWord_3388317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388317).length < 2 ^ (prefixWord ++ tailWord_3388317).sum := by decide
  have hdescent : baseEnd_3388317 < baseStart_3388317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388340 : List Nat := [2, 5, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3388340 : Nat := 118140960795 + 3388340 * 2 ^ 59
def prefixEnd_3388340 : Nat := 4983230072969 + 3 ^ 40 * 3388340 * 2
def baseEnd_3388340 : Nat := 386632675745639630637181

theorem tailTrace_3388340 : CollatzResearch.WordTrace tailWord_3388340 prefixEnd_3388340 386632675745639630637181 := by
  unfold tailWord_3388340
  simp only [CollatzResearch.WordTrace]
  refine ⟨61791456272315168622925237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82388608363086891497233649 61791456272315168622925237)
  ·
    refine ⟨5792949025529547058399241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61791456272315168622925237 5792949025529547058399241)
    ·
      refine ⟨4344711769147160293799431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5792949025529547058399241 4344711769147160293799431)
      ·
        refine ⟨6517067653720740440699147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344711769147160293799431 6517067653720740440699147)
        ·
          refine ⟨9775601480581110661048721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517067653720740440699147 9775601480581110661048721)
          ·
            refine ⟨7331701110435832995786541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9775601480581110661048721 7331701110435832995786541)
            ·
              refine ⟨2749387916413437373419953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7331701110435832995786541 2749387916413437373419953)
              ·
                refine ⟨2062040937310078030064965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749387916413437373419953 2062040937310078030064965)
                ·
                  refine ⟨386632675745639630637181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062040937310078030064965 386632675745639630637181)
                  ·
                    rfl

theorem cell22_3388340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3388340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388340 prefixEnd_3388340 := by exact prefixLift 3388340
  have htrace : WordTrace (prefixWord ++ tailWord_3388340) baseStart_3388340 baseEnd_3388340 := by
    simpa [prefixWord, tailWord_3388340, baseEnd_3388340] using wordTrace_append hprefix tailTrace_3388340
  have hstable : (prefixWord ++ tailWord_3388340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388340).length < 2 ^ (prefixWord ++ tailWord_3388340).sum := by decide
  have hdescent : baseEnd_3388340 < baseStart_3388340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388424 : List Nat := [2, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_3388424 : Nat := 118140960795 + 3388424 * 2 ^ 59
def prefixEnd_3388424 : Nat := 4983230072969 + 3 ^ 40 * 3388424 * 2
def baseEnd_3388424 : Nat := 386642260717856890937095

theorem tailTrace_3388424 : CollatzResearch.WordTrace tailWord_3388424 prefixEnd_3388424 386642260717856890937095 := by
  unfold tailWord_3388424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61792988138163009795954163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82390650850884013061272217 61792988138163009795954163)
  ·
    refine ⟨92689482207244514693931245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61792988138163009795954163 92689482207244514693931245)
    ·
      refine ⟨34758555827716693010224217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92689482207244514693931245 34758555827716693010224217)
      ·
        refine ⟨26068916870787519757668163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34758555827716693010224217 26068916870787519757668163)
        ·
          refine ⟨39103375306181279636502245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26068916870787519757668163 39103375306181279636502245)
          ·
            refine ⟨7331882869908989931844171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39103375306181279636502245 7331882869908989931844171)
            ·
              refine ⟨10997824304863484897766257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331882869908989931844171 10997824304863484897766257)
              ·
                refine ⟨8248368228647613673324693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10997824304863484897766257 8248368228647613673324693)
                ·
                  refine ⟨386642260717856890937095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8248368228647613673324693 386642260717856890937095)
                  ·
                    rfl

theorem cell22_3388424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_3388424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388424 prefixEnd_3388424 := by exact prefixLift 3388424
  have htrace : WordTrace (prefixWord ++ tailWord_3388424) baseStart_3388424 baseEnd_3388424 := by
    simpa [prefixWord, tailWord_3388424, baseEnd_3388424] using wordTrace_append hprefix tailTrace_3388424
  have hstable : (prefixWord ++ tailWord_3388424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388424).length < 2 ^ (prefixWord ++ tailWord_3388424).sum := by decide
  have hdescent : baseEnd_3388424 < baseStart_3388424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388434 : List Nat := [3, 2, 5, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3388434 : Nat := 118140960795 + 3388434 * 2 ^ 59
def prefixEnd_3388434 : Nat := 4983230072969 + 3 ^ 40 * 3388434 * 2
def baseEnd_3388434 : Nat := 1159930205357933980061255

theorem tailTrace_3388434 : CollatzResearch.WordTrace tailWord_3388434 prefixEnd_3388434 1159930205357933980061255 := by
  unfold tailWord_3388434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30896585251572447824943089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82390894004193194199848237 30896585251572447824943089)
  ·
    refine ⟨23172438938679335868707317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30896585251572447824943089 23172438938679335868707317)
    ·
      refine ⟨2172416150501187737691311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23172438938679335868707317 2172416150501187737691311)
      ·
        refine ⟨3258624225751781606536967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2172416150501187737691311 3258624225751781606536967)
        ·
          refine ⟨4887936338627672409805451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258624225751781606536967 4887936338627672409805451)
          ·
            refine ⟨7331904507941508614708177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887936338627672409805451 7331904507941508614708177)
            ·
              refine ⟨5498928380956131461031133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7331904507941508614708177 5498928380956131461031133)
              ·
                refine ⟨2062098142858549297886675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5498928380956131461031133 2062098142858549297886675)
                ·
                  refine ⟨3093147214287823946830013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062098142858549297886675 3093147214287823946830013)
                  ·
                    refine ⟨1159930205357933980061255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093147214287823946830013 1159930205357933980061255)
                    ·
                      rfl

theorem cell22_3388434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3388434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388434 prefixEnd_3388434 := by exact prefixLift 3388434
  have htrace : WordTrace (prefixWord ++ tailWord_3388434) baseStart_3388434 baseEnd_3388434 := by
    simpa [prefixWord, tailWord_3388434, baseEnd_3388434] using wordTrace_append hprefix tailTrace_3388434
  have hstable : (prefixWord ++ tailWord_3388434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388434).length < 2 ^ (prefixWord ++ tailWord_3388434).sum := by decide
  have hdescent : baseEnd_3388434 < baseStart_3388434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388612 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 1, 4]
def baseStart_3388612 : Nat := 118140960795 + 3388612 * 2 ^ 59
def prefixEnd_3388612 : Nat := 4983230072969 + 3 ^ 40 * 3388612 * 2
def baseEnd_3388612 : Nat := 1159991138395600849110709

theorem tailTrace_3388612 : CollatzResearch.WordTrace tailWord_3388612 prefixEnd_3388612 1159991138395600849110709 := by
  unfold tailWord_3388612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61796416599822463849876045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82395222133096618466501393 61796416599822463849876045)
  ·
    refine ⟨23173656224933423943703517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61796416599822463849876045 23173656224933423943703517)
    ·
      refine ⟨8690121084350033978888819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23173656224933423943703517 8690121084350033978888819)
      ·
        refine ⟨13035181626525050968333229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690121084350033978888819 13035181626525050968333229)
        ·
          refine ⟨4888193109946894113124961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13035181626525050968333229 4888193109946894113124961)
          ·
            refine ⟨3666144832460170584843721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4888193109946894113124961 3666144832460170584843721)
            ·
              refine ⟨2749608624345127938632791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3666144832460170584843721 2749608624345127938632791)
              ·
                refine ⟨4124412936517691907949187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749608624345127938632791 4124412936517691907949187)
                ·
                  refine ⟨6186619404776537861923781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124412936517691907949187 6186619404776537861923781)
                  ·
                    refine ⟨1159991138395600849110709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6186619404776537861923781 1159991138395600849110709)
                    ·
                      rfl

theorem cell22_3388612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_3388612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388612 prefixEnd_3388612 := by exact prefixLift 3388612
  have htrace : WordTrace (prefixWord ++ tailWord_3388612) baseStart_3388612 baseEnd_3388612 := by
    simpa [prefixWord, tailWord_3388612, baseEnd_3388612] using wordTrace_append hprefix tailTrace_3388612
  have hstable : (prefixWord ++ tailWord_3388612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388612).length < 2 ^ (prefixWord ++ tailWord_3388612).sum := by decide
  have hdescent : baseEnd_3388612 < baseStart_3388612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388649 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 11]
def baseStart_3388649 : Nat := 118140960795 + 3388649 * 2 ^ 59
def prefixEnd_3388649 : Nat := 4983230072969 + 3 ^ 40 * 3388649 * 2
def baseEnd_3388649 : Nat := 386667934750581695311865

theorem tailTrace_3388649 : CollatzResearch.WordTrace tailWord_3388649 prefixEnd_3388649 386667934750581695311865 := by
  unfold tailWord_3388649
  simp only [CollatzResearch.WordTrace]
  refine ⟨123594182700510883018849001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82396121800340588679232667 123594182700510883018849001)
  ·
    refine ⟨92695637025383162264136751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123594182700510883018849001 92695637025383162264136751)
    ·
      refine ⟨139043455538074743396205127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92695637025383162264136751 139043455538074743396205127)
      ·
        refine ⟨208565183307112115094307691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139043455538074743396205127 208565183307112115094307691)
        ·
          refine ⟨312847774960668172641461537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208565183307112115094307691 312847774960668172641461537)
          ·
            refine ⟨234635831220501129481096153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312847774960668172641461537 234635831220501129481096153)
            ·
              refine ⟨175976873415375847110822115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234635831220501129481096153 175976873415375847110822115)
              ·
                refine ⟨263965310123063770666233173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175976873415375847110822115 263965310123063770666233173)
                ·
                  refine ⟨386667934750581695311865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 263965310123063770666233173 386667934750581695311865)
                  ·
                    rfl

theorem cell22_3388649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_3388649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388649 prefixEnd_3388649 := by exact prefixLift 3388649
  have htrace : WordTrace (prefixWord ++ tailWord_3388649) baseStart_3388649 baseEnd_3388649 := by
    simpa [prefixWord, tailWord_3388649, baseEnd_3388649] using wordTrace_append hprefix tailTrace_3388649
  have hstable : (prefixWord ++ tailWord_3388649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388649).length < 2 ^ (prefixWord ++ tailWord_3388649).sum := by decide
  have hdescent : baseEnd_3388649 < baseStart_3388649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388655 : List Nat := [1, 1, 2, 1, 8, 1, 2, 6]
def baseStart_3388655 : Nat := 118140960795 + 3388655 * 2 ^ 59
def prefixEnd_3388655 : Nat := 4983230072969 + 3 ^ 40 * 3388655 * 2
def baseEnd_3388655 : Nat := 128889539797151452253953

theorem tailTrace_3388655 : CollatzResearch.WordTrace tailWord_3388655 prefixEnd_3388655 128889539797151452253953 := by
  unfold tailWord_3388655
  simp only [CollatzResearch.WordTrace]
  refine ⟨123594401538489146043567419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82396267692326097362378279 123594401538489146043567419)
  ·
    refine ⟨185391602307733719065351129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123594401538489146043567419 185391602307733719065351129)
    ·
      refine ⟨139043701730800289299013347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185391602307733719065351129 139043701730800289299013347)
      ·
        refine ⟨208565552596200433948520021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139043701730800289299013347 208565552596200433948520021)
        ·
          refine ⟨2444127569486723835334219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 208565552596200433948520021 2444127569486723835334219)
          ·
            refine ⟨3666191354230085753001329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444127569486723835334219 3666191354230085753001329)
            ·
              refine ⟨2749643515672564314750997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3666191354230085753001329 2749643515672564314750997)
              ·
                refine ⟨128889539797151452253953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2749643515672564314750997 128889539797151452253953)
                ·
                  rfl

theorem cell22_3388655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 6].length) (baseStart_3388655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388655 prefixEnd_3388655 := by exact prefixLift 3388655
  have htrace : WordTrace (prefixWord ++ tailWord_3388655) baseStart_3388655 baseEnd_3388655 := by
    simpa [prefixWord, tailWord_3388655, baseEnd_3388655] using wordTrace_append hprefix tailTrace_3388655
  have hstable : (prefixWord ++ tailWord_3388655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388655).length < 2 ^ (prefixWord ++ tailWord_3388655).sum := by decide
  have hdescent : baseEnd_3388655 < baseStart_3388655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388728 : List Nat := [2, 1, 2, 1, 3, 1, 1, 7, 4]
def baseStart_3388728 : Nat := 118140960795 + 3388728 * 2 ^ 59
def prefixEnd_3388728 : Nat := 4983230072969 + 3 ^ 40 * 3388728 * 2
def baseEnd_3388728 : Nat := 386676949188738404403451

theorem tailTrace_3388728 : CollatzResearch.WordTrace tailWord_3388728 prefixEnd_3388728 386676949188738404403451 := by
  unfold tailWord_3388728
  simp only [CollatzResearch.WordTrace]
  refine ⟨61798532033612339755487419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82398042711483119673983225 61798532033612339755487419)
  ·
    refine ⟨92697798050418509633231129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61798532033612339755487419 92697798050418509633231129)
    ·
      refine ⟨69523348537813882224923347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92697798050418509633231129 69523348537813882224923347)
      ·
        refine ⟨104285022806720823337385021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69523348537813882224923347 104285022806720823337385021)
        ·
          refine ⟨39106883552520308751519383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104285022806720823337385021 39106883552520308751519383)
          ·
            refine ⟨58660325328780463127279075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39106883552520308751519383 58660325328780463127279075)
            ·
              refine ⟨87990487993170694690918613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58660325328780463127279075 87990487993170694690918613)
              ·
                refine ⟨2062277062339938156818405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87990487993170694690918613 2062277062339938156818405)
                ·
                  refine ⟨386676949188738404403451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062277062339938156818405 386676949188738404403451)
                  ·
                    rfl

theorem cell22_3388728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 7, 4].length) (baseStart_3388728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388728 prefixEnd_3388728 := by exact prefixLift 3388728
  have htrace : WordTrace (prefixWord ++ tailWord_3388728) baseStart_3388728 baseEnd_3388728 := by
    simpa [prefixWord, tailWord_3388728, baseEnd_3388728] using wordTrace_append hprefix tailTrace_3388728
  have hstable : (prefixWord ++ tailWord_3388728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388728).length < 2 ^ (prefixWord ++ tailWord_3388728).sum := by decide
  have hdescent : baseEnd_3388728 < baseStart_3388728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388730 : List Nat := [3, 1, 1, 1, 4, 1, 5, 1, 1, 4]
def baseStart_3388730 : Nat := 118140960795 + 3388730 * 2 ^ 59
def prefixEnd_3388730 : Nat := 4983230072969 + 3 ^ 40 * 3388730 * 2
def baseEnd_3388730 : Nat := 1160031532207087874660347

theorem tailTrace_3388730 : CollatzResearch.WordTrace tailWord_3388730 prefixEnd_3388730 1160031532207087874660347 := by
  unfold tailWord_3388730
  simp only [CollatzResearch.WordTrace]
  refine ⟨30899284253304358463136911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82398091342144955901698429 30899284253304358463136911)
  ·
    refine ⟨46348926379956537694705367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30899284253304358463136911 46348926379956537694705367)
    ·
      refine ⟨69523389569934806542058051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46348926379956537694705367 69523389569934806542058051)
      ·
        refine ⟨104285084354902209813087077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69523389569934806542058051 104285084354902209813087077)
        ·
          refine ⟨19553453316544164339953827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104285084354902209813087077 19553453316544164339953827)
          ·
            refine ⟨29330179974816246509930741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19553453316544164339953827 29330179974816246509930741)
            ·
              refine ⟨2749704372639023110306007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29330179974816246509930741 2749704372639023110306007)
              ·
                refine ⟨4124556558958534665459011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749704372639023110306007 4124556558958534665459011)
                ·
                  refine ⟨6186834838437801998188517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124556558958534665459011 6186834838437801998188517)
                  ·
                    refine ⟨1160031532207087874660347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6186834838437801998188517 1160031532207087874660347)
                    ·
                      rfl

theorem cell22_3388730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 5, 1, 1, 4].length) (baseStart_3388730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388730 prefixEnd_3388730 := by exact prefixLift 3388730
  have htrace : WordTrace (prefixWord ++ tailWord_3388730) baseStart_3388730 baseEnd_3388730 := by
    simpa [prefixWord, tailWord_3388730, baseEnd_3388730] using wordTrace_append hprefix tailTrace_3388730
  have hstable : (prefixWord ++ tailWord_3388730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388730).length < 2 ^ (prefixWord ++ tailWord_3388730).sum := by decide
  have hdescent : baseEnd_3388730 < baseStart_3388730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388745 : List Nat := [1, 2, 1, 1, 2, 3, 6, 2, 4]
def baseStart_3388745 : Nat := 118140960795 + 3388745 * 2 ^ 59
def prefixEnd_3388745 : Nat := 4983230072969 + 3 ^ 40 * 3388745 * 2
def baseEnd_3388745 : Nat := 386678889004544278511767

theorem tailTrace_3388745 : CollatzResearch.WordTrace tailWord_3388745 prefixEnd_3388745 386678889004544278511767 := by
  unfold tailWord_3388745
  simp only [CollatzResearch.WordTrace]
  refine ⟨123597684108163091414343689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82398456072108727609562459 123597684108163091414343689)
  ·
    refine ⟨92698263081122318560757767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123597684108163091414343689 92698263081122318560757767)
    ·
      refine ⟨139047394621683477841136651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92698263081122318560757767 139047394621683477841136651)
      ·
        refine ⟨208571091932525216761704977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139047394621683477841136651 208571091932525216761704977)
        ·
          refine ⟨156428318949393912571278733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208571091932525216761704977 156428318949393912571278733)
          ·
            refine ⟨58660619606022717214229525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156428318949393912571278733 58660619606022717214229525)
            ·
              refine ⟨2749716544032314869417009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58660619606022717214229525 2749716544032314869417009)
              ·
                refine ⟨2062287408024236152062757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749716544032314869417009 2062287408024236152062757)
                ·
                  refine ⟨386678889004544278511767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062287408024236152062757 386678889004544278511767)
                  ·
                    rfl

theorem cell22_3388745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_3388745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388745 prefixEnd_3388745 := by exact prefixLift 3388745
  have htrace : WordTrace (prefixWord ++ tailWord_3388745) baseStart_3388745 baseEnd_3388745 := by
    simpa [prefixWord, tailWord_3388745, baseEnd_3388745] using wordTrace_append hprefix tailTrace_3388745
  have hstable : (prefixWord ++ tailWord_3388745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388745).length < 2 ^ (prefixWord ++ tailWord_3388745).sum := by decide
  have hdescent : baseEnd_3388745 < baseStart_3388745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388773 : List Nat := [1, 3, 1, 3, 1, 2, 5, 6]
def baseStart_3388773 : Nat := 118140960795 + 3388773 * 2 ^ 59
def prefixEnd_3388773 : Nat := 4983230072969 + 3 ^ 40 * 3388773 * 2
def baseEnd_3388773 : Nat := 128894027998427788426135

theorem tailTrace_3388773 : CollatzResearch.WordTrace tailWord_3388773 prefixEnd_3388773 128894027998427788426135 := by
  unfold tailWord_3388773
  simp only [CollatzResearch.WordTrace]
  refine ⟨123598705352061652196362973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82399136901374434797575315 123598705352061652196362973)
  ·
    refine ⟨46349514507023119573636115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123598705352061652196362973 46349514507023119573636115)
    ·
      refine ⟨69524271760534679360454173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46349514507023119573636115 69524271760534679360454173)
      ·
        refine ⟨26071601910200504760170315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69524271760534679360454173 26071601910200504760170315)
        ·
          refine ⟨39107402865300757140255473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26071601910200504760170315 39107402865300757140255473)
          ·
            refine ⟨29330552148975567855191605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39107402865300757140255473 29330552148975567855191605)
            ·
              refine ⟨2749739263966459486424213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29330552148975567855191605 2749739263966459486424213)
              ·
                refine ⟨128894027998427788426135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2749739263966459486424213 128894027998427788426135)
                ·
                  rfl

theorem cell22_3388773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5, 6].length) (baseStart_3388773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388773 prefixEnd_3388773 := by exact prefixLift 3388773
  have htrace : WordTrace (prefixWord ++ tailWord_3388773) baseStart_3388773 baseEnd_3388773 := by
    simpa [prefixWord, tailWord_3388773, baseEnd_3388773] using wordTrace_append hprefix tailTrace_3388773
  have hstable : (prefixWord ++ tailWord_3388773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388773).length < 2 ^ (prefixWord ++ tailWord_3388773).sum := by decide
  have hdescent : baseEnd_3388773 < baseStart_3388773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388910 : List Nat := [4, 1, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3388910 : Nat := 118140960795 + 3388910 * 2 ^ 59
def prefixEnd_3388910 : Nat := 4983230072969 + 3 ^ 40 * 3388910 * 2
def baseEnd_3388910 : Nat := 1160093149885627405159795

theorem tailTrace_3388910 : CollatzResearch.WordTrace tailWord_3388910 prefixEnd_3388910 1160093149885627405159795 := by
  unfold tailWord_3388910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450462769070665574262523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82402468101710216396066789 15450462769070665574262523)
  ·
    refine ⟨23175694153605998361393785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450462769070665574262523 23175694153605998361393785)
    ·
      refine ⟨17381770615204498771045339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23175694153605998361393785 17381770615204498771045339)
      ·
        refine ⟨26072655922806748156568009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17381770615204498771045339 26072655922806748156568009)
        ·
          refine ⟨19554491942105061117426007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26072655922806748156568009 19554491942105061117426007)
          ·
            refine ⟨29331737913157591676139011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19554491942105061117426007 29331737913157591676139011)
            ·
              refine ⟨43997606869736387514208517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29331737913157591676139011 43997606869736387514208517)
              ·
                refine ⟨8249551288075572658914097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43997606869736387514208517 8249551288075572658914097)
                ·
                  refine ⟨6187163466056679494185573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249551288075572658914097 6187163466056679494185573)
                  ·
                    refine ⟨1160093149885627405159795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6187163466056679494185573 1160093149885627405159795)
                    ·
                      rfl

theorem cell22_3388910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3388910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388910 prefixEnd_3388910 := by exact prefixLift 3388910
  have htrace : WordTrace (prefixWord ++ tailWord_3388910) baseStart_3388910 baseEnd_3388910 := by
    simpa [prefixWord, tailWord_3388910, baseEnd_3388910] using wordTrace_append hprefix tailTrace_3388910
  have hstable : (prefixWord ++ tailWord_3388910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388910).length < 2 ^ (prefixWord ++ tailWord_3388910).sum := by decide
  have hdescent : baseEnd_3388910 < baseStart_3388910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388912 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 2, 3]
def baseStart_3388912 : Nat := 118140960795 + 3388912 * 2 ^ 59
def prefixEnd_3388912 : Nat := 4983230072969 + 3 ^ 40 * 3388912 * 2
def baseEnd_3388912 : Nat := 1160093834526500066609789

theorem tailTrace_3388912 : CollatzResearch.WordTrace tailWord_3388912 prefixEnd_3388912 1160093834526500066609789 := by
  unfold tailWord_3388912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61801887549279039467836495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82402516732372052623781993 61801887549279039467836495)
  ·
    refine ⟨92702831323918559201754743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61801887549279039467836495 92702831323918559201754743)
    ·
      refine ⟨139054246985877838802632115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92702831323918559201754743 139054246985877838802632115)
      ·
        refine ⟨208581370478816758203948173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139054246985877838802632115 208581370478816758203948173)
        ·
          refine ⟨78218013929556284326480565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208581370478816758203948173 78218013929556284326480565)
          ·
            refine ⟨7332938805895901655607553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78218013929556284326480565 7332938805895901655607553)
            ·
              refine ⟨5499704104421926241705665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7332938805895901655607553 5499704104421926241705665)
              ·
                refine ⟨4124778078316444681279249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5499704104421926241705665 4124778078316444681279249)
                ·
                  refine ⟨3093583558737333510959437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4124778078316444681279249 3093583558737333510959437)
                  ·
                    refine ⟨1160093834526500066609789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093583558737333510959437 1160093834526500066609789)
                    ·
                      rfl

theorem cell22_3388912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_3388912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388912 prefixEnd_3388912 := by exact prefixLift 3388912
  have htrace : WordTrace (prefixWord ++ tailWord_3388912) baseStart_3388912 baseEnd_3388912 := by
    simpa [prefixWord, tailWord_3388912, baseEnd_3388912] using wordTrace_append hprefix tailTrace_3388912
  have hstable : (prefixWord ++ tailWord_3388912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388912).length < 2 ^ (prefixWord ++ tailWord_3388912).sum := by decide
  have hdescent : baseEnd_3388912 < baseStart_3388912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388914 : List Nat := [3, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_3388914 : Nat := 118140960795 + 3388914 * 2 ^ 59
def prefixEnd_3388914 : Nat := 4983230072969 + 3 ^ 40 * 3388914 * 2
def baseEnd_3388914 : Nat := 386698173055790909353261

theorem tailTrace_3388914 : CollatzResearch.WordTrace tailWord_3388914 prefixEnd_3388914 386698173055790909353261 := by
  unfold tailWord_3388914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30900962011137708319311449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82402565363033888851497197 30900962011137708319311449)
  ·
    refine ⟨23175721508353281239483587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30900962011137708319311449 23175721508353281239483587)
    ·
      refine ⟨34763582262529921859225381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175721508353281239483587 34763582262529921859225381)
      ·
        refine ⟨6518171674224360348604759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34763582262529921859225381 6518171674224360348604759)
        ·
          refine ⟨9777257511336540522907139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518171674224360348604759 9777257511336540522907139)
          ·
            refine ⟨14665886267004810784360709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777257511336540522907139 14665886267004810784360709)
            ·
              refine ⟨2749853675063402022067633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14665886267004810784360709 2749853675063402022067633)
              ·
                refine ⟨2062390256297551516550725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749853675063402022067633 2062390256297551516550725)
                ·
                  refine ⟨386698173055790909353261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2062390256297551516550725 386698173055790909353261)
                  ·
                    rfl

theorem cell22_3388914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_3388914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388914 prefixEnd_3388914 := by exact prefixLift 3388914
  have htrace : WordTrace (prefixWord ++ tailWord_3388914) baseStart_3388914 baseEnd_3388914 := by
    simpa [prefixWord, tailWord_3388914, baseEnd_3388914] using wordTrace_append hprefix tailTrace_3388914
  have hstable : (prefixWord ++ tailWord_3388914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388914).length < 2 ^ (prefixWord ++ tailWord_3388914).sum := by decide
  have hdescent : baseEnd_3388914 < baseStart_3388914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388925 : List Nat := [1, 4, 1, 1, 1, 6, 1, 7]
def baseStart_3388925 : Nat := 118140960795 + 3388925 * 2 ^ 59
def prefixEnd_3388925 : Nat := 4983230072969 + 3 ^ 40 * 3388925 * 2
def baseEnd_3388925 : Nat := 128899809410241374003861

theorem tailTrace_3388925 : CollatzResearch.WordTrace tailWord_3388925 prefixEnd_3388925 128899809410241374003861 := by
  unfold tailWord_3388925
  simp only [CollatzResearch.WordTrace]
  refine ⟨123604249247510982155896229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82402832831673988103930819 123604249247510982155896229)
  ·
    refine ⟨23175796733908309154230543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123604249247510982155896229 23175796733908309154230543)
    ·
      refine ⟨34763695100862463731345815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175796733908309154230543 34763695100862463731345815)
      ·
        refine ⟨52145542651293695597018723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34763695100862463731345815 52145542651293695597018723)
        ·
          refine ⟨78218313976940543395528085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52145542651293695597018723 78218313976940543395528085)
          ·
            refine ⟨3666483467669087971665379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78218313976940543395528085 3666483467669087971665379)
            ·
              refine ⟨5499725201503631957498069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666483467669087971665379 5499725201503631957498069)
              ·
                refine ⟨128899809410241374003861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5499725201503631957498069 128899809410241374003861)
                ·
                  rfl

theorem cell22_3388925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 7].length) (baseStart_3388925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388925 prefixEnd_3388925 := by exact prefixLift 3388925
  have htrace : WordTrace (prefixWord ++ tailWord_3388925) baseStart_3388925 baseEnd_3388925 := by
    simpa [prefixWord, tailWord_3388925, baseEnd_3388925] using wordTrace_append hprefix tailTrace_3388925
  have hstable : (prefixWord ++ tailWord_3388925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388925).length < 2 ^ (prefixWord ++ tailWord_3388925).sum := by decide
  have hdescent : baseEnd_3388925 < baseStart_3388925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388942 : List Nat := [4, 1, 1, 2, 4, 1, 3, 6]
def baseStart_3388942 : Nat := 118140960795 + 3388942 * 2 ^ 59
def prefixEnd_3388942 : Nat := 4983230072969 + 3 ^ 40 * 3388942 * 2
def baseEnd_3388942 : Nat := 128900456015509998706633

theorem tailTrace_3388942 : CollatzResearch.WordTrace tailWord_3388942 prefixEnd_3388942 128900456015509998706633 := by
  unfold tailWord_3388942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450608661056174257408135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82403246192299596039510053 15450608661056174257408135)
  ·
    refine ⟨23175912991584261386112203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450608661056174257408135 23175912991584261386112203)
    ·
      refine ⟨34763869487376392079168305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23175912991584261386112203 34763869487376392079168305)
      ·
        refine ⟨26072902115532294059376229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34763869487376392079168305 26072902115532294059376229)
        ·
          refine ⟨4888669146662305136133043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26072902115532294059376229 4888669146662305136133043)
          ·
            refine ⟨7333003719993457704199565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888669146662305136133043 7333003719993457704199565)
            ·
              refine ⟨2749876394997546639074837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7333003719993457704199565 2749876394997546639074837)
              ·
                refine ⟨128900456015509998706633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2749876394997546639074837 128900456015509998706633)
                ·
                  rfl

theorem cell22_3388942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_3388942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388942 prefixEnd_3388942 := by exact prefixLift 3388942
  have htrace : WordTrace (prefixWord ++ tailWord_3388942) baseStart_3388942 baseEnd_3388942 := by
    simpa [prefixWord, tailWord_3388942, baseEnd_3388942] using wordTrace_append hprefix tailTrace_3388942
  have hstable : (prefixWord ++ tailWord_3388942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388942).length < 2 ^ (prefixWord ++ tailWord_3388942).sum := by decide
  have hdescent : baseEnd_3388942 < baseStart_3388942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388970 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_3388970 : Nat := 118140960795 + 3388970 * 2 ^ 59
def prefixEnd_3388970 : Nat := 4983230072969 + 3 ^ 40 * 3388970 * 2
def baseEnd_3388970 : Nat := 386704563037269082886537

theorem tailTrace_3388970 : CollatzResearch.WordTrace tailWord_3388970 prefixEnd_3388970 386704563037269082886537 := by
  unfold tailWord_3388970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30901472633086988710321091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82403927021565303227522909 30901472633086988710321091)
  ·
    refine ⟨46352208949630483065481637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30901472633086988710321091 46352208949630483065481637)
    ·
      refine ⟨8691039178055715574777807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46352208949630483065481637 8691039178055715574777807)
      ·
        refine ⟨13036558767083573362166711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691039178055715574777807 13036558767083573362166711)
        ·
          refine ⟨19554838150625360043250067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036558767083573362166711 19554838150625360043250067)
          ·
            refine ⟨29332257225938040064875101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19554838150625360043250067 29332257225938040064875101)
            ·
              refine ⟨10999596459726765024328163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29332257225938040064875101 10999596459726765024328163)
              ·
                refine ⟨16499394689590147536492245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10999596459726765024328163 16499394689590147536492245)
                ·
                  refine ⟨386704563037269082886537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16499394689590147536492245 386704563037269082886537)
                  ·
                    rfl

theorem cell22_3388970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_3388970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388970 prefixEnd_3388970 := by exact prefixLift 3388970
  have htrace : WordTrace (prefixWord ++ tailWord_3388970) baseStart_3388970 baseEnd_3388970 := by
    simpa [prefixWord, tailWord_3388970, baseEnd_3388970] using wordTrace_append hprefix tailTrace_3388970
  have hstable : (prefixWord ++ tailWord_3388970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388970).length < 2 ^ (prefixWord ++ tailWord_3388970).sum := by decide
  have hdescent : baseEnd_3388970 < baseStart_3388970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388974 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3388974 : Nat := 118140960795 + 3388974 * 2 ^ 59
def prefixEnd_3388974 : Nat := 4983230072969 + 3 ^ 40 * 3388974 * 2
def baseEnd_3388974 : Nat := 1160115058393552571559599

theorem tailTrace_3388974 : CollatzResearch.WordTrace tailWord_3388974 prefixEnd_3388974 1160115058393552571559599 := by
  unfold tailWord_3388974
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450754553041682940553747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82404024282888975682953317 15450754553041682940553747)
  ·
    refine ⟨23176131829562524410830621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450754553041682940553747 23176131829562524410830621)
    ·
      refine ⟨8691049436085946654061483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23176131829562524410830621 8691049436085946654061483)
      ·
        refine ⟨13036574154128919981092225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691049436085946654061483 13036574154128919981092225)
        ·
          refine ⟨9777430615596689985819169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13036574154128919981092225 9777430615596689985819169)
          ·
            refine ⟨7333072961697517489364377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9777430615596689985819169 7333072961697517489364377)
            ·
              refine ⟨5499804721273138117023283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333072961697517489364377 5499804721273138117023283)
              ·
                refine ⟨8249707081909707175534925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499804721273138117023283 8249707081909707175534925)
                ·
                  refine ⟨3093640155716140190825597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8249707081909707175534925 3093640155716140190825597)
                  ·
                    refine ⟨1160115058393552571559599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3093640155716140190825597 1160115058393552571559599)
                    ·
                      rfl

theorem cell22_3388974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3388974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388974 prefixEnd_3388974 := by exact prefixLift 3388974
  have htrace : WordTrace (prefixWord ++ tailWord_3388974) baseStart_3388974 baseEnd_3388974 := by
    simpa [prefixWord, tailWord_3388974, baseEnd_3388974] using wordTrace_append hprefix tailTrace_3388974
  have hstable : (prefixWord ++ tailWord_3388974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388974).length < 2 ^ (prefixWord ++ tailWord_3388974).sum := by decide
  have hdescent : baseEnd_3388974 < baseStart_3388974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388985 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_3388985 : Nat := 118140960795 + 3388985 * 2 ^ 59
def prefixEnd_3388985 : Nat := 4983230072969 + 3 ^ 40 * 3388985 * 2
def baseEnd_3388985 : Nat := 1160118823918352209534565

theorem tailTrace_3388985 : CollatzResearch.WordTrace tailWord_3388985 prefixEnd_3388985 1160118823918352209534565 := by
  unfold tailWord_3388985
  simp only [CollatzResearch.WordTrace]
  refine ⟨123606437627293612403080409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82404291751529074935386939 123606437627293612403080409)
  ·
    refine ⟨92704828220470209302310307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123606437627293612403080409 92704828220470209302310307)
    ·
      refine ⟨139057242330705313953465461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92704828220470209302310307 139057242330705313953465461)
      ·
        refine ⟨13036616468503623183137387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139057242330705313953465461 13036616468503623183137387)
        ·
          refine ⟨19554924702755434774706081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036616468503623183137387 19554924702755434774706081)
          ·
            refine ⟨14666193527066576081029561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19554924702755434774706081 14666193527066576081029561)
            ·
              refine ⟨10999645145299932060772171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14666193527066576081029561 10999645145299932060772171)
              ·
                refine ⟨16499467717949898091158257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10999645145299932060772171 16499467717949898091158257)
                ·
                  refine ⟨12374600788462423568368693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16499467717949898091158257 12374600788462423568368693)
                  ·
                    refine ⟨1160118823918352209534565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12374600788462423568368693 1160118823918352209534565)
                    ·
                      rfl

theorem cell22_3388985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_3388985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3388985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3388985 prefixEnd_3388985 := by exact prefixLift 3388985
  have htrace : WordTrace (prefixWord ++ tailWord_3388985) baseStart_3388985 baseEnd_3388985 := by
    simpa [prefixWord, tailWord_3388985, baseEnd_3388985] using wordTrace_append hprefix tailTrace_3388985
  have hstable : (prefixWord ++ tailWord_3388985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388985).length < 2 ^ (prefixWord ++ tailWord_3388985).sum := by decide
  have hdescent : baseEnd_3388985 < baseStart_3388985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389032 : List Nat := [2, 1, 4, 3, 1, 1, 3, 1, 6]
def baseStart_3389032 : Nat := 118140960795 + 3389032 * 2 ^ 59
def prefixEnd_3389032 : Nat := 4983230072969 + 3 ^ 40 * 3389032 * 2
def baseEnd_3389032 : Nat := 386711637659619917869807

theorem tailTrace_3389032 : CollatzResearch.WordTrace tailWord_3389032 prefixEnd_3389032 386711637659619917869807 := by
  unfold tailWord_3389032
  simp only [CollatzResearch.WordTrace]
  refine ⟨61804075929061669715020675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82405434572082226286694233 61804075929061669715020675)
  ·
    refine ⟨92706113893592504572531013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61804075929061669715020675 92706113893592504572531013)
    ·
      refine ⟨17382396355048594607349565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92706113893592504572531013 17382396355048594607349565)
      ·
        refine ⟨6518398633143222977756087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17382396355048594607349565 6518398633143222977756087)
        ·
          refine ⟨9777597949714834466634131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518398633143222977756087 9777597949714834466634131)
          ·
            refine ⟨14666396924572251699951197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777597949714834466634131 14666396924572251699951197)
            ·
              refine ⟨5499898846714594387481699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14666396924572251699951197 5499898846714594387481699)
              ·
                refine ⟨8249848270071891581222549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499898846714594387481699 8249848270071891581222549)
                ·
                  refine ⟨386711637659619917869807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8249848270071891581222549 386711637659619917869807)
                  ·
                    rfl

theorem cell22_3389032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 6].length) (baseStart_3389032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389032 prefixEnd_3389032 := by exact prefixLift 3389032
  have htrace : WordTrace (prefixWord ++ tailWord_3389032) baseStart_3389032 baseEnd_3389032 := by
    simpa [prefixWord, tailWord_3389032, baseEnd_3389032] using wordTrace_append hprefix tailTrace_3389032
  have hstable : (prefixWord ++ tailWord_3389032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389032).length < 2 ^ (prefixWord ++ tailWord_3389032).sum := by decide
  have hdescent : baseEnd_3389032 < baseStart_3389032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389064 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 1, 5]
def baseStart_3389064 : Nat := 118140960795 + 3389064 * 2 ^ 59
def prefixEnd_3389064 : Nat := 4983230072969 + 3 ^ 40 * 3389064 * 2
def baseEnd_3389064 : Nat := 1160145867232822336809323

theorem tailTrace_3389064 : CollatzResearch.WordTrace tailWord_3389064 prefixEnd_3389064 1160145867232822336809323 := by
  unfold tailWord_3389064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61804659497003704447603123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82406212662671605930137497 61804659497003704447603123)
  ·
    refine ⟨92706989245505556671404685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61804659497003704447603123 92706989245505556671404685)
    ·
      refine ⟨34765120967064583751776757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92706989245505556671404685 34765120967064583751776757)
      ·
        refine ⟨3259230090662304726729071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34765120967064583751776757 3259230090662304726729071)
        ·
          refine ⟨4888845135993457090093607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259230090662304726729071 4888845135993457090093607)
          ·
            refine ⟨7333267703990185635140411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888845135993457090093607 7333267703990185635140411)
            ·
              refine ⟨10999901555985278452710617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333267703990185635140411 10999901555985278452710617)
              ·
                refine ⟨8249926166988958839532963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10999901555985278452710617 8249926166988958839532963)
                ·
                  refine ⟨12374889250483438259299445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8249926166988958839532963 12374889250483438259299445)
                  ·
                    refine ⟨1160145867232822336809323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12374889250483438259299445 1160145867232822336809323)
                    ·
                      rfl

theorem cell22_3389064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_3389064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389064 prefixEnd_3389064 := by exact prefixLift 3389064
  have htrace : WordTrace (prefixWord ++ tailWord_3389064) baseStart_3389064 baseEnd_3389064 := by
    simpa [prefixWord, tailWord_3389064, baseEnd_3389064] using wordTrace_append hprefix tailTrace_3389064
  have hstable : (prefixWord ++ tailWord_3389064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389064).length < 2 ^ (prefixWord ++ tailWord_3389064).sum := by decide
  have hdescent : baseEnd_3389064 < baseStart_3389064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389120 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 1, 7]
def baseStart_3389120 : Nat := 118140960795 + 3389120 * 2 ^ 59
def prefixEnd_3389120 : Nat := 4983230072969 + 3 ^ 40 * 3389120 * 2
def baseEnd_3389120 : Nat := 1160165037177256857409151

theorem tailTrace_3389120 : CollatzResearch.WordTrace tailWord_3389120 prefixEnd_3389120 1160165037177256857409151 := by
  unfold tailWord_3389120
  simp only [CollatzResearch.WordTrace]
  refine ⟨61805680740902265229622407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82407574321203020306163209 61805680740902265229622407)
  ·
    refine ⟨92708521111353397844433611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61805680740902265229622407 92708521111353397844433611)
    ·
      refine ⟨139062781667030096766650417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92708521111353397844433611 139062781667030096766650417)
      ·
        refine ⟨104297086250272572574987813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139062781667030096766650417 104297086250272572574987813)
        ·
          refine ⟨19555703671926107357810215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104297086250272572574987813 19555703671926107357810215)
          ·
            refine ⟨29333555507889161036715323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19555703671926107357810215 29333555507889161036715323)
            ·
              refine ⟨44000333261833741555072985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29333555507889161036715323 44000333261833741555072985)
              ·
                refine ⟨33000249946375306166304739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44000333261833741555072985 33000249946375306166304739)
                ·
                  refine ⟨49500374919562959249457109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33000249946375306166304739 49500374919562959249457109)
                  ·
                    refine ⟨1160165037177256857409151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49500374919562959249457109 1160165037177256857409151)
                    ·
                      rfl

theorem cell22_3389120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 7].length) (baseStart_3389120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3389120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3389120 prefixEnd_3389120 := by exact prefixLift 3389120
  have htrace : WordTrace (prefixWord ++ tailWord_3389120) baseStart_3389120 baseEnd_3389120 := by
    simpa [prefixWord, tailWord_3389120, baseEnd_3389120] using wordTrace_append hprefix tailTrace_3389120
  have hstable : (prefixWord ++ tailWord_3389120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389120).length < 2 ^ (prefixWord ++ tailWord_3389120).sum := by decide
  have hdescent : baseEnd_3389120 < baseStart_3389120 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
