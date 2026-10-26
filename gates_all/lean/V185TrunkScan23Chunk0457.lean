import V185TrunkScan23Chunk0456

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2704109 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2704109 : Nat := 118140960795 + 2704109 * 2 ^ 59
def prefixEnd_2704109 : Nat := 4983230072969 + 3 ^ 40 * 2704109 * 2
def baseEnd_2704109 : Nat := 1388507659148865894801535

theorem tailTrace_2704109 : CollatzResearch.WordTrace tailWord_2704109 prefixEnd_2704109 1388507659148865894801535 := by
  unfold tailWord_2704109
  simp only [CollatzResearch.WordTrace]
  refine ⟨98626957760482392894539381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65751305173654928596359587 98626957760482392894539381)
  ·
    refine ⟨9246277290045224333863067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98626957760482392894539381 9246277290045224333863067)
    ·
      refine ⟨13869415935067836500794601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246277290045224333863067 13869415935067836500794601)
      ·
        refine ⟨10402061951300877375595951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13869415935067836500794601 10402061951300877375595951)
        ·
          refine ⟨15603092926951316063393927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402061951300877375595951 15603092926951316063393927)
          ·
            refine ⟨23404639390426974095090891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15603092926951316063393927 23404639390426974095090891)
            ·
              refine ⟨35106959085640461142636337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23404639390426974095090891 35106959085640461142636337)
              ·
                refine ⟨26330219314230345856977253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35106959085640461142636337 26330219314230345856977253)
                ·
                  refine ⟨4936916121418189848183235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26330219314230345856977253 4936916121418189848183235)
                  ·
                    refine ⟨7405374182127284772274853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936916121418189848183235 7405374182127284772274853)
                    ·
                      refine ⟨1388507659148865894801535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7405374182127284772274853 1388507659148865894801535)
                      ·
                        rfl

theorem cell23_2704109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2704109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704109 prefixEnd_2704109 := by exact prefixLift 2704109
  have htrace : WordTrace (prefixWord ++ tailWord_2704109) baseStart_2704109 baseEnd_2704109 := by
    simpa [prefixWord, tailWord_2704109, baseEnd_2704109] using wordTrace_append hprefix tailTrace_2704109
  have hstable : (prefixWord ++ tailWord_2704109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704109).length < 2 ^ (prefixWord ++ tailWord_2704109).sum := by decide
  have hdescent : baseEnd_2704109 < baseStart_2704109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704122 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_2704122 : Nat := 118140960795 + 2704122 * 2 ^ 59
def prefixEnd_2704122 : Nat := 4983230072969 + 3 ^ 40 * 2704122 * 2
def baseEnd_2704122 : Nat := 1388514334397374343938975

theorem tailTrace_2704122 : CollatzResearch.WordTrace tailWord_2704122 prefixEnd_2704122 1388514334397374343938975 := by
  unfold tailWord_2704122
  simp only [CollatzResearch.WordTrace]
  refine ⟨24656857977358824028690655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65751621272956864076508413 24656857977358824028690655)
  ·
    refine ⟨36985286966038236043035983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24656857977358824028690655 36985286966038236043035983)
    ·
      refine ⟨55477930449057354064553975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36985286966038236043035983 55477930449057354064553975)
      ·
        refine ⟨83216895673586031096830963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55477930449057354064553975 83216895673586031096830963)
        ·
          refine ⟨124825343510379046645246445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83216895673586031096830963 124825343510379046645246445)
          ·
            refine ⟨46809503816392142491967417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124825343510379046645246445 46809503816392142491967417)
            ·
              refine ⟨35107127862294106868975563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46809503816392142491967417 35107127862294106868975563)
              ·
                refine ⟨52660691793441160303463345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35107127862294106868975563 52660691793441160303463345)
                ·
                  refine ⟨39495518845080870227597509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52660691793441160303463345 39495518845080870227597509)
                  ·
                    refine ⟨7405409783452663167674533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39495518845080870227597509 7405409783452663167674533)
                    ·
                      refine ⟨1388514334397374343938975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7405409783452663167674533 1388514334397374343938975)
                      ·
                        rfl

theorem cell23_2704122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_2704122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704122 prefixEnd_2704122 := by exact prefixLift 2704122
  have htrace : WordTrace (prefixWord ++ tailWord_2704122) baseStart_2704122 baseEnd_2704122 := by
    simpa [prefixWord, tailWord_2704122, baseEnd_2704122] using wordTrace_append hprefix tailTrace_2704122
  have hstable : (prefixWord ++ tailWord_2704122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704122).length < 2 ^ (prefixWord ++ tailWord_2704122).sum := by decide
  have hdescent : baseEnd_2704122 < baseStart_2704122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704126 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2704126 : Nat := 118140960795 + 2704126 * 2 ^ 59
def prefixEnd_2704126 : Nat := 4983230072969 + 3 ^ 40 * 2704126 * 2
def baseEnd_2704126 : Nat := 1388516388319992328288957

theorem tailTrace_2704126 : CollatzResearch.WordTrace tailWord_2704126 prefixEnd_2704126 1388516388319992328288957 := by
  unfold tailWord_2704126
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328447225177600599738529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65751718534280536531938821 12328447225177600599738529)
  ·
    refine ⟨9246335418883200449803897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12328447225177600599738529 9246335418883200449803897)
    ·
      refine ⟨6934751564162400337352923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9246335418883200449803897 6934751564162400337352923)
      ·
        refine ⟨10402127346243600506029385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6934751564162400337352923 10402127346243600506029385)
        ·
          refine ⟨7801595509682700379522039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10402127346243600506029385 7801595509682700379522039)
          ·
            refine ⟨11702393264524050569283059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801595509682700379522039 11702393264524050569283059)
            ·
              refine ⟨17553589896786075853924589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11702393264524050569283059 17553589896786075853924589)
              ·
                refine ⟨6582596211294778445221721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17553589896786075853924589 6582596211294778445221721)
                ·
                  refine ⟨4936947158471083833916291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6582596211294778445221721 4936947158471083833916291)
                  ·
                    refine ⟨7405420737706625750874437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936947158471083833916291 7405420737706625750874437)
                    ·
                      refine ⟨1388516388319992328288957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7405420737706625750874437 1388516388319992328288957)
                      ·
                        rfl

theorem cell23_2704126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2704126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704126 prefixEnd_2704126 := by exact prefixLift 2704126
  have htrace : WordTrace (prefixWord ++ tailWord_2704126) baseStart_2704126 baseEnd_2704126 := by
    simpa [prefixWord, tailWord_2704126, baseEnd_2704126] using wordTrace_append hprefix tailTrace_2704126
  have hstable : (prefixWord ++ tailWord_2704126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704126).length < 2 ^ (prefixWord ++ tailWord_2704126).sum := by decide
  have hdescent : baseEnd_2704126 < baseStart_2704126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704149 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 6]
def baseStart_2704149 : Nat := 118140960795 + 2704149 * 2 ^ 59
def prefixEnd_2704149 : Nat := 4983230072969 + 3 ^ 40 * 2704149 * 2
def baseEnd_2704149 : Nat := 154280910930560637589039

theorem tailTrace_2704149 : CollatzResearch.WordTrace tailWord_2704149 prefixEnd_2704149 154280910930560637589039 := by
  unfold tailWord_2704149
  simp only [CollatzResearch.WordTrace]
  refine ⟨98628416680337479725995501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65752277786891653150663667 98628416680337479725995501)
  ·
    refine ⟨36985656255126554897248313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98628416680337479725995501 36985656255126554897248313)
    ·
      refine ⟨27739242191344916172936235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36985656255126554897248313 27739242191344916172936235)
      ·
        refine ⟨41608863287017374259404353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27739242191344916172936235 41608863287017374259404353)
        ·
          refine ⟨31206647465263030694553265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41608863287017374259404353 31206647465263030694553265)
          ·
            refine ⟨23404985598947273020914949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31206647465263030694553265 23404985598947273020914949)
            ·
              refine ⟨4388434799802613691421553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23404985598947273020914949 4388434799802613691421553)
              ·
                refine ⟨3291326099851960268566165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388434799802613691421553 3291326099851960268566165)
                ·
                  refine ⟨154280910930560637589039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3291326099851960268566165 154280910930560637589039)
                  ·
                    rfl

theorem cell23_2704149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_2704149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704149 prefixEnd_2704149 := by exact prefixLift 2704149
  have htrace : WordTrace (prefixWord ++ tailWord_2704149) baseStart_2704149 baseEnd_2704149 := by
    simpa [prefixWord, tailWord_2704149, baseEnd_2704149] using wordTrace_append hprefix tailTrace_2704149
  have hstable : (prefixWord ++ tailWord_2704149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704149).length < 2 ^ (prefixWord ++ tailWord_2704149).sum := by decide
  have hdescent : baseEnd_2704149 < baseStart_2704149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704152 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2704152 : Nat := 118140960795 + 2704152 * 2 ^ 59
def prefixEnd_2704152 : Nat := 4983230072969 + 3 ^ 40 * 2704152 * 2
def baseEnd_2704152 : Nat := 1388529738817009226563837

theorem tailTrace_2704152 : CollatzResearch.WordTrace tailWord_2704152 prefixEnd_2704152 1388529738817009226563837 := by
  unfold tailWord_2704152
  simp only [CollatzResearch.WordTrace]
  refine ⟨49314263049663305619177355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65752350732884407492236473 49314263049663305619177355)
  ·
    refine ⟨73971394574494958428766033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49314263049663305619177355 73971394574494958428766033)
    ·
      refine ⟨55478545930871218821574525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73971394574494958428766033 55478545930871218821574525)
      ·
        refine ⟨20804454724076707058090447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55478545930871218821574525 20804454724076707058090447)
        ·
          refine ⟨31206682086115060587135671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20804454724076707058090447 31206682086115060587135671)
          ·
            refine ⟨46810023129172590880703507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31206682086115060587135671 46810023129172590880703507)
            ·
              refine ⟨70215034693758886321055261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46810023129172590880703507 70215034693758886321055261)
              ·
                refine ⟨26330638010159582370395723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70215034693758886321055261 26330638010159582370395723)
                ·
                  refine ⟨39495957015239373555593585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26330638010159582370395723 39495957015239373555593585)
                  ·
                    refine ⟨29621967761429530166695189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39495957015239373555593585 29621967761429530166695189)
                    ·
                      refine ⟨1388529738817009226563837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29621967761429530166695189 1388529738817009226563837)
                      ·
                        rfl

theorem cell23_2704152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2704152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704152 prefixEnd_2704152 := by exact prefixLift 2704152
  have htrace : WordTrace (prefixWord ++ tailWord_2704152) baseStart_2704152 baseEnd_2704152 := by
    simpa [prefixWord, tailWord_2704152, baseEnd_2704152] using wordTrace_append hprefix tailTrace_2704152
  have hstable : (prefixWord ++ tailWord_2704152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704152).length < 2 ^ (prefixWord ++ tailWord_2704152).sum := by decide
  have hdescent : baseEnd_2704152 < baseStart_2704152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704169 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 5, 2]
def baseStart_2704169 : Nat := 118140960795 + 2704169 * 2 ^ 59
def prefixEnd_2704169 : Nat := 4983230072969 + 3 ^ 40 * 2704169 * 2
def baseEnd_2704169 : Nat := 1388538467988135660051259

theorem tailTrace_2704169 : CollatzResearch.WordTrace tailWord_2704169 prefixEnd_2704169 1388538467988135660051259 := by
  unfold tailWord_2704169
  simp only [CollatzResearch.WordTrace]
  refine ⟨98629146140265023141723561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65752764093510015427815707 98629146140265023141723561)
  ·
    refine ⟨73971859605198767356292671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98629146140265023141723561 73971859605198767356292671)
    ·
      refine ⟨110957789407798151034439007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73971859605198767356292671 110957789407798151034439007)
      ·
        refine ⟨166436684111697226551658511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110957789407798151034439007 166436684111697226551658511)
        ·
          refine ⟨249655026167545839827487767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166436684111697226551658511 249655026167545839827487767)
          ·
            refine ⟨374482539251318759741231651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249655026167545839827487767 374482539251318759741231651)
            ·
              refine ⟨561723808876978139611847477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374482539251318759741231651 561723808876978139611847477)
              ·
                refine ⟨52661607082216700588610701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 561723808876978139611847477 52661607082216700588610701)
                ·
                  refine ⟨19748102655831262720729013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52661607082216700588610701 19748102655831262720729013)
                  ·
                    refine ⟨1851384623984180880068345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19748102655831262720729013 1851384623984180880068345)
                    ·
                      refine ⟨1388538467988135660051259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851384623984180880068345 1388538467988135660051259)
                      ·
                        rfl

theorem cell23_2704169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 5, 2].length) (baseStart_2704169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704169 prefixEnd_2704169 := by exact prefixLift 2704169
  have htrace : WordTrace (prefixWord ++ tailWord_2704169) baseStart_2704169 baseEnd_2704169 := by
    simpa [prefixWord, tailWord_2704169, baseEnd_2704169] using wordTrace_append hprefix tailTrace_2704169
  have hstable : (prefixWord ++ tailWord_2704169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704169).length < 2 ^ (prefixWord ++ tailWord_2704169).sum := by decide
  have hdescent : baseEnd_2704169 < baseStart_2704169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704172 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2704172 : Nat := 118140960795 + 2704172 * 2 ^ 59
def prefixEnd_2704172 : Nat := 4983230072969 + 3 ^ 40 * 2704172 * 2
def baseEnd_2704172 : Nat := 1388540008430099148313745

theorem tailTrace_2704172 : CollatzResearch.WordTrace tailWord_2704172 prefixEnd_2704172 1388540008430099148313745 := by
  unfold tailWord_2704172
  simp only [CollatzResearch.WordTrace]
  refine ⟨49314627779627077327041385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65752837039502769769388513 49314627779627077327041385)
  ·
    refine ⟨36985970834720307995281039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49314627779627077327041385 36985970834720307995281039)
    ·
      refine ⟨55478956252080461992921559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36985970834720307995281039 55478956252080461992921559)
      ·
        refine ⟨83218434378120692989382339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55478956252080461992921559 83218434378120692989382339)
        ·
          refine ⟨124827651567181039484073509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83218434378120692989382339 124827651567181039484073509)
          ·
            refine ⟨23405184668846444903263783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124827651567181039484073509 23405184668846444903263783)
            ·
              refine ⟨35107777003269667354895675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23405184668846444903263783 35107777003269667354895675)
              ·
                refine ⟨52661665504904501032343513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35107777003269667354895675 52661665504904501032343513)
                ·
                  refine ⟨39496249128678375774257635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52661665504904501032343513 39496249128678375774257635)
                  ·
                    refine ⟨59244373693017563661386453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39496249128678375774257635 59244373693017563661386453)
                    ·
                      refine ⟨1388540008430099148313745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59244373693017563661386453 1388540008430099148313745)
                      ·
                        rfl

theorem cell23_2704172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2704172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704172 prefixEnd_2704172 := by exact prefixLift 2704172
  have htrace : WordTrace (prefixWord ++ tailWord_2704172) baseStart_2704172 baseEnd_2704172 := by
    simpa [prefixWord, tailWord_2704172, baseEnd_2704172] using wordTrace_append hprefix tailTrace_2704172
  have hstable : (prefixWord ++ tailWord_2704172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704172).length < 2 ^ (prefixWord ++ tailWord_2704172).sum := by decide
  have hdescent : baseEnd_2704172 < baseStart_2704172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704179 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 3, 5]
def baseStart_2704179 : Nat := 118140960795 + 2704179 * 2 ^ 59
def prefixEnd_2704179 : Nat := 4983230072969 + 3 ^ 40 * 2704179 * 2
def baseEnd_2704179 : Nat := 462847867598226873642071

theorem tailTrace_2704179 : CollatzResearch.WordTrace tailWord_2704179 prefixEnd_2704179 462847867598226873642071 := by
  unfold tailWord_2704179
  simp only [CollatzResearch.WordTrace]
  refine ⟨98629510870228794849587591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65753007246819196566391727 98629510870228794849587591)
  ·
    refine ⟨147944266305343192274381387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98629510870228794849587591 147944266305343192274381387)
    ·
      refine ⟨221916399458014788411572081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147944266305343192274381387 221916399458014788411572081)
      ·
        refine ⟨166437299593511091308679061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221916399458014788411572081 166437299593511091308679061)
        ·
          refine ⟨7801748418445832405094331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 166437299593511091308679061 7801748418445832405094331)
          ·
            refine ⟨11702622627668748607641497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801748418445832405094331 11702622627668748607641497)
            ·
              refine ⟨8776966970751561455731123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11702622627668748607641497 8776966970751561455731123)
              ·
                refine ⟨13165450456127342183596685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8776966970751561455731123 13165450456127342183596685)
                ·
                  refine ⟨4937043921047753318848757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13165450456127342183596685 4937043921047753318848757)
                  ·
                    refine ⟨462847867598226873642071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4937043921047753318848757 462847867598226873642071)
                    ·
                      rfl

theorem cell23_2704179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 5].length) (baseStart_2704179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704179 prefixEnd_2704179 := by exact prefixLift 2704179
  have htrace : WordTrace (prefixWord ++ tailWord_2704179) baseStart_2704179 baseEnd_2704179 := by
    simpa [prefixWord, tailWord_2704179, baseEnd_2704179] using wordTrace_append hprefix tailTrace_2704179
  have hstable : (prefixWord ++ tailWord_2704179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704179).length < 2 ^ (prefixWord ++ tailWord_2704179).sum := by decide
  have hdescent : baseEnd_2704179 < baseStart_2704179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704180 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2704180 : Nat := 118140960795 + 2704180 * 2 ^ 59
def prefixEnd_2704180 : Nat := 4983230072969 + 3 ^ 40 * 2704180 * 2
def baseEnd_2704180 : Nat := 1388544116275335117013709

theorem tailTrace_2704180 : CollatzResearch.WordTrace tailWord_2704180 prefixEnd_2704180 1388544116275335117013709 := by
  unfold tailWord_2704180
  simp only [CollatzResearch.WordTrace]
  refine ⟨49314773671612586010186997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65753031562150114680249329 49314773671612586010186997)
  ·
    refine ⟨4623260031713679938455031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49314773671612586010186997 4623260031713679938455031)
    ·
      refine ⟨6934890047570519907682547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623260031713679938455031 6934890047570519907682547)
      ·
        refine ⟨10402335071355779861523821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6934890047570519907682547 10402335071355779861523821)
        ·
          refine ⟨3900875651758417448071433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10402335071355779861523821 3900875651758417448071433)
          ·
            refine ⟨2925656738818813086053575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3900875651758417448071433 2925656738818813086053575)
            ·
              refine ⟨4388485108228219629080363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925656738818813086053575 4388485108228219629080363)
              ·
                refine ⟨6582727662342329443620545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388485108228219629080363 6582727662342329443620545)
                ·
                  refine ⟨4937045746756747082715409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6582727662342329443620545 4937045746756747082715409)
                  ·
                    refine ⟨3702784310067560312036557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937045746756747082715409 3702784310067560312036557)
                    ·
                      refine ⟨1388544116275335117013709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3702784310067560312036557 1388544116275335117013709)
                      ·
                        rfl

theorem cell23_2704180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2704180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704180 prefixEnd_2704180 := by exact prefixLift 2704180
  have htrace : WordTrace (prefixWord ++ tailWord_2704180) baseStart_2704180 baseEnd_2704180 := by
    simpa [prefixWord, tailWord_2704180, baseEnd_2704180] using wordTrace_append hprefix tailTrace_2704180
  have hstable : (prefixWord ++ tailWord_2704180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704180).length < 2 ^ (prefixWord ++ tailWord_2704180).sum := by decide
  have hdescent : baseEnd_2704180 < baseStart_2704180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704340 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_2704340 : Nat := 118140960795 + 2704340 * 2 ^ 59
def prefixEnd_2704340 : Nat := 4983230072969 + 3 ^ 40 * 2704340 * 2
def baseEnd_2704340 : Nat := 1388626273180054491012973

theorem tailTrace_2704340 : CollatzResearch.WordTrace tailWord_2704340 prefixEnd_2704340 1388626273180054491012973 := by
  unfold tailWord_2704340
  simp only [CollatzResearch.WordTrace]
  refine ⟨49317691511322759673099237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65756922015097012897465649 49317691511322759673099237)
  ·
    refine ⟨9247067158373017438706107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49317691511322759673099237 9247067158373017438706107)
    ·
      refine ⟨13870600737559526158059161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9247067158373017438706107 13870600737559526158059161)
      ·
        refine ⟨10402950553169644618544371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13870600737559526158059161 10402950553169644618544371)
        ·
          refine ⟨15604425829754466927816557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402950553169644618544371 15604425829754466927816557)
          ·
            refine ⟨5851659686157925097931209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15604425829754466927816557 5851659686157925097931209)
            ·
              refine ⟨4388744764618443823448407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5851659686157925097931209 4388744764618443823448407)
              ·
                refine ⟨6583117146927665735172611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388744764618443823448407 6583117146927665735172611)
                ·
                  refine ⟨9874675720391498602758917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583117146927665735172611 9874675720391498602758917)
                  ·
                    refine ⟨1851501697573405988017297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9874675720391498602758917 1851501697573405988017297)
                    ·
                      refine ⟨1388626273180054491012973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851501697573405988017297 1388626273180054491012973)
                      ·
                        rfl

theorem cell23_2704340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_2704340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704340 prefixEnd_2704340 := by exact prefixLift 2704340
  have htrace : WordTrace (prefixWord ++ tailWord_2704340) baseStart_2704340 baseEnd_2704340 := by
    simpa [prefixWord, tailWord_2704340, baseEnd_2704340] using wordTrace_append hprefix tailTrace_2704340
  have hstable : (prefixWord ++ tailWord_2704340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704340).length < 2 ^ (prefixWord ++ tailWord_2704340).sum := by decide
  have hdescent : baseEnd_2704340 < baseStart_2704340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704346 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_2704346 : Nat := 118140960795 + 2704346 * 2 ^ 59
def prefixEnd_2704346 : Nat := 4983230072969 + 3 ^ 40 * 2704346 * 2
def baseEnd_2704346 : Nat := 154292150451553496393105

theorem tailTrace_2704346 : CollatzResearch.WordTrace tailWord_2704346 prefixEnd_2704346 154292150451553496393105 := by
  unfold tailWord_2704346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24658900465155945592729223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65757067907082521580611261 24658900465155945592729223)
  ·
    refine ⟨36988350697733918389093835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24658900465155945592729223 36988350697733918389093835)
    ·
      refine ⟨55482526046600877583640753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36988350697733918389093835 55482526046600877583640753)
      ·
        refine ⟨41611894534950658187730565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55482526046600877583640753 41611894534950658187730565)
        ·
          refine ⟨7802230225303248410199481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41611894534950658187730565 7802230225303248410199481)
          ·
            refine ⟨5851672668977436307649611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802230225303248410199481 5851672668977436307649611)
            ·
              refine ⟨8777509003466154461474417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851672668977436307649611 8777509003466154461474417)
              ·
                refine ⟨6583131752599615846105813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8777509003466154461474417 6583131752599615846105813)
                ·
                  refine ⟨154292150451553496393105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6583131752599615846105813 154292150451553496393105)
                  ·
                    rfl

theorem cell23_2704346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_2704346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704346 prefixEnd_2704346 := by exact prefixLift 2704346
  have htrace : WordTrace (prefixWord ++ tailWord_2704346) baseStart_2704346 baseEnd_2704346 := by
    simpa [prefixWord, tailWord_2704346, baseEnd_2704346] using wordTrace_append hprefix tailTrace_2704346
  have hstable : (prefixWord ++ tailWord_2704346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704346).length < 2 ^ (prefixWord ++ tailWord_2704346).sum := by decide
  have hdescent : baseEnd_2704346 < baseStart_2704346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704374 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_2704374 : Nat := 118140960795 + 2704374 * 2 ^ 59
def prefixEnd_2704374 : Nat := 4983230072969 + 3 ^ 40 * 2704374 * 2
def baseEnd_2704374 : Nat := 1388643731522307357987817

theorem tailTrace_2704374 : CollatzResearch.WordTrace tailWord_2704374 prefixEnd_2704374 1388643731522307357987817 := by
  unfold tailWord_2704374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164788944032646447058511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65757748736348228768624117 6164788944032646447058511)
  ·
    refine ⟨9247183416048969670587767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164788944032646447058511 9247183416048969670587767)
    ·
      refine ⟨13870775124073454505881651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9247183416048969670587767 13870775124073454505881651)
      ·
        refine ⟨20806162686110181758822477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13870775124073454505881651 20806162686110181758822477)
        ·
          refine ⟨7802311007291318159558429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20806162686110181758822477 7802311007291318159558429)
          ·
            refine ⟨2925866627734244309834411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7802311007291318159558429 2925866627734244309834411)
            ·
              refine ⟨4388799941601366464751617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925866627734244309834411 4388799941601366464751617)
              ·
                refine ⟨3291599956201024848563713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388799941601366464751617 3291599956201024848563713)
                ·
                  refine ⟨2468699967150768636422785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3291599956201024848563713 2468699967150768636422785)
                  ·
                    refine ⟨1851524975363076477317089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2468699967150768636422785 1851524975363076477317089)
                    ·
                      refine ⟨1388643731522307357987817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851524975363076477317089 1388643731522307357987817)
                      ·
                        rfl

theorem cell23_2704374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_2704374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704374 prefixEnd_2704374 := by exact prefixLift 2704374
  have htrace : WordTrace (prefixWord ++ tailWord_2704374) baseStart_2704374 baseEnd_2704374 := by
    simpa [prefixWord, tailWord_2704374, baseEnd_2704374] using wordTrace_append hprefix tailTrace_2704374
  have hstable : (prefixWord ++ tailWord_2704374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704374).length < 2 ^ (prefixWord ++ tailWord_2704374).sum := by decide
  have hdescent : baseEnd_2704374 < baseStart_2704374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704396 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2704396 : Nat := 118140960795 + 2704396 * 2 ^ 59
def prefixEnd_2704396 : Nat := 4983230072969 + 3 ^ 40 * 2704396 * 2
def baseEnd_2704396 : Nat := 1388655028096706271912715

theorem tailTrace_2704396 : CollatzResearch.WordTrace tailWord_2704396 prefixEnd_2704396 1388655028096706271912715 := by
  unfold tailWord_2704396
  simp only [CollatzResearch.WordTrace]
  refine ⟨49318712755221320455118521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65758283673628427273491361 49318712755221320455118521)
  ·
    refine ⟨36989034566415990341338891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49318712755221320455118521 36989034566415990341338891)
    ·
      refine ⟨55483551849623985512008337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36989034566415990341338891 55483551849623985512008337)
      ·
        refine ⟨41612663887217989134006253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55483551849623985512008337 41612663887217989134006253)
        ·
          refine ⟨15604748957706745925252345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41612663887217989134006253 15604748957706745925252345)
          ·
            refine ⟨11703561718280059443939259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15604748957706745925252345 11703561718280059443939259)
            ·
              refine ⟨17555342577420089165908889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11703561718280059443939259 17555342577420089165908889)
              ·
                refine ⟨13166506933065066874431667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17555342577420089165908889 13166506933065066874431667)
                ·
                  refine ⟨19749760399597600311647501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13166506933065066874431667 19749760399597600311647501)
                  ·
                    refine ⟨7406160149849100116867813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19749760399597600311647501 7406160149849100116867813)
                    ·
                      refine ⟨1388655028096706271912715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7406160149849100116867813 1388655028096706271912715)
                      ·
                        rfl

theorem cell23_2704396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2704396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704396 prefixEnd_2704396 := by exact prefixLift 2704396
  have htrace : WordTrace (prefixWord ++ tailWord_2704396) baseStart_2704396 baseEnd_2704396 := by
    simpa [prefixWord, tailWord_2704396, baseEnd_2704396] using wordTrace_append hprefix tailTrace_2704396
  have hstable : (prefixWord ++ tailWord_2704396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704396).length < 2 ^ (prefixWord ++ tailWord_2704396).sum := by decide
  have hdescent : baseEnd_2704396 < baseStart_2704396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704399 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_2704399 : Nat := 118140960795 + 2704399 * 2 ^ 59
def prefixEnd_2704399 : Nat := 4983230072969 + 3 ^ 40 * 2704399 * 2
def baseEnd_2704399 : Nat := 1388656568538669760175201

theorem tailTrace_2704399 : CollatzResearch.WordTrace tailWord_2704399 prefixEnd_2704399 1388656568538669760175201 := by
  unfold tailWord_2704399
  simp only [CollatzResearch.WordTrace]
  refine ⟨98637534929431772422596251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65758356619621181615064167 98637534929431772422596251)
  ·
    refine ⟨147956302394147658633894377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98637534929431772422596251 147956302394147658633894377)
    ·
      refine ⟨110967226795610743975420783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147956302394147658633894377 110967226795610743975420783)
      ·
        refine ⟨166450840193416115963131175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110967226795610743975420783 166450840193416115963131175)
        ·
          refine ⟨249676260290124173944696763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166450840193416115963131175 249676260290124173944696763)
          ·
            refine ⟨374514390435186260917045145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249676260290124173944696763 374514390435186260917045145)
            ·
              refine ⟨280885792826389695687783859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374514390435186260917045145 280885792826389695687783859)
              ·
                refine ⟨421328689239584543531675789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280885792826389695687783859 421328689239584543531675789)
                ·
                  refine ⟨157998258464844203824378421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421328689239584543531675789 157998258464844203824378421)
                  ·
                    refine ⟨14812336731079144108535477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 157998258464844203824378421 14812336731079144108535477)
                    ·
                      refine ⟨1388656568538669760175201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14812336731079144108535477 1388656568538669760175201)
                      ·
                        rfl

theorem cell23_2704399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_2704399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704399 prefixEnd_2704399 := by exact prefixLift 2704399
  have htrace : WordTrace (prefixWord ++ tailWord_2704399) baseStart_2704399 baseEnd_2704399 := by
    simpa [prefixWord, tailWord_2704399, baseEnd_2704399] using wordTrace_append hprefix tailTrace_2704399
  have hstable : (prefixWord ++ tailWord_2704399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704399).length < 2 ^ (prefixWord ++ tailWord_2704399).sum := by decide
  have hdescent : baseEnd_2704399 < baseStart_2704399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704433 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_2704433 : Nat := 118140960795 + 2704433 * 2 ^ 59
def prefixEnd_2704433 : Nat := 4983230072969 + 3 ^ 40 * 2704433 * 2
def baseEnd_2704433 : Nat := 1388674026880922627150045

theorem tailTrace_2704433 : CollatzResearch.WordTrace tailWord_2704433 prefixEnd_2704433 1388674026880922627150045 := by
  unfold tailWord_2704433
  simp only [CollatzResearch.WordTrace]
  refine ⟨98638775011308596229333953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65759183340872397486222635 98638775011308596229333953)
  ·
    refine ⟨73979081258481447172000465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98638775011308596229333953 73979081258481447172000465)
    ·
      refine ⟨55484310943861085379000349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73979081258481447172000465 55484310943861085379000349)
      ·
        refine ⟨20806616603947907017125131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55484310943861085379000349 20806616603947907017125131)
        ·
          refine ⟨31209924905921860525687697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20806616603947907017125131 31209924905921860525687697)
          ·
            refine ⟨23407443679441395394265773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31209924905921860525687697 23407443679441395394265773)
            ·
              refine ⟨8777791379790523272849665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23407443679441395394265773 8777791379790523272849665)
              ·
                refine ⟨6583343534842892454637249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8777791379790523272849665 6583343534842892454637249)
                ·
                  refine ⟨4937507651132169340977937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6583343534842892454637249 4937507651132169340977937)
                  ·
                    refine ⟨3703130738349127005733453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937507651132169340977937 3703130738349127005733453)
                    ·
                      refine ⟨1388674026880922627150045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703130738349127005733453 1388674026880922627150045)
                      ·
                        rfl

theorem cell23_2704433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_2704433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704433 prefixEnd_2704433 := by exact prefixLift 2704433
  have htrace : WordTrace (prefixWord ++ tailWord_2704433) baseStart_2704433 baseEnd_2704433 := by
    simpa [prefixWord, tailWord_2704433, baseEnd_2704433] using wordTrace_append hprefix tailTrace_2704433
  have hstable : (prefixWord ++ tailWord_2704433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704433).length < 2 ^ (prefixWord ++ tailWord_2704433).sum := by decide
  have hdescent : baseEnd_2704433 < baseStart_2704433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704440 : List Nat := [2, 1, 2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_2704440 : Nat := 118140960795 + 2704440 * 2 ^ 59
def prefixEnd_2704440 : Nat := 4983230072969 + 3 ^ 40 * 2704440 * 2
def baseEnd_2704440 : Nat := 462892540415168033254171

theorem tailTrace_2704440 : CollatzResearch.WordTrace tailWord_2704440 prefixEnd_2704440 462892540415168033254171 := by
  unfold tailWord_2704440
  simp only [CollatzResearch.WordTrace]
  refine ⟨49319515161141618212419387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65759353548188824283225849 49319515161141618212419387)
  ·
    refine ⟨73979272741712427318629081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49319515161141618212419387 73979272741712427318629081)
    ·
      refine ⟨55484454556284320488971811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73979272741712427318629081 55484454556284320488971811)
      ·
        refine ⟨83226681834426480733457717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55484454556284320488971811 83226681834426480733457717)
        ·
          refine ⟨7802501421977482568761661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83226681834426480733457717 7802501421977482568761661)
          ·
            refine ⟨2925938033241555963285623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7802501421977482568761661 2925938033241555963285623)
            ·
              refine ⟨4388907049862333944928435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925938033241555963285623 4388907049862333944928435)
              ·
                refine ⟨6583360574793500917392653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388907049862333944928435 6583360574793500917392653)
                ·
                  refine ⟨2468760215547562844022245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6583360574793500917392653 2468760215547562844022245)
                  ·
                    refine ⟨462892540415168033254171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2468760215547562844022245 462892540415168033254171)
                    ·
                      rfl

theorem cell23_2704440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_2704440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704440 prefixEnd_2704440 := by exact prefixLift 2704440
  have htrace : WordTrace (prefixWord ++ tailWord_2704440) baseStart_2704440 baseEnd_2704440 := by
    simpa [prefixWord, tailWord_2704440, baseEnd_2704440] using wordTrace_append hprefix tailTrace_2704440
  have hstable : (prefixWord ++ tailWord_2704440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704440).length < 2 ^ (prefixWord ++ tailWord_2704440).sum := by decide
  have hdescent : baseEnd_2704440 < baseStart_2704440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704453 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 6]
def baseStart_2704453 : Nat := 118140960795 + 2704453 * 2 ^ 59
def prefixEnd_2704453 : Nat := 4983230072969 + 3 ^ 40 * 2704453 * 2
def baseEnd_2704453 : Nat := 154298255166001394322217

theorem tailTrace_2704453 : CollatzResearch.WordTrace tailWord_2704453 prefixEnd_2704453 154298255166001394322217 := by
  unfold tailWord_2704453
  simp only [CollatzResearch.WordTrace]
  refine ⟨98639504471236139645062013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65759669647490759763374675 98639504471236139645062013)
  ·
    refine ⟨36989814176713552366898255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98639504471236139645062013 36989814176713552366898255)
    ·
      refine ⟨55484721265070328550347383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36989814176713552366898255 55484721265070328550347383)
      ·
        refine ⟨83227081897605492825521075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55484721265070328550347383 83227081897605492825521075)
        ·
          refine ⟨124840622846408239238281613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83227081897605492825521075 124840622846408239238281613)
          ·
            refine ⟨46815233567403089714355605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124840622846408239238281613 46815233567403089714355605)
            ·
              refine ⟨2194464073472019830360419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46815233567403089714355605 2194464073472019830360419)
              ·
                refine ⟨3291696110208029745540629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194464073472019830360419 3291696110208029745540629)
                ·
                  refine ⟨154298255166001394322217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3291696110208029745540629 154298255166001394322217)
                  ·
                    rfl

theorem cell23_2704453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_2704453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704453 prefixEnd_2704453 := by exact prefixLift 2704453
  have htrace : WordTrace (prefixWord ++ tailWord_2704453) baseStart_2704453 baseEnd_2704453 := by
    simpa [prefixWord, tailWord_2704453, baseEnd_2704453] using wordTrace_append hprefix tailTrace_2704453
  have hstable : (prefixWord ++ tailWord_2704453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704453).length < 2 ^ (prefixWord ++ tailWord_2704453).sum := by decide
  have hdescent : baseEnd_2704453 < baseStart_2704453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704496 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_2704496 : Nat := 118140960795 + 2704496 * 2 ^ 59
def prefixEnd_2704496 : Nat := 4983230072969 + 3 ^ 40 * 2704496 * 2
def baseEnd_2704496 : Nat := 462902125387385293554085

theorem tailTrace_2704496 : CollatzResearch.WordTrace tailWord_2704496 prefixEnd_2704496 462902125387385293554085 := by
  unfold tailWord_2704496
  simp only [CollatzResearch.WordTrace]
  refine ⟨49320536405040178994438671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65760715206720238659251561 49320536405040178994438671)
  ·
    refine ⟨73980804607560268491658007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49320536405040178994438671 73980804607560268491658007)
    ·
      refine ⟨110971206911340402737487011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73980804607560268491658007 110971206911340402737487011)
      ·
        refine ⟨166456810367010604106230517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110971206911340402737487011 166456810367010604106230517)
        ·
          refine ⟨15605325971907244134959111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166456810367010604106230517 15605325971907244134959111)
          ·
            refine ⟨23407988957860866202438667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15605325971907244134959111 23407988957860866202438667)
            ·
              refine ⟨35111983436791299303658001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23407988957860866202438667 35111983436791299303658001)
              ·
                refine ⟨26333987577593474477743501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35111983436791299303658001 26333987577593474477743501)
                ·
                  refine ⟨9875245341597552929153813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26333987577593474477743501 9875245341597552929153813)
                  ·
                    refine ⟨462902125387385293554085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9875245341597552929153813 462902125387385293554085)
                    ·
                      rfl

theorem cell23_2704496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_2704496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704496 prefixEnd_2704496 := by exact prefixLift 2704496
  have htrace : WordTrace (prefixWord ++ tailWord_2704496) baseStart_2704496 baseEnd_2704496 := by
    simpa [prefixWord, tailWord_2704496, baseEnd_2704496] using wordTrace_append hprefix tailTrace_2704496
  have hstable : (prefixWord ++ tailWord_2704496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704496).length < 2 ^ (prefixWord ++ tailWord_2704496).sum := by decide
  have hdescent : baseEnd_2704496 < baseStart_2704496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704513 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 1, 6]
def baseStart_2704513 : Nat := 118140960795 + 2704513 * 2 ^ 59
def prefixEnd_2704513 : Nat := 4983230072969 + 3 ^ 40 * 2704513 * 2
def baseEnd_2704513 : Nat := 462905035111094104716559

theorem tailTrace_2704513 : CollatzResearch.WordTrace tailWord_2704513 prefixEnd_2704513 462905035111094104716559 := by
  unfold tailWord_2704513
  simp only [CollatzResearch.WordTrace]
  refine ⟨98641692851018769892246193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65761128567345846594830795 98641692851018769892246193)
  ·
    refine ⟨73981269638264077419184645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98641692851018769892246193 73981269638264077419184645)
    ·
      refine ⟨13871488057174514516097121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73981269638264077419184645 13871488057174514516097121)
      ·
        refine ⟨10403616042880885887072841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13871488057174514516097121 10403616042880885887072841)
        ·
          refine ⟨7802712032160664415304631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10403616042880885887072841 7802712032160664415304631)
          ·
            refine ⟨11704068048240996622956947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802712032160664415304631 11704068048240996622956947)
            ·
              refine ⟨17556102072361494934435421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704068048240996622956947 17556102072361494934435421)
              ·
                refine ⟨6583538277135560600413283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17556102072361494934435421 6583538277135560600413283)
                ·
                  refine ⟨9875307415703340900619925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583538277135560600413283 9875307415703340900619925)
                  ·
                    refine ⟨462905035111094104716559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9875307415703340900619925 462905035111094104716559)
                    ·
                      rfl

theorem cell23_2704513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_2704513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704513 prefixEnd_2704513 := by exact prefixLift 2704513
  have htrace : WordTrace (prefixWord ++ tailWord_2704513) baseStart_2704513 baseEnd_2704513 := by
    simpa [prefixWord, tailWord_2704513, baseEnd_2704513] using wordTrace_append hprefix tailTrace_2704513
  have hstable : (prefixWord ++ tailWord_2704513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704513).length < 2 ^ (prefixWord ++ tailWord_2704513).sum := by decide
  have hdescent : baseEnd_2704513 < baseStart_2704513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704543 : List Nat := [1, 1, 2, 6, 2, 1, 10]
def baseStart_2704543 : Nat := 118140960795 + 2704543 * 2 ^ 59
def prefixEnd_2704543 : Nat := 4983230072969 + 3 ^ 40 * 2704543 * 2
def baseEnd_2704543 : Nat := 17144821108060706133019

theorem tailTrace_2704543 : CollatzResearch.WordTrace tailWord_2704543 prefixEnd_2704543 17144821108060706133019 := by
  unfold tailWord_2704543
  simp only [CollatzResearch.WordTrace]
  refine ⟨98642787040910085015838283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65761858027273390010558855 98642787040910085015838283)
  ·
    refine ⟨147964180561365127523757425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98642787040910085015838283 147964180561365127523757425)
    ·
      refine ⟨110973135421023845642818069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147964180561365127523757425 110973135421023845642818069)
      ·
        refine ⟨5201865722860492764507097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110973135421023845642818069 5201865722860492764507097)
        ·
          refine ⟨3901399292145369573380323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5201865722860492764507097 3901399292145369573380323)
          ·
            refine ⟨5852098938218054360070485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901399292145369573380323 5852098938218054360070485)
            ·
              refine ⟨17144821108060706133019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5852098938218054360070485 17144821108060706133019)
              ·
                rfl

theorem cell23_2704543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 10].length) (baseStart_2704543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704543 prefixEnd_2704543 := by exact prefixLift 2704543
  have htrace : WordTrace (prefixWord ++ tailWord_2704543) baseStart_2704543 baseEnd_2704543 := by
    simpa [prefixWord, tailWord_2704543, baseEnd_2704543] using wordTrace_append hprefix tailTrace_2704543
  have hstable : (prefixWord ++ tailWord_2704543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704543).length < 2 ^ (prefixWord ++ tailWord_2704543).sum := by decide
  have hdescent : baseEnd_2704543 < baseStart_2704543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704554 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2704554 : Nat := 118140960795 + 2704554 * 2 ^ 59
def prefixEnd_2704554 : Nat := 4983230072969 + 3 ^ 40 * 2704554 * 2
def baseEnd_2704554 : Nat := 1388736158040116653736989

theorem tailTrace_2704554 : CollatzResearch.WordTrace tailWord_2704554 prefixEnd_2704554 1388736158040116653736989 := by
  unfold tailWord_2704554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24660797060967558473622179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65762125495913489262992477 24660797060967558473622179)
  ·
    refine ⟨36991195591451337710433269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24660797060967558473622179 36991195591451337710433269)
    ·
      refine ⟨3467924586698562910353119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36991195591451337710433269 3467924586698562910353119)
      ·
        refine ⟨5201886880047844365529679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467924586698562910353119 5201886880047844365529679)
        ·
          refine ⟨7802830320071766548294519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201886880047844365529679 7802830320071766548294519)
          ·
            refine ⟨11704245480107649822441779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802830320071766548294519 11704245480107649822441779)
            ·
              refine ⟨17556368220161474733662669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11704245480107649822441779 17556368220161474733662669)
              ·
                refine ⟨6583638082560553025123501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17556368220161474733662669 6583638082560553025123501)
                ·
                  refine ⟨2468864280960207384421313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6583638082560553025123501 2468864280960207384421313)
                  ·
                    refine ⟨1851648210720155538315985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2468864280960207384421313 1851648210720155538315985)
                    ·
                      refine ⟨1388736158040116653736989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851648210720155538315985 1388736158040116653736989)
                      ·
                        rfl

theorem cell23_2704554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2704554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704554 prefixEnd_2704554 := by exact prefixLift 2704554
  have htrace : WordTrace (prefixWord ++ tailWord_2704554) baseStart_2704554 baseEnd_2704554 := by
    simpa [prefixWord, tailWord_2704554, baseEnd_2704554] using wordTrace_append hprefix tailTrace_2704554
  have hstable : (prefixWord ++ tailWord_2704554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704554).length < 2 ^ (prefixWord ++ tailWord_2704554).sum := by decide
  have hdescent : baseEnd_2704554 < baseStart_2704554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704556 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_2704556 : Nat := 118140960795 + 2704556 * 2 ^ 59
def prefixEnd_2704556 : Nat := 4983230072969 + 3 ^ 40 * 2704556 * 2
def baseEnd_2704556 : Nat := 462912395000475215303993

theorem tailTrace_2704556 : CollatzResearch.WordTrace tailWord_2704556 prefixEnd_2704556 462912395000475215303993 := by
  unfold tailWord_2704556
  simp only [CollatzResearch.WordTrace]
  refine ⟨49321630594931494118030761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65762174126575325490707681 49321630594931494118030761)
  ·
    refine ⟨36991222946198620588523071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49321630594931494118030761 36991222946198620588523071)
    ·
      refine ⟨55486834419297930882784607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36991222946198620588523071 55486834419297930882784607)
      ·
        refine ⟨83230251628946896324176911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55486834419297930882784607 83230251628946896324176911)
        ·
          refine ⟨124845377443420344486265367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83230251628946896324176911 124845377443420344486265367)
          ·
            refine ⟨187268066165130516729398051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124845377443420344486265367 187268066165130516729398051)
            ·
              refine ⟨280902099247695775094097077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187268066165130516729398051 280902099247695775094097077)
              ·
                refine ⟨26334571804471478915071601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 280902099247695775094097077 26334571804471478915071601)
                ·
                  refine ⟨19750928853353609186303701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26334571804471478915071601 19750928853353609186303701)
                  ·
                    refine ⟨462912395000475215303993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19750928853353609186303701 462912395000475215303993)
                    ·
                      rfl

theorem cell23_2704556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_2704556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704556 prefixEnd_2704556 := by exact prefixLift 2704556
  have htrace : WordTrace (prefixWord ++ tailWord_2704556) baseStart_2704556 baseEnd_2704556 := by
    simpa [prefixWord, tailWord_2704556, baseEnd_2704556] using wordTrace_append hprefix tailTrace_2704556
  have hstable : (prefixWord ++ tailWord_2704556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704556).length < 2 ^ (prefixWord ++ tailWord_2704556).sum := by decide
  have hdescent : baseEnd_2704556 < baseStart_2704556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704577 : List Nat := [1, 2, 6, 1, 1, 3, 2, 7]
def baseStart_2704577 : Nat := 118140960795 + 2704577 * 2 ^ 59
def prefixEnd_2704577 : Nat := 4983230072969 + 3 ^ 40 * 2704577 * 2
def baseEnd_2704577 : Nat := 51435109929450743101829

theorem tailTrace_2704577 : CollatzResearch.WordTrace tailWord_2704577 prefixEnd_2704577 51435109929450743101829 := by
  unfold tailWord_2704577
  simp only [CollatzResearch.WordTrace]
  refine ⟨98644027122786908822575985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65762684748524605881717323 98644027122786908822575985)
  ·
    refine ⟨73983020342090181616931989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98644027122786908822575985 73983020342090181616931989)
    ·
      refine ⟨3467954078535477263293687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73983020342090181616931989 3467954078535477263293687)
      ·
        refine ⟨5201931117803215894940531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467954078535477263293687 5201931117803215894940531)
        ·
          refine ⟨7802896676704823842410797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5201931117803215894940531 7802896676704823842410797)
          ·
            refine ⟨2926086253764308940904049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7802896676704823842410797 2926086253764308940904049)
            ·
              refine ⟨2194564690323231705678037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926086253764308940904049 2194564690323231705678037)
              ·
                refine ⟨51435109929450743101829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2194564690323231705678037 51435109929450743101829)
                ·
                  rfl

theorem cell23_2704577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 7].length) (baseStart_2704577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704577 prefixEnd_2704577 := by exact prefixLift 2704577
  have htrace : WordTrace (prefixWord ++ tailWord_2704577) baseStart_2704577 baseEnd_2704577 := by
    simpa [prefixWord, tailWord_2704577, baseEnd_2704577] using wordTrace_append hprefix tailTrace_2704577
  have hstable : (prefixWord ++ tailWord_2704577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704577).length < 2 ^ (prefixWord ++ tailWord_2704577).sum := by decide
  have hdescent : baseEnd_2704577 < baseStart_2704577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704582 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2704582 : Nat := 118140960795 + 2704582 * 2 ^ 59
def prefixEnd_2704582 : Nat := 4983230072969 + 3 ^ 40 * 2704582 * 2
def baseEnd_2704582 : Nat := 1388750535498442544186861

theorem tailTrace_2704582 : CollatzResearch.WordTrace tailWord_2704582 prefixEnd_2704582 1388750535498442544186861 := by
  unfold tailWord_2704582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082631546492774833640875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65762806325179196451005333 3082631546492774833640875)
  ·
    refine ⟨4623947319739162250461313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082631546492774833640875 4623947319739162250461313)
    ·
      refine ⟨3467960489804371687845985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4623947319739162250461313 3467960489804371687845985)
      ·
        refine ⟨2600970367353278765884489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3467960489804371687845985 2600970367353278765884489)
        ·
          refine ⟨1950727775514959074413367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2600970367353278765884489 1950727775514959074413367)
          ·
            refine ⟨2926091663272438611620051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950727775514959074413367 2926091663272438611620051)
            ·
              refine ⟨4389137494908657917430077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926091663272438611620051 4389137494908657917430077)
              ·
                refine ⟨1645926560590746719036279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389137494908657917430077 1645926560590746719036279)
                ·
                  refine ⟨2468889840886120078554419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645926560590746719036279 2468889840886120078554419)
                  ·
                    refine ⟨3703334761329180117831629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2468889840886120078554419 3703334761329180117831629)
                    ·
                      refine ⟨1388750535498442544186861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703334761329180117831629 1388750535498442544186861)
                      ·
                        rfl

theorem cell23_2704582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2704582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704582 prefixEnd_2704582 := by exact prefixLift 2704582
  have htrace : WordTrace (prefixWord ++ tailWord_2704582) baseStart_2704582 baseEnd_2704582 := by
    simpa [prefixWord, tailWord_2704582, baseEnd_2704582] using wordTrace_append hprefix tailTrace_2704582
  have hstable : (prefixWord ++ tailWord_2704582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704582).length < 2 ^ (prefixWord ++ tailWord_2704582).sum := by decide
  have hdescent : baseEnd_2704582 < baseStart_2704582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704621 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_2704621 : Nat := 118140960795 + 2704621 * 2 ^ 59
def prefixEnd_2704621 : Nat := 4983230072969 + 3 ^ 40 * 2704621 * 2
def baseEnd_2704621 : Nat := 1388770561243967891599181

theorem tailTrace_2704621 : CollatzResearch.WordTrace tailWord_2704621 prefixEnd_2704621 1388770561243967891599181 := by
  unfold tailWord_2704621
  simp only [CollatzResearch.WordTrace]
  refine ⟨98645631934627504337177717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65763754623085002891451811 98645631934627504337177717)
  ·
    refine ⟨9248027993871328531610411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98645631934627504337177717 9248027993871328531610411)
    ·
      refine ⟨13872041990806992797415617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9248027993871328531610411 13872041990806992797415617)
      ·
        refine ⟨10404031493105244598061713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13872041990806992797415617 10404031493105244598061713)
        ·
          refine ⟨7803023619828933448546285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10404031493105244598061713 7803023619828933448546285)
          ·
            refine ⟨2926133857435850043204857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7803023619828933448546285 2926133857435850043204857)
            ·
              refine ⟨2194600393076887532403643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926133857435850043204857 2194600393076887532403643)
              ·
                refine ⟨3291900589615331298605465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194600393076887532403643 3291900589615331298605465)
                ·
                  refine ⟨2468925442211498473954099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3291900589615331298605465 2468925442211498473954099)
                  ·
                    refine ⟨3703388163317247710931149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2468925442211498473954099 3703388163317247710931149)
                    ·
                      refine ⟨1388770561243967891599181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703388163317247710931149 1388770561243967891599181)
                      ·
                        rfl

theorem cell23_2704621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_2704621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704621 prefixEnd_2704621 := by exact prefixLift 2704621
  have htrace : WordTrace (prefixWord ++ tailWord_2704621) baseStart_2704621 baseEnd_2704621 := by
    simpa [prefixWord, tailWord_2704621, baseEnd_2704621] using wordTrace_append hprefix tailTrace_2704621
  have hstable : (prefixWord ++ tailWord_2704621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704621).length < 2 ^ (prefixWord ++ tailWord_2704621).sum := by decide
  have hdescent : baseEnd_2704621 < baseStart_2704621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704650 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_2704650 : Nat := 118140960795 + 2704650 * 2 ^ 59
def prefixEnd_2704650 : Nat := 4983230072969 + 3 ^ 40 * 2704650 * 2
def baseEnd_2704650 : Nat := 154309494686994253126283

theorem tailTrace_2704650 : CollatzResearch.WordTrace tailWord_2704650 prefixEnd_2704650 154309494686994253126283 := by
  unfold tailWord_2704650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24661672412880610572495851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65764459767681628193322269 24661672412880610572495851)
  ·
    refine ⟨36992508619320915858743777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24661672412880610572495851 36992508619320915858743777)
    ·
      refine ⟨27744381464490686894057833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36992508619320915858743777 27744381464490686894057833)
      ·
        refine ⟨20808286098368015170543375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27744381464490686894057833 20808286098368015170543375)
        ·
          refine ⟨31212429147552022755815063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20808286098368015170543375 31212429147552022755815063)
          ·
            refine ⟨46818643721328034133722595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31212429147552022755815063 46818643721328034133722595)
            ·
              refine ⟨70227965581992051200583893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46818643721328034133722595 70227965581992051200583893)
              ·
                refine ⟨1645967943327938700013685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70227965581992051200583893 1645967943327938700013685)
                ·
                  refine ⟨154309494686994253126283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1645967943327938700013685 154309494686994253126283)
                  ·
                    rfl

theorem cell23_2704650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_2704650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704650 prefixEnd_2704650 := by exact prefixLift 2704650
  have htrace : WordTrace (prefixWord ++ tailWord_2704650) baseStart_2704650 baseEnd_2704650 := by
    simpa [prefixWord, tailWord_2704650, baseEnd_2704650] using wordTrace_append hprefix tailTrace_2704650
  have hstable : (prefixWord ++ tailWord_2704650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704650).length < 2 ^ (prefixWord ++ tailWord_2704650).sum := by decide
  have hdescent : baseEnd_2704650 < baseStart_2704650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704700 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2704700 : Nat := 118140960795 + 2704700 * 2 ^ 59
def prefixEnd_2704700 : Nat := 4983230072969 + 3 ^ 40 * 2704700 * 2
def baseEnd_2704700 : Nat := 1388811126215673082511317

theorem tailTrace_2704700 : CollatzResearch.WordTrace tailWord_2704700 prefixEnd_2704700 1388811126215673082511317 := by
  unfold tailWord_2704700
  simp only [CollatzResearch.WordTrace]
  refine ⟨49324256650670650414651777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65765675534227533886202369 49324256650670650414651777)
  ·
    refine ⟨36993192488002987810988833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49324256650670650414651777 36993192488002987810988833)
    ·
      refine ⟨27744894366002240858241625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36993192488002987810988833 27744894366002240858241625)
      ·
        refine ⟨20808670774501680643681219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27744894366002240858241625 20808670774501680643681219)
        ·
          refine ⟨31213006161752520965521829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20808670774501680643681219 31213006161752520965521829)
          ·
            refine ⟨5852438655328597681035343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31213006161752520965521829 5852438655328597681035343)
            ·
              refine ⟨8778657982992896521553015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5852438655328597681035343 8778657982992896521553015)
              ·
                refine ⟨13167986974489344782329523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8778657982992896521553015 13167986974489344782329523)
                ·
                  refine ⟨19751980461734017173494285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13167986974489344782329523 19751980461734017173494285)
                  ·
                    refine ⟨7406992673150256440060357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19751980461734017173494285 7406992673150256440060357)
                    ·
                      refine ⟨1388811126215673082511317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7406992673150256440060357 1388811126215673082511317)
                      ·
                        rfl

theorem cell23_2704700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2704700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704700 prefixEnd_2704700 := by exact prefixLift 2704700
  have htrace : WordTrace (prefixWord ++ tailWord_2704700) baseStart_2704700 baseEnd_2704700 := by
    simpa [prefixWord, tailWord_2704700, baseEnd_2704700] using wordTrace_append hprefix tailTrace_2704700
  have hstable : (prefixWord ++ tailWord_2704700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704700).length < 2 ^ (prefixWord ++ tailWord_2704700).sum := by decide
  have hdescent : baseEnd_2704700 < baseStart_2704700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704713 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_2704713 : Nat := 118140960795 + 2704713 * 2 ^ 59
def prefixEnd_2704713 : Nat := 4983230072969 + 3 ^ 40 * 2704713 * 2
def baseEnd_2704713 : Nat := 1388817801464181531648757

theorem tailTrace_2704713 : CollatzResearch.WordTrace tailWord_2704713 prefixEnd_2704713 1388817801464181531648757 := by
  unfold tailWord_2704713
  simp only [CollatzResearch.WordTrace]
  refine ⟨98648987450294204049526793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65765991633529469366351195 98648987450294204049526793)
  ·
    refine ⟨73986740587720653037145095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98648987450294204049526793 73986740587720653037145095)
    ·
      refine ⟨110980110881580979555717643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73986740587720653037145095 110980110881580979555717643)
      ·
        refine ⟨166470166322371469333576465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110980110881580979555717643 166470166322371469333576465)
        ·
          refine ⟨124852624741778602000182349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166470166322371469333576465 124852624741778602000182349)
          ·
            refine ⟨46819734278166975750068381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124852624741778602000182349 46819734278166975750068381)
            ·
              refine ⟨17557400354312615906275643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46819734278166975750068381 17557400354312615906275643)
              ·
                refine ⟨26336100531468923859413465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17557400354312615906275643 26336100531468923859413465)
                ·
                  refine ⟨19752075398601692894560099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26336100531468923859413465 19752075398601692894560099)
                  ·
                    refine ⟨29628113097902539341840149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19752075398601692894560099 29628113097902539341840149)
                    ·
                      refine ⟨1388817801464181531648757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29628113097902539341840149 1388817801464181531648757)
                      ·
                        rfl

theorem cell23_2704713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_2704713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704713 prefixEnd_2704713 := by exact prefixLift 2704713
  have htrace : WordTrace (prefixWord ++ tailWord_2704713) baseStart_2704713 baseEnd_2704713 := by
    simpa [prefixWord, tailWord_2704713, baseEnd_2704713] using wordTrace_append hprefix tailTrace_2704713
  have hstable : (prefixWord ++ tailWord_2704713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704713).length < 2 ^ (prefixWord ++ tailWord_2704713).sum := by decide
  have hdescent : baseEnd_2704713 < baseStart_2704713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704720 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_2704720 : Nat := 118140960795 + 2704720 * 2 ^ 59
def prefixEnd_2704720 : Nat := 4983230072969 + 3 ^ 40 * 2704720 * 2
def baseEnd_2704720 : Nat := 1388821395828763004261225

theorem tailTrace_2704720 : CollatzResearch.WordTrace tailWord_2704720 prefixEnd_2704720 1388821395828763004261225 := by
  unfold tailWord_2704720
  simp only [CollatzResearch.WordTrace]
  refine ⟨49324621380634422122515807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65766161840845896163354409 49324621380634422122515807)
  ·
    refine ⟨73986932070951633183773711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49324621380634422122515807 73986932070951633183773711)
    ·
      refine ⟨110980398106427449775660567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73986932070951633183773711 110980398106427449775660567)
      ·
        refine ⟨166470597159641174663490851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110980398106427449775660567 166470597159641174663490851)
        ·
          refine ⟨249705895739461761995236277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166470597159641174663490851 249705895739461761995236277)
          ·
            refine ⟨23409927725574540187053401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249705895739461761995236277 23409927725574540187053401)
            ·
              refine ⟨17557445794180905140290051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23409927725574540187053401 17557445794180905140290051)
              ·
                refine ⟨26336168691271357710435077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17557445794180905140290051 26336168691271357710435077)
                ·
                  refine ⟨4938031629613379570706577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26336168691271357710435077 4938031629613379570706577)
                  ·
                    refine ⟨3703523722210034678029933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4938031629613379570706577 3703523722210034678029933)
                    ·
                      refine ⟨1388821395828763004261225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703523722210034678029933 1388821395828763004261225)
                      ·
                        rfl

theorem cell23_2704720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_2704720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704720 prefixEnd_2704720 := by exact prefixLift 2704720
  have htrace : WordTrace (prefixWord ++ tailWord_2704720) baseStart_2704720 baseEnd_2704720 := by
    simpa [prefixWord, tailWord_2704720, baseEnd_2704720] using wordTrace_append hprefix tailTrace_2704720
  have hstable : (prefixWord ++ tailWord_2704720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704720).length < 2 ^ (prefixWord ++ tailWord_2704720).sum := by decide
  have hdescent : baseEnd_2704720 < baseStart_2704720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704723 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 8]
def baseStart_2704723 : Nat := 118140960795 + 2704723 * 2 ^ 59
def prefixEnd_2704723 : Nat := 4983230072969 + 3 ^ 40 * 2704723 * 2
def baseEnd_2704723 : Nat := 154313659585636276947079

theorem tailTrace_2704723 : CollatzResearch.WordTrace tailWord_2704723 prefixEnd_2704723 154313659585636276947079 := by
  unfold tailWord_2704723
  simp only [CollatzResearch.WordTrace]
  refine ⟨98649352180257975757390823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65766234786838650504927215 98649352180257975757390823)
  ·
    refine ⟨147974028270386963636086235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98649352180257975757390823 147974028270386963636086235)
    ·
      refine ⟨221961042405580445454129353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147974028270386963636086235 221961042405580445454129353)
      ·
        refine ⟨166470781804185334090597015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 221961042405580445454129353 166470781804185334090597015)
        ·
          refine ⟨249706172706278001135895523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166470781804185334090597015 249706172706278001135895523)
          ·
            refine ⟨374559259059417001703843285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249706172706278001135895523 374559259059417001703843285)
            ·
              refine ⟨8778732634205085977433827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 374559259059417001703843285 8778732634205085977433827)
              ·
                refine ⟨13168098951307628966150741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8778732634205085977433827 13168098951307628966150741)
                ·
                  refine ⟨154313659585636276947079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13168098951307628966150741 154313659585636276947079)
                  ·
                    rfl

theorem cell23_2704723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 8].length) (baseStart_2704723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704723 prefixEnd_2704723 := by exact prefixLift 2704723
  have htrace : WordTrace (prefixWord ++ tailWord_2704723) baseStart_2704723 baseEnd_2704723 := by
    simpa [prefixWord, tailWord_2704723, baseEnd_2704723] using wordTrace_append hprefix tailTrace_2704723
  have hstable : (prefixWord ++ tailWord_2704723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704723).length < 2 ^ (prefixWord ++ tailWord_2704723).sum := by decide
  have hdescent : baseEnd_2704723 < baseStart_2704723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704727 : List Nat := [1, 1, 3, 2, 3, 3, 2, 1, 3, 4]
def baseStart_2704727 : Nat := 118140960795 + 2704727 * 2 ^ 59
def prefixEnd_2704727 : Nat := 4983230072969 + 3 ^ 40 * 2704727 * 2
def baseEnd_2704727 : Nat := 462941663397781492291231

theorem tailTrace_2704727 : CollatzResearch.WordTrace tailWord_2704727 prefixEnd_2704727 462941663397781492291231 := by
  unfold tailWord_2704727
  simp only [CollatzResearch.WordTrace]
  refine ⟨98649498072243484440536435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65766332048162322960357623 98649498072243484440536435)
  ·
    refine ⟨147974247108365226660804653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98649498072243484440536435 147974247108365226660804653)
    ·
      refine ⟨55490342665636959997801745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 147974247108365226660804653 55490342665636959997801745)
      ·
        refine ⟨41617756999227719998351309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55490342665636959997801745 41617756999227719998351309)
        ·
          refine ⟨15606658874710394999381741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41617756999227719998351309 15606658874710394999381741)
          ·
            refine ⟨5852497078016398124768153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15606658874710394999381741 5852497078016398124768153)
            ·
              refine ⟨4389372808512298593576115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5852497078016398124768153 4389372808512298593576115)
              ·
                refine ⟨6584059212768447890364173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389372808512298593576115 6584059212768447890364173)
                ·
                  refine ⟨2469022204788167958886565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6584059212768447890364173 2469022204788167958886565)
                  ·
                    refine ⟨462941663397781492291231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469022204788167958886565 462941663397781492291231)
                    ·
                      rfl

theorem cell23_2704727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_2704727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704727 prefixEnd_2704727 := by exact prefixLift 2704727
  have htrace : WordTrace (prefixWord ++ tailWord_2704727) baseStart_2704727 baseEnd_2704727 := by
    simpa [prefixWord, tailWord_2704727, baseEnd_2704727] using wordTrace_append hprefix tailTrace_2704727
  have hstable : (prefixWord ++ tailWord_2704727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704727).length < 2 ^ (prefixWord ++ tailWord_2704727).sum := by decide
  have hdescent : baseEnd_2704727 < baseStart_2704727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704800 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_2704800 : Nat := 118140960795 + 2704800 * 2 ^ 59
def prefixEnd_2704800 : Nat := 4983230072969 + 3 ^ 40 * 2704800 * 2
def baseEnd_2704800 : Nat := 462954158093707563753619

theorem tailTrace_2704800 : CollatzResearch.WordTrace tailWord_2704800 prefixEnd_2704800 462954158093707563753619 := by
  unfold tailWord_2704800
  simp only [CollatzResearch.WordTrace]
  refine ⟨49326080300489508953971927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65768107067319345271962569 49326080300489508953971927)
  ·
    refine ⟨73989120450734263430957891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49326080300489508953971927 73989120450734263430957891)
    ·
      refine ⟨110983680676101395146436837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73989120450734263430957891 110983680676101395146436837)
      ·
        refine ⟨20809440126769011589956907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110983680676101395146436837 20809440126769011589956907)
        ·
          refine ⟨31214160190153517384935361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20809440126769011589956907 31214160190153517384935361)
          ·
            refine ⟨23410620142615138038701521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31214160190153517384935361 23410620142615138038701521)
            ·
              refine ⟨17557965106961353529026141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23410620142615138038701521 17557965106961353529026141)
              ·
                refine ⟨6584236915110507573384803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17557965106961353529026141 6584236915110507573384803)
                ·
                  refine ⟨9876355372665761360077205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6584236915110507573384803 9876355372665761360077205)
                  ·
                    refine ⟨462954158093707563753619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9876355372665761360077205 462954158093707563753619)
                    ·
                      rfl

theorem cell23_2704800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_2704800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704800 prefixEnd_2704800 := by exact prefixLift 2704800
  have htrace : WordTrace (prefixWord ++ tailWord_2704800) baseStart_2704800 baseEnd_2704800 := by
    simpa [prefixWord, tailWord_2704800, baseEnd_2704800] using wordTrace_append hprefix tailTrace_2704800
  have hstable : (prefixWord ++ tailWord_2704800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704800).length < 2 ^ (prefixWord ++ tailWord_2704800).sum := by decide
  have hdescent : baseEnd_2704800 < baseStart_2704800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704807 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_2704807 : Nat := 118140960795 + 2704807 * 2 ^ 59
def prefixEnd_2704807 : Nat := 4983230072969 + 3 ^ 40 * 2704807 * 2
def baseEnd_2704807 : Nat := 1388866068645704163873325

theorem tailTrace_2704807 : CollatzResearch.WordTrace tailWord_2704807 prefixEnd_2704807 1388866068645704163873325 := by
  unfold tailWord_2704807
  simp only [CollatzResearch.WordTrace]
  refine ⟨98652415911953658103448675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65768277274635772068965783 98652415911953658103448675)
  ·
    refine ⟨147978623867930487155173013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98652415911953658103448675 147978623867930487155173013)
    ·
      refine ⟨6936497993809241585398735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 147978623867930487155173013 6936497993809241585398735)
      ·
        refine ⟨10404746990713862378098103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936497993809241585398735 10404746990713862378098103)
        ·
          refine ⟨15607120486070793567147155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404746990713862378098103 15607120486070793567147155)
          ·
            refine ⟨23410680729106190350720733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15607120486070793567147155 23410680729106190350720733)
            ·
              refine ⟨8779005273414821381520275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23410680729106190350720733 8779005273414821381520275)
              ·
                refine ⟨13168507910122232072280413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779005273414821381520275 13168507910122232072280413)
                ·
                  refine ⟨4938190466295837027105155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13168507910122232072280413 4938190466295837027105155)
                  ·
                    refine ⟨7407285699443755540657733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4938190466295837027105155 7407285699443755540657733)
                    ·
                      refine ⟨1388866068645704163873325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7407285699443755540657733 1388866068645704163873325)
                      ·
                        rfl

theorem cell23_2704807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_2704807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704807 prefixEnd_2704807 := by exact prefixLift 2704807
  have htrace : WordTrace (prefixWord ++ tailWord_2704807) baseStart_2704807 baseEnd_2704807 := by
    simpa [prefixWord, tailWord_2704807, baseEnd_2704807] using wordTrace_append hprefix tailTrace_2704807
  have hstable : (prefixWord ++ tailWord_2704807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704807).length < 2 ^ (prefixWord ++ tailWord_2704807).sum := by decide
  have hdescent : baseEnd_2704807 < baseStart_2704807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704854 : List Nat := [5, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2704854 : Nat := 118140960795 + 2704854 * 2 ^ 59
def prefixEnd_2704854 : Nat := 4983230072969 + 3 ^ 40 * 2704854 * 2
def baseEnd_2704854 : Nat := 1388890202236465479985609

theorem tailTrace_2704854 : CollatzResearch.WordTrace tailWord_2704854 prefixEnd_2704854 1388890202236465479985609 := by
  unfold tailWord_2704854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165883133923961570650601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65769420095188923420273077 6165883133923961570650601)
  ·
    refine ⟨4624412350442971177987951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6165883133923961570650601 4624412350442971177987951)
    ·
      refine ⟨6936618525664456766981927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624412350442971177987951 6936618525664456766981927)
      ·
        refine ⟨10404927788496685150472891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936618525664456766981927 10404927788496685150472891)
        ·
          refine ⟨15607391682745027725709337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10404927788496685150472891 15607391682745027725709337)
          ·
            refine ⟨11705543762058770794282003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15607391682745027725709337 11705543762058770794282003)
            ·
              refine ⟨17558315643088156191423005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705543762058770794282003 17558315643088156191423005)
              ·
                refine ⟨6584368366158058571783627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17558315643088156191423005 6584368366158058571783627)
                ·
                  refine ⟨9876552549237087857675441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6584368366158058571783627 9876552549237087857675441)
                  ·
                    refine ⟨7407414411927815893256581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9876552549237087857675441 7407414411927815893256581)
                    ·
                      refine ⟨1388890202236465479985609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7407414411927815893256581 1388890202236465479985609)
                      ·
                        rfl

theorem cell23_2704854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2704854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704854 prefixEnd_2704854 := by exact prefixLift 2704854
  have htrace : WordTrace (prefixWord ++ tailWord_2704854) baseStart_2704854 baseEnd_2704854 := by
    simpa [prefixWord, tailWord_2704854, baseEnd_2704854] using wordTrace_append hprefix tailTrace_2704854
  have hstable : (prefixWord ++ tailWord_2704854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704854).length < 2 ^ (prefixWord ++ tailWord_2704854).sum := by decide
  have hdescent : baseEnd_2704854 < baseStart_2704854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704857 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_2704857 : Nat := 118140960795 + 2704857 * 2 ^ 59
def prefixEnd_2704857 : Nat := 4983230072969 + 3 ^ 40 * 2704857 * 2
def baseEnd_2704857 : Nat := 1388891742678428968248095

theorem tailTrace_2704857 : CollatzResearch.WordTrace tailWord_2704857 prefixEnd_2704857 1388891742678428968248095 := by
  unfold tailWord_2704857
  simp only [CollatzResearch.WordTrace]
  refine ⟨98654239561772516642768825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65769493041181677761845883 98654239561772516642768825)
  ·
    refine ⟨73990679671329387482076619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98654239561772516642768825 73990679671329387482076619)
    ·
      refine ⟨110986019506994081223114929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73990679671329387482076619 110986019506994081223114929)
      ·
        refine ⟨83239514630245560917336197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110986019506994081223114929 83239514630245560917336197)
        ·
          refine ⟨15607408993171042672000537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83239514630245560917336197 15607408993171042672000537)
          ·
            refine ⟨11705556744878282004000403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15607408993171042672000537 11705556744878282004000403)
            ·
              refine ⟨17558335117317423006000605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11705556744878282004000403 17558335117317423006000605)
              ·
                refine ⟨6584375668994033627250227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17558335117317423006000605 6584375668994033627250227)
                ·
                  refine ⟨9876563503491050440875341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6584375668994033627250227 9876563503491050440875341)
                  ·
                    refine ⟨3703711313809143915328253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9876563503491050440875341 3703711313809143915328253)
                    ·
                      refine ⟨1388891742678428968248095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703711313809143915328253 1388891742678428968248095)
                      ·
                        rfl

theorem cell23_2704857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_2704857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704857 prefixEnd_2704857 := by exact prefixLift 2704857
  have htrace : WordTrace (prefixWord ++ tailWord_2704857) baseStart_2704857 baseEnd_2704857 := by
    simpa [prefixWord, tailWord_2704857, baseEnd_2704857] using wordTrace_append hprefix tailTrace_2704857
  have hstable : (prefixWord ++ tailWord_2704857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704857).length < 2 ^ (prefixWord ++ tailWord_2704857).sum := by decide
  have hdescent : baseEnd_2704857 < baseStart_2704857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704890 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_2704890 : Nat := 118140960795 + 2704890 * 2 ^ 59
def prefixEnd_2704890 : Nat := 4983230072969 + 3 ^ 40 * 2704890 * 2
def baseEnd_2704890 : Nat := 462969562513342446378481

theorem tailTrace_2704890 : CollatzResearch.WordTrace tailWord_2704890 prefixEnd_2704890 462969562513342446378481 := by
  unfold tailWord_2704890
  simp only [CollatzResearch.WordTrace]
  refine ⟨24663860792663240819680031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65770295447101975519146749 24663860792663240819680031)
  ·
    refine ⟨36995791188994861229520047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24663860792663240819680031 36995791188994861229520047)
    ·
      refine ⟨55493686783492291844280071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36995791188994861229520047 55493686783492291844280071)
      ·
        refine ⟨83240530175238437766420107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55493686783492291844280071 83240530175238437766420107)
        ·
          refine ⟨124860795262857656649630161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83240530175238437766420107 124860795262857656649630161)
          ·
            refine ⟨93645596447143242487222621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124860795262857656649630161 93645596447143242487222621)
            ·
              refine ⟨35117098667678715932708483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93645596447143242487222621 35117098667678715932708483)
              ·
                refine ⟨52675648001518073899062725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35117098667678715932708483 52675648001518073899062725)
                ·
                  refine ⟨9876684000284638856074261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52675648001518073899062725 9876684000284638856074261)
                  ·
                    refine ⟨462969562513342446378481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9876684000284638856074261 462969562513342446378481)
                    ·
                      rfl

theorem cell23_2704890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_2704890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704890 prefixEnd_2704890 := by exact prefixLift 2704890
  have htrace : WordTrace (prefixWord ++ tailWord_2704890) baseStart_2704890 baseEnd_2704890 := by
    simpa [prefixWord, tailWord_2704890, baseEnd_2704890] using wordTrace_append hprefix tailTrace_2704890
  have hstable : (prefixWord ++ tailWord_2704890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704890).length < 2 ^ (prefixWord ++ tailWord_2704890).sum := by decide
  have hdescent : baseEnd_2704890 < baseStart_2704890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704902 : List Nat := [6, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_2704902 : Nat := 118140960795 + 2704902 * 2 ^ 59
def prefixEnd_2704902 : Nat := 4983230072969 + 3 ^ 40 * 2704902 * 2
def baseEnd_2704902 : Nat := 462971616435960430728463

theorem tailTrace_2704902 : CollatzResearch.WordTrace tailWord_2704902 prefixEnd_2704902 462971616435960430728463 := by
  unfold tailWord_2704902
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082996276456546541504905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65770587231072992885437973 3082996276456546541504905)
  ·
    refine ⟨2312247207342409906128679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3082996276456546541504905 2312247207342409906128679)
    ·
      refine ⟨3468370811013614859193019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312247207342409906128679 3468370811013614859193019)
      ·
        refine ⟨5202556216520422288789529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468370811013614859193019 5202556216520422288789529)
        ·
          refine ⟨3901917162390316716592147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5202556216520422288789529 3901917162390316716592147)
          ·
            refine ⟨5852875743585475074888221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901917162390316716592147 5852875743585475074888221)
            ·
              refine ⟨2194828403844553153083083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5852875743585475074888221 2194828403844553153083083)
              ·
                refine ⟨3292242605766829729624625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194828403844553153083083 3292242605766829729624625)
                ·
                  refine ⟨2469181954325122297218469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3292242605766829729624625 2469181954325122297218469)
                  ·
                    refine ⟨462971616435960430728463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469181954325122297218469 462971616435960430728463)
                    ·
                      rfl

theorem cell23_2704902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_2704902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704902 prefixEnd_2704902 := by exact prefixLift 2704902
  have htrace : WordTrace (prefixWord ++ tailWord_2704902) baseStart_2704902 baseEnd_2704902 := by
    simpa [prefixWord, tailWord_2704902, baseEnd_2704902] using wordTrace_append hprefix tailTrace_2704902
  have hstable : (prefixWord ++ tailWord_2704902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704902).length < 2 ^ (prefixWord ++ tailWord_2704902).sum := by decide
  have hdescent : baseEnd_2704902 < baseStart_2704902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704908 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_2704908 : Nat := 118140960795 + 2704908 * 2 ^ 59
def prefixEnd_2704908 : Nat := 4983230072969 + 3 ^ 40 * 2704908 * 2
def baseEnd_2704908 : Nat := 1388917930191808268710361

theorem tailTrace_2704908 : CollatzResearch.WordTrace tailWord_2704908 prefixEnd_2704908 1388917930191808268710361 := by
  unfold tailWord_2704908
  simp only [CollatzResearch.WordTrace]
  refine ⟨49328049842293876176437689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65770733123058501568583585 49328049842293876176437689)
  ·
    refine ⟨36996037381720407132328267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49328049842293876176437689 36996037381720407132328267)
    ·
      refine ⟨55494056072580610698492401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36996037381720407132328267 55494056072580610698492401)
      ·
        refine ⟨41620542054435458023869301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55494056072580610698492401 41620542054435458023869301)
        ·
          refine ⟨3901925817603324189737747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41620542054435458023869301 3901925817603324189737747)
          ·
            refine ⟨5852888726404986284606621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901925817603324189737747 5852888726404986284606621)
            ·
              refine ⟨2194833272401869856727483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5852888726404986284606621 2194833272401869856727483)
              ·
                refine ⟨3292249908602804785091225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194833272401869856727483 3292249908602804785091225)
                ·
                  refine ⟨2469187431452103588818419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3292249908602804785091225 2469187431452103588818419)
                  ·
                    refine ⟨3703781147178155383227629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469187431452103588818419 3703781147178155383227629)
                    ·
                      refine ⟨1388917930191808268710361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703781147178155383227629 1388917930191808268710361)
                      ·
                        rfl

theorem cell23_2704908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_2704908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704908 prefixEnd_2704908 := by exact prefixLift 2704908
  have htrace : WordTrace (prefixWord ++ tailWord_2704908) baseStart_2704908 baseEnd_2704908 := by
    simpa [prefixWord, tailWord_2704908, baseEnd_2704908] using wordTrace_append hprefix tailTrace_2704908
  have hstable : (prefixWord ++ tailWord_2704908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704908).length < 2 ^ (prefixWord ++ tailWord_2704908).sum := by decide
  have hdescent : baseEnd_2704908 < baseStart_2704908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704926 : List Nat := [4, 3, 3, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2704926 : Nat := 118140960795 + 2704926 * 2 ^ 59
def prefixEnd_2704926 : Nat := 4983230072969 + 3 ^ 40 * 2704926 * 2
def baseEnd_2704926 : Nat := 1388927172843589198285279

theorem tailTrace_2704926 : CollatzResearch.WordTrace tailWord_2704926 prefixEnd_2704926 1388927172843589198285279 := by
  unfold tailWord_2704926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332094524815317678378829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65771170799015027618020421 12332094524815317678378829)
  ·
    refine ⟨4624535446805744129392061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12332094524815317678378829 4624535446805744129392061)
    ·
      refine ⟨1734200792552154048522023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4624535446805744129392061 1734200792552154048522023)
      ·
        refine ⟨2601301188828231072783035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734200792552154048522023 2601301188828231072783035)
        ·
          refine ⟨3901951783242346609174553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601301188828231072783035 3901951783242346609174553)
          ·
            refine ⟨2926463837431759956880915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901951783242346609174553 2926463837431759956880915)
            ·
              refine ⟨4389695756147639935321373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926463837431759956880915 4389695756147639935321373)
              ·
                refine ⟨1646135908555364975745515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389695756147639935321373 1646135908555364975745515)
                ·
                  refine ⟨2469203862833047463618273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646135908555364975745515 2469203862833047463618273)
                  ·
                    refine ⟨1851902897124785597713705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2469203862833047463618273 1851902897124785597713705)
                    ·
                      refine ⟨1388927172843589198285279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851902897124785597713705 1388927172843589198285279)
                      ·
                        rfl

theorem cell23_2704926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2704926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704926 prefixEnd_2704926 := by exact prefixLift 2704926
  have htrace : WordTrace (prefixWord ++ tailWord_2704926) baseStart_2704926 baseEnd_2704926 := by
    simpa [prefixWord, tailWord_2704926, baseEnd_2704926] using wordTrace_append hprefix tailTrace_2704926
  have hstable : (prefixWord ++ tailWord_2704926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704926).length < 2 ^ (prefixWord ++ tailWord_2704926).sum := by decide
  have hdescent : baseEnd_2704926 < baseStart_2704926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2704940 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2704940 : Nat := 118140960795 + 2704940 * 2 ^ 59
def prefixEnd_2704940 : Nat := 4983230072969 + 3 ^ 40 * 2704940 * 2
def baseEnd_2704940 : Nat := 1388934361572752143510213

theorem tailTrace_2704940 : CollatzResearch.WordTrace tailWord_2704940 prefixEnd_2704940 1388934361572752143510213 := by
  unfold tailWord_2704940
  simp only [CollatzResearch.WordTrace]
  refine ⟨49328633410235910909020137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65771511213647881212026849 49328633410235910909020137)
  ·
    refine ⟨36996475057676933181765103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49328633410235910909020137 36996475057676933181765103)
    ·
      refine ⟨55494712586515399772647655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36996475057676933181765103 55494712586515399772647655)
      ·
        refine ⟨83242068879773099658971483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55494712586515399772647655 83242068879773099658971483)
        ·
          refine ⟨124863103319659649488457225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83242068879773099658971483 124863103319659649488457225)
          ·
            refine ⟨93647327489744737116342919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124863103319659649488457225 93647327489744737116342919)
            ·
              refine ⟨140470991234617105674514379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93647327489744737116342919 140470991234617105674514379)
              ·
                refine ⟨210706486851925658511771569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140470991234617105674514379 210706486851925658511771569)
                ·
                  refine ⟨158029865138944243883828677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210706486851925658511771569 158029865138944243883828677)
                  ·
                    refine ⟨29630599713552045728217877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158029865138944243883828677 29630599713552045728217877)
                    ·
                      refine ⟨1388934361572752143510213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29630599713552045728217877 1388934361572752143510213)
                      ·
                        rfl

theorem cell23_2704940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2704940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2704940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2704940 prefixEnd_2704940 := by exact prefixLift 2704940
  have htrace : WordTrace (prefixWord ++ tailWord_2704940) baseStart_2704940 baseEnd_2704940 := by
    simpa [prefixWord, tailWord_2704940, baseEnd_2704940] using wordTrace_append hprefix tailTrace_2704940
  have hstable : (prefixWord ++ tailWord_2704940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2704940).length < 2 ^ (prefixWord ++ tailWord_2704940).sum := by decide
  have hdescent : baseEnd_2704940 < baseStart_2704940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2704940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705004 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_2705004 : Nat := 118140960795 + 2705004 * 2 ^ 59
def prefixEnd_2705004 : Nat := 4983230072969 + 3 ^ 40 * 2705004 * 2
def baseEnd_2705004 : Nat := 1388967224334639893109919

theorem tailTrace_2705004 : CollatzResearch.WordTrace tailWord_2705004 prefixEnd_2705004 1388967224334639893109919 := by
  unfold tailWord_2705004
  simp only [CollatzResearch.WordTrace]
  refine ⟨49329800546119980374185033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65773067394826640498913377 49329800546119980374185033)
  ·
    refine ⟨36997350409589985280638775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49329800546119980374185033 36997350409589985280638775)
    ·
      refine ⟨55496025614384977920958163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36997350409589985280638775 55496025614384977920958163)
      ·
        refine ⟨83244038421577466881437245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55496025614384977920958163 83244038421577466881437245)
        ·
          refine ⟨31216514408091550080538967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83244038421577466881437245 31216514408091550080538967)
          ·
            refine ⟨46824771612137325120808451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31216514408091550080538967 46824771612137325120808451)
            ·
              refine ⟨70237157418205987681212677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46824771612137325120808451 70237157418205987681212677)
              ·
                refine ⟨13169467015913622690227377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70237157418205987681212677 13169467015913622690227377)
                ·
                  refine ⟨9877100261935217017670533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13169467015913622690227377 9877100261935217017670533)
                  ·
                    refine ⟨1851956299112853190813225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9877100261935217017670533 1851956299112853190813225)
                    ·
                      refine ⟨1388967224334639893109919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851956299112853190813225 1388967224334639893109919)
                      ·
                        rfl

theorem cell23_2705004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_2705004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705004 prefixEnd_2705004 := by exact prefixLift 2705004
  have htrace : WordTrace (prefixWord ++ tailWord_2705004) baseStart_2705004 baseEnd_2705004 := by
    simpa [prefixWord, tailWord_2705004, baseEnd_2705004] using wordTrace_append hprefix tailTrace_2705004
  have hstable : (prefixWord ++ tailWord_2705004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705004).length < 2 ^ (prefixWord ++ tailWord_2705004).sum := by decide
  have hdescent : baseEnd_2705004 < baseStart_2705004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705005 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 5]
def baseStart_2705005 : Nat := 118140960795 + 2705005 * 2 ^ 59
def prefixEnd_2705005 : Nat := 4983230072969 + 3 ^ 40 * 2705005 * 2
def baseEnd_2705005 : Nat := 154329748646143821021935

theorem tailTrace_2705005 : CollatzResearch.WordTrace tailWord_2705005 prefixEnd_2705005 154329748646143821021935 := by
  unfold tailWord_2705005
  simp only [CollatzResearch.WordTrace]
  refine ⟨98659637565236337919156469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65773091710157558612770979 98659637565236337919156469)
  ·
    refine ⟨9249341021740906679920919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98659637565236337919156469 9249341021740906679920919)
    ·
      refine ⟨13874011532611360019881379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9249341021740906679920919 13874011532611360019881379)
      ·
        refine ⟨20811017298917040029822069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13874011532611360019881379 20811017298917040029822069)
        ·
          refine ⟨1951032871773472502795819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20811017298917040029822069 1951032871773472502795819)
          ·
            refine ⟨2926549307660208754193729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951032871773472502795819 2926549307660208754193729)
            ·
              refine ⟨2194911980745156565645297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926549307660208754193729 2194911980745156565645297)
              ·
                refine ⟨1646183985558867424233973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194911980745156565645297 1646183985558867424233973)
                ·
                  refine ⟨154329748646143821021935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1646183985558867424233973 154329748646143821021935)
                  ·
                    rfl

theorem cell23_2705005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_2705005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705005 prefixEnd_2705005 := by exact prefixLift 2705005
  have htrace : WordTrace (prefixWord ++ tailWord_2705005) baseStart_2705005 baseEnd_2705005 := by
    simpa [prefixWord, tailWord_2705005, baseEnd_2705005] using wordTrace_append hprefix tailTrace_2705005
  have hstable : (prefixWord ++ tailWord_2705005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705005).length < 2 ^ (prefixWord ++ tailWord_2705005).sum := by decide
  have hdescent : baseEnd_2705005 < baseStart_2705005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705007 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_2705007 : Nat := 118140960795 + 2705007 * 2 ^ 59
def prefixEnd_2705007 : Nat := 4983230072969 + 3 ^ 40 * 2705007 * 2
def baseEnd_2705007 : Nat := 1388968764776603381372405

theorem tailTrace_2705007 : CollatzResearch.WordTrace tailWord_2705007 prefixEnd_2705007 1388968764776603381372405 := by
  unfold tailWord_2705007
  simp only [CollatzResearch.WordTrace]
  refine ⟨98659710511229092260729275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65773140340819394840486183 98659710511229092260729275)
  ·
    refine ⟨147989565766843638391093913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98659710511229092260729275 147989565766843638391093913)
    ·
      refine ⟨110992174325132728793320435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147989565766843638391093913 110992174325132728793320435)
      ·
        refine ⟨166488261487699093189980653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110992174325132728793320435 166488261487699093189980653)
        ·
          refine ⟨62433098057887159946242745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166488261487699093189980653 62433098057887159946242745)
          ·
            refine ⟨46824823543415369959682059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62433098057887159946242745 46824823543415369959682059)
            ·
              refine ⟨70237235315123054939523089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46824823543415369959682059 70237235315123054939523089)
              ·
                refine ⟨52677926486342291204642317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70237235315123054939523089 52677926486342291204642317)
                ·
                  refine ⟨19754222432378359201740869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52677926486342291204642317 19754222432378359201740869)
                  ·
                    refine ⟨3703916706070942350326413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19754222432378359201740869 3703916706070942350326413)
                    ·
                      refine ⟨1388968764776603381372405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3703916706070942350326413 1388968764776603381372405)
                      ·
                        rfl

theorem cell23_2705007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_2705007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705007 prefixEnd_2705007 := by exact prefixLift 2705007
  have htrace : WordTrace (prefixWord ++ tailWord_2705007) baseStart_2705007 baseEnd_2705007 := by
    simpa [prefixWord, tailWord_2705007, baseEnd_2705007] using wordTrace_append hprefix tailTrace_2705007
  have hstable : (prefixWord ++ tailWord_2705007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705007).length < 2 ^ (prefixWord ++ tailWord_2705007).sum := by decide
  have hdescent : baseEnd_2705007 < baseStart_2705007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705021 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_2705021 : Nat := 118140960795 + 2705021 * 2 ^ 59
def prefixEnd_2705021 : Nat := 4983230072969 + 3 ^ 40 * 2705021 * 2
def baseEnd_2705021 : Nat := 1388975953505766326597341

theorem tailTrace_2705021 : CollatzResearch.WordTrace tailWord_2705021 prefixEnd_2705021 1388975953505766326597341 := by
  unfold tailWord_2705021
  simp only [CollatzResearch.WordTrace]
  refine ⟨98660221133178372651738917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65773480755452248434492611 98660221133178372651738917)
  ·
    refine ⟨18498791462470944872201047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98660221133178372651738917 18498791462470944872201047)
    ·
      refine ⟨27748187193706417308301571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18498791462470944872201047 27748187193706417308301571)
      ·
        refine ⟨41622280790559625962452357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27748187193706417308301571 41622280790559625962452357)
        ·
          refine ⟨7804177648229929867959817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41622280790559625962452357 7804177648229929867959817)
          ·
            refine ⟨5853133236172447400969863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804177648229929867959817 5853133236172447400969863)
            ·
              refine ⟨8779699854258671101454795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853133236172447400969863 8779699854258671101454795)
              ·
                refine ⟨13169549781388006652182193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8779699854258671101454795 13169549781388006652182193)
                ·
                  refine ⟨9877162336041004989136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13169549781388006652182193 9877162336041004989136645)
                  ·
                    refine ⟨1851967938007688435463121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9877162336041004989136645 1851967938007688435463121)
                    ·
                      refine ⟨1388975953505766326597341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1851967938007688435463121 1388975953505766326597341)
                      ·
                        rfl

theorem cell23_2705021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_2705021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705021 prefixEnd_2705021 := by exact prefixLift 2705021
  have htrace : WordTrace (prefixWord ++ tailWord_2705021) baseStart_2705021 baseEnd_2705021 := by
    simpa [prefixWord, tailWord_2705021, baseEnd_2705021] using wordTrace_append hprefix tailTrace_2705021
  have hstable : (prefixWord ++ tailWord_2705021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705021).length < 2 ^ (prefixWord ++ tailWord_2705021).sum := by decide
  have hdescent : baseEnd_2705021 < baseStart_2705021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705048 : List Nat := [2, 1, 2, 4, 1, 3, 2, 3, 1, 4]
def baseStart_2705048 : Nat := 118140960795 + 2705048 * 2 ^ 59
def prefixEnd_2705048 : Nat := 4983230072969 + 3 ^ 40 * 2705048 * 2
def baseEnd_2705048 : Nat := 462996605827812573653239

theorem tailTrace_2705048 : CollatzResearch.WordTrace tailWord_2705048 prefixEnd_2705048 462996605827812573653239 := by
  unfold tailWord_2705048
  simp only [CollatzResearch.WordTrace]
  refine ⟨49330602952040278131485899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65774137269387037508647865 49330602952040278131485899)
  ·
    refine ⟨73995904428060417197228849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49330602952040278131485899 73995904428060417197228849)
    ·
      refine ⟨55496928321045312897921637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73995904428060417197228849 55496928321045312897921637)
      ·
        refine ⟨10405674060195996168360307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55496928321045312897921637 10405674060195996168360307)
        ·
          refine ⟨15608511090293994252540461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10405674060195996168360307 15608511090293994252540461)
          ·
            refine ⟨5853191658860247844702673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15608511090293994252540461 5853191658860247844702673)
            ·
              refine ⟨4389893744145185883527005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853191658860247844702673 4389893744145185883527005)
              ·
                refine ⟨1646210154054444706322627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389893744145185883527005 1646210154054444706322627)
                ·
                  refine ⟨2469315231081667059483941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646210154054444706322627 2469315231081667059483941)
                  ·
                    refine ⟨462996605827812573653239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469315231081667059483941 462996605827812573653239)
                    ·
                      rfl

theorem cell23_2705048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_2705048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705048 prefixEnd_2705048 := by exact prefixLift 2705048
  have htrace : WordTrace (prefixWord ++ tailWord_2705048) baseStart_2705048 baseEnd_2705048 := by
    simpa [prefixWord, tailWord_2705048, baseEnd_2705048] using wordTrace_append hprefix tailTrace_2705048
  have hstable : (prefixWord ++ tailWord_2705048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705048).length < 2 ^ (prefixWord ++ tailWord_2705048).sum := by decide
  have hdescent : baseEnd_2705048 < baseStart_2705048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705071 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 3]
def baseStart_2705071 : Nat := 118140960795 + 2705071 * 2 ^ 59
def prefixEnd_2705071 : Nat := 4983230072969 + 3 ^ 40 * 2705071 * 2
def baseEnd_2705071 : Nat := 1389001627538491130972111

theorem tailTrace_2705071 : CollatzResearch.WordTrace tailWord_2705071 prefixEnd_2705071 1389001627538491130972111 := by
  unfold tailWord_2705071
  simp only [CollatzResearch.WordTrace]
  refine ⟨98662044782997231191059067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65774696521998154127372711 98662044782997231191059067)
  ·
    refine ⟨147993067174495846786588601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98662044782997231191059067 147993067174495846786588601)
    ·
      refine ⟨110994800380871885089941451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 147993067174495846786588601 110994800380871885089941451)
      ·
        refine ⟨166492200571307827634912177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110994800380871885089941451 166492200571307827634912177)
        ·
          refine ⟨124869150428480870726184133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166492200571307827634912177 124869150428480870726184133)
          ·
            refine ⟨23412965705340163261159525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124869150428480870726184133 23412965705340163261159525)
            ·
              refine ⟨4389931069751280611467411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23412965705340163261159525 4389931069751280611467411)
              ·
                refine ⟨6584896604626920917201117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389931069751280611467411 6584896604626920917201117)
                ·
                  refine ⟨2469336226735095343950419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6584896604626920917201117 2469336226735095343950419)
                  ·
                    refine ⟨3704004340102643015925629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469336226735095343950419 3704004340102643015925629)
                    ·
                      refine ⟨1389001627538491130972111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704004340102643015925629 1389001627538491130972111)
                      ·
                        rfl

theorem cell23_2705071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_2705071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705071 prefixEnd_2705071 := by exact prefixLift 2705071
  have htrace : WordTrace (prefixWord ++ tailWord_2705071) baseStart_2705071 baseEnd_2705071 := by
    simpa [prefixWord, tailWord_2705071, baseEnd_2705071] using wordTrace_append hprefix tailTrace_2705071
  have hstable : (prefixWord ++ tailWord_2705071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705071).length < 2 ^ (prefixWord ++ tailWord_2705071).sum := by decide
  have hdescent : baseEnd_2705071 < baseStart_2705071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705105 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 1, 1, 3]
def baseStart_2705105 : Nat := 118140960795 + 2705105 * 2 ^ 59
def prefixEnd_2705105 : Nat := 4983230072969 + 3 ^ 40 * 2705105 * 2
def baseEnd_2705105 : Nat := 1389019085880743997946955

theorem tailTrace_2705105 : CollatzResearch.WordTrace tailWord_2705105 prefixEnd_2705105 1389019085880743997946955 := by
  unfold tailWord_2705105
  simp only [CollatzResearch.WordTrace]
  refine ⟨98663284864874054997796769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65775523243249369998531179 98663284864874054997796769)
  ·
    refine ⟨73997463648655541248347577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98663284864874054997796769 73997463648655541248347577)
    ·
      refine ⟨55498097736491655936260683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73997463648655541248347577 55498097736491655936260683)
      ·
        refine ⟨83247146604737483904391025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55498097736491655936260683 83247146604737483904391025)
        ·
          refine ⟨62435359953553112928293269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83247146604737483904391025 62435359953553112928293269)
          ·
            refine ⟨2926657497822802168513747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62435359953553112928293269 2926657497822802168513747)
            ·
              refine ⟨4389986246734203252770621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926657497822802168513747 4389986246734203252770621)
              ·
                refine ⟨1646244842525326219788983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389986246734203252770621 1646244842525326219788983)
                ·
                  refine ⟨2469367263787989329683475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646244842525326219788983 2469367263787989329683475)
                  ·
                    refine ⟨3704050895681983994525213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469367263787989329683475 3704050895681983994525213)
                    ·
                      refine ⟨1389019085880743997946955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704050895681983994525213 1389019085880743997946955)
                      ·
                        rfl

theorem cell23_2705105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_2705105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705105 prefixEnd_2705105 := by exact prefixLift 2705105
  have htrace : WordTrace (prefixWord ++ tailWord_2705105) baseStart_2705105 baseEnd_2705105 := by
    simpa [prefixWord, tailWord_2705105, baseEnd_2705105] using wordTrace_append hprefix tailTrace_2705105
  have hstable : (prefixWord ++ tailWord_2705105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705105).length < 2 ^ (prefixWord ++ tailWord_2705105).sum := by decide
  have hdescent : baseEnd_2705105 < baseStart_2705105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705114 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2705114 : Nat := 118140960795 + 2705114 * 2 ^ 59
def prefixEnd_2705114 : Nat := 4983230072969 + 3 ^ 40 * 2705114 * 2
def baseEnd_2705114 : Nat := 1389023707206634462734413

theorem tailTrace_2705114 : CollatzResearch.WordTrace tailWord_2705114 prefixEnd_2705114 1389023707206634462734413 := by
  unfold tailWord_2705114
  simp only [CollatzResearch.WordTrace]
  refine ⟨24665903280460362383718599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65775742081227633023249597 24665903280460362383718599)
  ·
    refine ⟨36998854920690543575577899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24665903280460362383718599 36998854920690543575577899)
    ·
      refine ⟨55498282381035815363366849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36998854920690543575577899 55498282381035815363366849)
      ·
        refine ⟨41623711785776861522525137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55498282381035815363366849 41623711785776861522525137)
        ·
          refine ⟨31217783839332646141893853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41623711785776861522525137 31217783839332646141893853)
          ·
            refine ⟨11706668939749742303210195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31217783839332646141893853 11706668939749742303210195)
            ·
              refine ⟨17560003409624613454815293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11706668939749742303210195 17560003409624613454815293)
              ·
                refine ⟨6585001278609230045555735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17560003409624613454815293 6585001278609230045555735)
                ·
                  refine ⟨9877501917913845068333603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585001278609230045555735 9877501917913845068333603)
                  ·
                    refine ⟨14816252876870767602500405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9877501917913845068333603 14816252876870767602500405)
                    ·
                      refine ⟨1389023707206634462734413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14816252876870767602500405 1389023707206634462734413)
                      ·
                        rfl

theorem cell23_2705114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2705114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705114 prefixEnd_2705114 := by exact prefixLift 2705114
  have htrace : WordTrace (prefixWord ++ tailWord_2705114) baseStart_2705114 baseEnd_2705114 := by
    simpa [prefixWord, tailWord_2705114, baseEnd_2705114] using wordTrace_append hprefix tailTrace_2705114
  have hstable : (prefixWord ++ tailWord_2705114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705114).length < 2 ^ (prefixWord ++ tailWord_2705114).sum := by decide
  have hdescent : baseEnd_2705114 < baseStart_2705114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705134 : List Nat := [4, 1, 2, 1, 1, 2, 4, 8]
def baseStart_2705134 : Nat := 118140960795 + 2705134 * 2 ^ 59
def prefixEnd_2705134 : Nat := 4983230072969 + 3 ^ 40 * 2705134 * 2
def baseEnd_2705134 : Nat := 51445702845174977203123

theorem tailTrace_2705134 : CollatzResearch.WordTrace tailWord_2705134 prefixEnd_2705134 51445702845174977203123 := by
  unfold tailWord_2705134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12333042822721124118825307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65776228387845995300401637 12333042822721124118825307)
  ·
    refine ⟨18499564234081686178237961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12333042822721124118825307 18499564234081686178237961)
    ·
      refine ⟨13874673175561264633678471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18499564234081686178237961 13874673175561264633678471)
      ·
        refine ⟨20812009763341896950517707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13874673175561264633678471 20812009763341896950517707)
        ·
          refine ⟨31218014645012845425776561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20812009763341896950517707 31218014645012845425776561)
          ·
            refine ⟨23413510983759634069332421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31218014645012845425776561 23413510983759634069332421)
            ·
              refine ⟨4390033309454931387999829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23413510983759634069332421 4390033309454931387999829)
              ·
                refine ⟨51445702845174977203123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4390033309454931387999829 51445702845174977203123)
                ·
                  rfl

theorem cell23_2705134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_2705134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705134 prefixEnd_2705134 := by exact prefixLift 2705134
  have htrace : WordTrace (prefixWord ++ tailWord_2705134) baseStart_2705134 baseEnd_2705134 := by
    simpa [prefixWord, tailWord_2705134, baseEnd_2705134] using wordTrace_append hprefix tailTrace_2705134
  have hstable : (prefixWord ++ tailWord_2705134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705134).length < 2 ^ (prefixWord ++ tailWord_2705134).sum := by decide
  have hdescent : baseEnd_2705134 < baseStart_2705134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705147 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 4, 7]
def baseStart_2705147 : Nat := 118140960795 + 2705147 * 2 ^ 59
def prefixEnd_2705147 : Nat := 4983230072969 + 3 ^ 40 * 2705147 * 2
def baseEnd_2705147 : Nat := 463013550689410944540587

theorem tailTrace_2705147 : CollatzResearch.WordTrace tailWord_2705147 prefixEnd_2705147 463013550689410944540587 := by
  unfold tailWord_2705147
  simp only [CollatzResearch.WordTrace]
  refine ⟨98664816730721896170825695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65776544487147930780550463 98664816730721896170825695)
  ·
    refine ⟨147997225096082844256238543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98664816730721896170825695 147997225096082844256238543)
    ·
      refine ⟨221995837644124266384357815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147997225096082844256238543 221995837644124266384357815)
      ·
        refine ⟨332993756466186399576536723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221995837644124266384357815 332993756466186399576536723)
        ·
          refine ⟨499490634699279599364805085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332993756466186399576536723 499490634699279599364805085)
          ·
            refine ⟨187308988012229849761801907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499490634699279599364805085 187308988012229849761801907)
            ·
              refine ⟨280963482018344774642702861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187308988012229849761801907 280963482018344774642702861)
              ·
                refine ⟨105361305756879290491013573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280963482018344774642702861 105361305756879290491013573)
                ·
                  refine ⟨19755244829414866967065045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105361305756879290491013573 19755244829414866967065045)
                  ·
                    refine ⟨463013550689410944540587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19755244829414866967065045 463013550689410944540587)
                    ·
                      rfl

theorem cell23_2705147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_2705147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705147 prefixEnd_2705147 := by exact prefixLift 2705147
  have htrace : WordTrace (prefixWord ++ tailWord_2705147) baseStart_2705147 baseEnd_2705147 := by
    simpa [prefixWord, tailWord_2705147, baseEnd_2705147] using wordTrace_append hprefix tailTrace_2705147
  have hstable : (prefixWord ++ tailWord_2705147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705147).length < 2 ^ (prefixWord ++ tailWord_2705147).sum := by decide
  have hdescent : baseEnd_2705147 < baseStart_2705147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705178 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2705178 : Nat := 118140960795 + 2705178 * 2 ^ 59
def prefixEnd_2705178 : Nat := 4983230072969 + 3 ^ 40 * 2705178 * 2
def baseEnd_2705178 : Nat := 1389056569968522212334119

theorem tailTrace_2705178 : CollatzResearch.WordTrace tailWord_2705178 prefixEnd_2705178 1389056569968522212334119 := by
  unfold tailWord_2705178
  simp only [CollatzResearch.WordTrace]
  refine ⟨24666486848402397116301047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65777298262406392310136125 24666486848402397116301047)
  ·
    refine ⟨36999730272603595674451571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24666486848402397116301047 36999730272603595674451571)
    ·
      refine ⟨55499595408905393511677357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36999730272603595674451571 55499595408905393511677357)
      ·
        refine ⟨20812348278339522566879009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55499595408905393511677357 20812348278339522566879009)
        ·
          refine ⟨15609261208754641925159257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20812348278339522566879009 15609261208754641925159257)
          ·
            refine ⟨11706945906565981443869443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15609261208754641925159257 11706945906565981443869443)
            ·
              refine ⟨17560418859848972165804165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11706945906565981443869443 17560418859848972165804165)
              ·
                refine ⟨3292578536221682281088281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17560418859848972165804165 3292578536221682281088281)
                ·
                  refine ⟨2469433902166261710816211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3292578536221682281088281 2469433902166261710816211)
                  ·
                    refine ⟨3704150853249392566224317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469433902166261710816211 3704150853249392566224317)
                    ·
                      refine ⟨1389056569968522212334119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704150853249392566224317 1389056569968522212334119)
                      ·
                        rfl

theorem cell23_2705178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2705178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705178 prefixEnd_2705178 := by exact prefixLift 2705178
  have htrace : WordTrace (prefixWord ++ tailWord_2705178) baseStart_2705178 baseEnd_2705178 := by
    simpa [prefixWord, tailWord_2705178, baseEnd_2705178] using wordTrace_append hprefix tailTrace_2705178
  have hstable : (prefixWord ++ tailWord_2705178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705178).length < 2 ^ (prefixWord ++ tailWord_2705178).sum := by decide
  have hdescent : baseEnd_2705178 < baseStart_2705178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705184 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2705184 : Nat := 118140960795 + 2705184 * 2 ^ 59
def prefixEnd_2705184 : Nat := 4983230072969 + 3 ^ 40 * 2705184 * 2
def baseEnd_2705184 : Nat := 1389059650852449188859091

theorem tailTrace_2705184 : CollatzResearch.WordTrace tailWord_2705184 prefixEnd_2705184 1389059650852449188859091 := by
  unfold tailWord_2705184
  simp only [CollatzResearch.WordTrace]
  refine ⟨49333083115793925744961303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65777444154391900993281737 49333083115793925744961303)
  ·
    refine ⟨73999624673690888617441955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49333083115793925744961303 73999624673690888617441955)
    ·
      refine ⟨110999437010536332926162933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73999624673690888617441955 110999437010536332926162933)
      ·
        refine ⟨10406197219737781211827775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110999437010536332926162933 10406197219737781211827775)
        ·
          refine ⟨15609295829606671817741663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10406197219737781211827775 15609295829606671817741663)
          ·
            refine ⟨23413943744410007726612495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15609295829606671817741663 23413943744410007726612495)
            ·
              refine ⟨35120915616615011589918743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23413943744410007726612495 35120915616615011589918743)
              ·
                refine ⟨52681373424922517384878115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35120915616615011589918743 52681373424922517384878115)
                ·
                  refine ⟨79022060137383776077317173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52681373424922517384878115 79022060137383776077317173)
                  ·
                    refine ⟨7408318137879729007248485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79022060137383776077317173 7408318137879729007248485)
                    ·
                      refine ⟨1389059650852449188859091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7408318137879729007248485 1389059650852449188859091)
                      ·
                        rfl

theorem cell23_2705184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2705184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705184 prefixEnd_2705184 := by exact prefixLift 2705184
  have htrace : WordTrace (prefixWord ++ tailWord_2705184) baseStart_2705184 baseEnd_2705184 := by
    simpa [prefixWord, tailWord_2705184, baseEnd_2705184] using wordTrace_append hprefix tailTrace_2705184
  have hstable : (prefixWord ++ tailWord_2705184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705184).length < 2 ^ (prefixWord ++ tailWord_2705184).sum := by decide
  have hdescent : baseEnd_2705184 < baseStart_2705184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705188 : List Nat := [2, 3, 1, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_2705188 : Nat := 118140960795 + 2705188 * 2 ^ 59
def prefixEnd_2705188 : Nat := 4983230072969 + 3 ^ 40 * 2705188 * 2
def baseEnd_2705188 : Nat := 1389061704775067173209073

theorem tailTrace_2705188 : CollatzResearch.WordTrace tailWord_2705188 prefixEnd_2705188 1389061704775067173209073 := by
  unfold tailWord_2705188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49333156061786680086534109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65777541415715573448712145 49333156061786680086534109)
  ·
    refine ⟨18499933523170005032450291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49333156061786680086534109 18499933523170005032450291)
    ·
      refine ⟨27749900284755007548675437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499933523170005032450291 27749900284755007548675437)
      ·
        refine ⟨10406212606783127830753289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27749900284755007548675437 10406212606783127830753289)
        ·
          refine ⟨7804659455087345873064967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10406212606783127830753289 7804659455087345873064967)
          ·
            refine ⟨11706989182631018809597451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7804659455087345873064967 11706989182631018809597451)
            ·
              refine ⟨17560483773946528214396177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11706989182631018809597451 17560483773946528214396177)
              ·
                refine ⟨13170362830459896160797133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17560483773946528214396177 13170362830459896160797133)
                ·
                  refine ⟨4938886061422461060298925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13170362830459896160797133 4938886061422461060298925)
                  ·
                    refine ⟨1852082273033422897612097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4938886061422461060298925 1852082273033422897612097)
                    ·
                      refine ⟨1389061704775067173209073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852082273033422897612097 1389061704775067173209073)
                      ·
                        rfl

theorem cell23_2705188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_2705188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705188 prefixEnd_2705188 := by exact prefixLift 2705188
  have htrace : WordTrace (prefixWord ++ tailWord_2705188) baseStart_2705188 baseEnd_2705188 := by
    simpa [prefixWord, tailWord_2705188, baseEnd_2705188] using wordTrace_append hprefix tailTrace_2705188
  have hstable : (prefixWord ++ tailWord_2705188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705188).length < 2 ^ (prefixWord ++ tailWord_2705188).sum := by decide
  have hdescent : baseEnd_2705188 < baseStart_2705188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705241 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 5]
def baseStart_2705241 : Nat := 118140960795 + 2705241 * 2 ^ 59
def prefixEnd_2705241 : Nat := 4983230072969 + 3 ^ 40 * 2705241 * 2
def baseEnd_2705241 : Nat := 154343213249972829538481

theorem tailTrace_2705241 : CollatzResearch.WordTrace tailWord_2705241 prefixEnd_2705241 154343213249972829538481 := by
  unfold tailWord_2705241
  simp only [CollatzResearch.WordTrace]
  refine ⟨98668245192381350224747577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65778830128254233483165051 98668245192381350224747577)
  ·
    refine ⟨74001183894286012668560683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98668245192381350224747577 74001183894286012668560683)
    ·
      refine ⟨111001775841429019002841025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74001183894286012668560683 111001775841429019002841025)
      ·
        refine ⟨83251331881071764252130769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111001775841429019002841025 83251331881071764252130769)
        ·
          refine ⟨62438498910803823189098077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83251331881071764252130769 62438498910803823189098077)
          ·
            refine ⟨23414437091551433695911779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62438498910803823189098077 23414437091551433695911779)
            ·
              refine ⟨35121655637327150543867669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23414437091551433695911779 35121655637327150543867669)
              ·
                refine ⟨1646327607999710181743797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35121655637327150543867669 1646327607999710181743797)
                ·
                  refine ⟨154343213249972829538481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1646327607999710181743797 154343213249972829538481)
                  ·
                    rfl

theorem cell23_2705241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 5].length) (baseStart_2705241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705241 prefixEnd_2705241 := by exact prefixLift 2705241
  have htrace : WordTrace (prefixWord ++ tailWord_2705241) baseStart_2705241 baseEnd_2705241 := by
    simpa [prefixWord, tailWord_2705241, baseEnd_2705241] using wordTrace_append hprefix tailTrace_2705241
  have hstable : (prefixWord ++ tailWord_2705241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705241).length < 2 ^ (prefixWord ++ tailWord_2705241).sum := by decide
  have hdescent : baseEnd_2705241 < baseStart_2705241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705252 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_2705252 : Nat := 118140960795 + 2705252 * 2 ^ 59
def prefixEnd_2705252 : Nat := 4983230072969 + 3 ^ 40 * 2705252 * 2
def baseEnd_2705252 : Nat := 1389094567536954922808779

theorem tailTrace_2705252 : CollatzResearch.WordTrace tailWord_2705252 prefixEnd_2705252 1389094567536954922808779 := by
  unfold tailWord_2705252
  simp only [CollatzResearch.WordTrace]
  refine ⟨49334323197670749551699005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65779097596894332735598673 49334323197670749551699005)
  ·
    refine ⟨18500371199126531081887127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49334323197670749551699005 18500371199126531081887127)
    ·
      refine ⟨27750556798689796622830691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18500371199126531081887127 27750556798689796622830691)
      ·
        refine ⟨41625835198034694934246037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27750556798689796622830691 41625835198034694934246037)
        ·
          refine ⟨1951211024907876325042783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41625835198034694934246037 1951211024907876325042783)
          ·
            refine ⟨2926816537361814487564175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951211024907876325042783 2926816537361814487564175)
            ·
              refine ⟨4390224806042721731346263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926816537361814487564175 4390224806042721731346263)
              ·
                refine ⟨6585337209064082597019395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390224806042721731346263 6585337209064082597019395)
                ·
                  refine ⟨9878005813596123895529093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585337209064082597019395 9878005813596123895529093)
                  ·
                    refine ⟨1852126090049273230411705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9878005813596123895529093 1852126090049273230411705)
                    ·
                      refine ⟨1389094567536954922808779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852126090049273230411705 1389094567536954922808779)
                      ·
                        rfl

theorem cell23_2705252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_2705252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705252 prefixEnd_2705252 := by exact prefixLift 2705252
  have htrace : WordTrace (prefixWord ++ tailWord_2705252) baseStart_2705252 baseEnd_2705252 := by
    simpa [prefixWord, tailWord_2705252, baseEnd_2705252] using wordTrace_append hprefix tailTrace_2705252
  have hstable : (prefixWord ++ tailWord_2705252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705252).length < 2 ^ (prefixWord ++ tailWord_2705252).sum := by decide
  have hdescent : baseEnd_2705252 < baseStart_2705252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705264 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_2705264 : Nat := 118140960795 + 2705264 * 2 ^ 59
def prefixEnd_2705264 : Nat := 4983230072969 + 3 ^ 40 * 2705264 * 2
def baseEnd_2705264 : Nat := 1389100729304808875858723

theorem tailTrace_2705264 : CollatzResearch.WordTrace tailWord_2705264 prefixEnd_2705264 1389100729304808875858723 := by
  unfold tailWord_2705264
  simp only [CollatzResearch.WordTrace]
  refine ⟨49334542035649012576417423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65779389380865350101889897 49334542035649012576417423)
  ·
    refine ⟨74001813053473518864626135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49334542035649012576417423 74001813053473518864626135)
    ·
      refine ⟨111002719580210278296939203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74001813053473518864626135 111002719580210278296939203)
      ·
        refine ⟨166504079370315417445408805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111002719580210278296939203 166504079370315417445408805)
        ·
          refine ⟨31219514881934140771014151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166504079370315417445408805 31219514881934140771014151)
          ·
            refine ⟨46829272322901211156521227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31219514881934140771014151 46829272322901211156521227)
            ·
              refine ⟨70243908484351816734781841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46829272322901211156521227 70243908484351816734781841)
              ·
                refine ⟨52682931363263862551086381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70243908484351816734781841 52682931363263862551086381)
                ·
                  refine ⟨19756099261223948456657393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52682931363263862551086381 19756099261223948456657393)
                  ·
                    refine ⟨14817074445917961342493045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19756099261223948456657393 14817074445917961342493045)
                    ·
                      refine ⟨1389100729304808875858723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14817074445917961342493045 1389100729304808875858723)
                      ·
                        rfl

theorem cell23_2705264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_2705264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705264 prefixEnd_2705264 := by exact prefixLift 2705264
  have htrace : WordTrace (prefixWord ++ tailWord_2705264) baseStart_2705264 baseEnd_2705264 := by
    simpa [prefixWord, tailWord_2705264, baseEnd_2705264] using wordTrace_append hprefix tailTrace_2705264
  have hstable : (prefixWord ++ tailWord_2705264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705264).length < 2 ^ (prefixWord ++ tailWord_2705264).sum := by decide
  have hdescent : baseEnd_2705264 < baseStart_2705264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705288 : List Nat := [2, 1, 3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_2705288 : Nat := 118140960795 + 2705288 * 2 ^ 59
def prefixEnd_2705288 : Nat := 4983230072969 + 3 ^ 40 * 2705288 * 2
def baseEnd_2705288 : Nat := 463037684280172260652871

theorem tailTrace_2705288 : CollatzResearch.WordTrace tailWord_2705288 prefixEnd_2705288 463037684280172260652871 := by
  unfold tailWord_2705288
  simp only [CollatzResearch.WordTrace]
  refine ⟨49334979711605538625854259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65779972948807384834472345 49334979711605538625854259)
  ·
    refine ⟨74002469567408307938781389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49334979711605538625854259 74002469567408307938781389)
    ·
      refine ⟨27750926087778115477043021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74002469567408307938781389 27750926087778115477043021)
      ·
        refine ⟨10406597282916793303891133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27750926087778115477043021 10406597282916793303891133)
        ·
          refine ⟨3902473981093797488959175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10406597282916793303891133 3902473981093797488959175)
          ·
            refine ⟨5853710971640696233438763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902473981093797488959175 5853710971640696233438763)
            ·
              refine ⟨8780566457461044350158145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853710971640696233438763 8780566457461044350158145)
              ·
                refine ⟨6585424843095783262618609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8780566457461044350158145 6585424843095783262618609)
                ·
                  refine ⟨4939068632321837446963957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6585424843095783262618609 4939068632321837446963957)
                  ·
                    refine ⟨463037684280172260652871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4939068632321837446963957 463037684280172260652871)
                    ·
                      rfl

theorem cell23_2705288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_2705288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705288 prefixEnd_2705288 := by exact prefixLift 2705288
  have htrace : WordTrace (prefixWord ++ tailWord_2705288) baseStart_2705288 baseEnd_2705288 := by
    simpa [prefixWord, tailWord_2705288, baseEnd_2705288] using wordTrace_append hprefix tailTrace_2705288
  have hstable : (prefixWord ++ tailWord_2705288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705288).length < 2 ^ (prefixWord ++ tailWord_2705288).sum := by decide
  have hdescent : baseEnd_2705288 < baseStart_2705288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705298 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2705298 : Nat := 118140960795 + 2705298 * 2 ^ 59
def prefixEnd_2705298 : Nat := 4983230072969 + 3 ^ 40 * 2705298 * 2
def baseEnd_2705298 : Nat := 1389118187647061742833567

theorem tailTrace_2705298 : CollatzResearch.WordTrace tailWord_2705298 prefixEnd_2705298 1389118187647061742833567 := by
  unfold tailWord_2705298
  simp only [CollatzResearch.WordTrace]
  refine ⟨24667581038293712239893137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65780216102116565973048365 24667581038293712239893137)
  ·
    refine ⟨18500685778720284179919853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24667581038293712239893137 18500685778720284179919853)
    ·
      refine ⟨6937757167020106567469945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18500685778720284179919853 6937757167020106567469945)
      ·
        refine ⟨5203317875265079925602459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6937757167020106567469945 5203317875265079925602459)
        ·
          refine ⟨7804976812897619888403689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203317875265079925602459 7804976812897619888403689)
          ·
            refine ⟨5853732609673214916302767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804976812897619888403689 5853732609673214916302767)
            ·
              refine ⟨8780598914509822374454151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853732609673214916302767 8780598914509822374454151)
              ·
                refine ⟨13170898371764733561681227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8780598914509822374454151 13170898371764733561681227)
                ·
                  refine ⟨19756347557647100342521841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13170898371764733561681227 19756347557647100342521841)
                  ·
                    refine ⟨14817260668235325256891381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19756347557647100342521841 14817260668235325256891381)
                    ·
                      refine ⟨1389118187647061742833567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14817260668235325256891381 1389118187647061742833567)
                      ·
                        rfl

theorem cell23_2705298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2705298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705298 prefixEnd_2705298 := by exact prefixLift 2705298
  have htrace : WordTrace (prefixWord ++ tailWord_2705298) baseStart_2705298 baseEnd_2705298 := by
    simpa [prefixWord, tailWord_2705298, baseEnd_2705298] using wordTrace_append hprefix tailTrace_2705298
  have hstable : (prefixWord ++ tailWord_2705298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705298).length < 2 ^ (prefixWord ++ tailWord_2705298).sum := by decide
  have hdescent : baseEnd_2705298 < baseStart_2705298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705324 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2705324 : Nat := 118140960795 + 2705324 * 2 ^ 59
def prefixEnd_2705324 : Nat := 4983230072969 + 3 ^ 40 * 2705324 * 2
def baseEnd_2705324 : Nat := 1389131538144078641108447

theorem tailTrace_2705324 : CollatzResearch.WordTrace tailWord_2705324 prefixEnd_2705324 1389131538144078641108447 := by
  unfold tailWord_2705324
  simp only [CollatzResearch.WordTrace]
  refine ⟨49335636225540327700009513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65780848300720436933346017 49335636225540327700009513)
  ·
    refine ⟨37001727169155245775007135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49335636225540327700009513 37001727169155245775007135)
    ·
      refine ⟨55502590753732868662510703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37001727169155245775007135 55502590753732868662510703)
      ·
        refine ⟨83253886130599302993766055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55502590753732868662510703 83253886130599302993766055)
        ·
          refine ⟨124880829195898954490649083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83253886130599302993766055 124880829195898954490649083)
          ·
            refine ⟨187321243793848431735973625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124880829195898954490649083 187321243793848431735973625)
            ·
              refine ⟨140490932845386323801980219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187321243793848431735973625 140490932845386323801980219)
              ·
                refine ⟨210736399268079485702970329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140490932845386323801980219 210736399268079485702970329)
                ·
                  refine ⟨158052299451059614277227747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210736399268079485702970329 158052299451059614277227747)
                  ·
                    refine ⟨237078449176589421415841621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158052299451059614277227747 237078449176589421415841621)
                    ·
                      refine ⟨1389131538144078641108447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 237078449176589421415841621 1389131538144078641108447)
                      ·
                        rfl

theorem cell23_2705324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2705324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705324 prefixEnd_2705324 := by exact prefixLift 2705324
  have htrace : WordTrace (prefixWord ++ tailWord_2705324) baseStart_2705324 baseEnd_2705324 := by
    simpa [prefixWord, tailWord_2705324, baseEnd_2705324] using wordTrace_append hprefix tailTrace_2705324
  have hstable : (prefixWord ++ tailWord_2705324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705324).length < 2 ^ (prefixWord ++ tailWord_2705324).sum := by decide
  have hdescent : baseEnd_2705324 < baseStart_2705324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705352 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 1, 4]
def baseStart_2705352 : Nat := 118140960795 + 2705352 * 2 ^ 59
def prefixEnd_2705352 : Nat := 4983230072969 + 3 ^ 40 * 2705352 * 2
def baseEnd_2705352 : Nat := 463048638534134843852773

theorem tailTrace_2705352 : CollatzResearch.WordTrace tailWord_2705352 prefixEnd_2705352 463048638534134843852773 := by
  unfold tailWord_2705352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49336146847489608091019155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65781529129986144121358873 49336146847489608091019155)
  ·
    refine ⟨74004220271234412136528733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49336146847489608091019155 74004220271234412136528733)
    ·
      refine ⟨27751582601712904551198275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74004220271234412136528733 27751582601712904551198275)
      ·
        refine ⟨41627373902569356826797413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27751582601712904551198275 41627373902569356826797413)
        ·
          refine ⟨7805132606731754405024515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41627373902569356826797413 7805132606731754405024515)
          ·
            refine ⟨11707698910097631607536773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805132606731754405024515 11707698910097631607536773)
            ·
              refine ⟨2195193545643305926413145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11707698910097631607536773 2195193545643305926413145)
              ·
                refine ⟨1646395159232479444809859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195193545643305926413145 1646395159232479444809859)
                ·
                  refine ⟨2469592738848719167214789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646395159232479444809859 2469592738848719167214789)
                  ·
                    refine ⟨463048638534134843852773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469592738848719167214789 463048638534134843852773)
                    ·
                      rfl

theorem cell23_2705352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_2705352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705352 prefixEnd_2705352 := by exact prefixLift 2705352
  have htrace : WordTrace (prefixWord ++ tailWord_2705352) baseStart_2705352 baseEnd_2705352 := by
    simpa [prefixWord, tailWord_2705352, baseEnd_2705352] using wordTrace_append hprefix tailTrace_2705352
  have hstable : (prefixWord ++ tailWord_2705352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705352).length < 2 ^ (prefixWord ++ tailWord_2705352).sum := by decide
  have hdescent : baseEnd_2705352 < baseStart_2705352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705368 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_2705368 : Nat := 118140960795 + 2705368 * 2 ^ 59
def prefixEnd_2705368 : Nat := 4983230072969 + 3 ^ 40 * 2705368 * 2
def baseEnd_2705368 : Nat := 1389154131292876468958245

theorem tailTrace_2705368 : CollatzResearch.WordTrace tailWord_2705368 prefixEnd_2705368 1389154131292876468958245 := by
  unfold tailWord_2705368
  simp only [CollatzResearch.WordTrace]
  refine ⟨49336438631460625457310379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65781918175280833943080505 49336438631460625457310379)
  ·
    refine ⟨74004657947190938185965569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49336438631460625457310379 74004657947190938185965569)
    ·
      refine ⟨55503493460393203639474177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74004657947190938185965569 55503493460393203639474177)
      ·
        refine ⟨41627620095294902729605633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55503493460393203639474177 41627620095294902729605633)
        ·
          refine ⟨31220715071471177047204225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41627620095294902729605633 31220715071471177047204225)
          ·
            refine ⟨23415536303603382785403169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31220715071471177047204225 23415536303603382785403169)
            ·
              refine ⟨17561652227702537089052377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23415536303603382785403169 17561652227702537089052377)
              ·
                refine ⟨13171239170776902816789283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17561652227702537089052377 13171239170776902816789283)
                ·
                  refine ⟨19756858756165354225183925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13171239170776902816789283 19756858756165354225183925)
                  ·
                    refine ⟨1852205508390501958610993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19756858756165354225183925 1852205508390501958610993)
                    ·
                      refine ⟨1389154131292876468958245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852205508390501958610993 1389154131292876468958245)
                      ·
                        rfl

theorem cell23_2705368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_2705368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705368 prefixEnd_2705368 := by exact prefixLift 2705368
  have htrace : WordTrace (prefixWord ++ tailWord_2705368) baseStart_2705368 baseEnd_2705368 := by
    simpa [prefixWord, tailWord_2705368, baseEnd_2705368] using wordTrace_append hprefix tailTrace_2705368
  have hstable : (prefixWord ++ tailWord_2705368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705368).length < 2 ^ (prefixWord ++ tailWord_2705368).sum := by decide
  have hdescent : baseEnd_2705368 < baseStart_2705368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705375 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 3]
def baseStart_2705375 : Nat := 118140960795 + 2705375 * 2 ^ 59
def prefixEnd_2705375 : Nat := 4983230072969 + 3 ^ 40 * 2705375 * 2
def baseEnd_2705375 : Nat := 1389157725657457941570713

theorem tailTrace_2705375 : CollatzResearch.WordTrace tailWord_2705375 prefixEnd_2705375 1389157725657457941570713 := by
  unfold tailWord_2705375
  simp only [CollatzResearch.WordTrace]
  refine ⟨98673132573895891110125579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65782088382597260740083719 98673132573895891110125579)
  ·
    refine ⟨148009698860843836665188369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98673132573895891110125579 148009698860843836665188369)
    ·
      refine ⟨111007274145632877498891277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148009698860843836665188369 111007274145632877498891277)
      ·
        refine ⟨41627727804612329062084229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111007274145632877498891277 41627727804612329062084229)
        ·
          refine ⟨7805198963364811699140793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41627727804612329062084229 7805198963364811699140793)
          ·
            refine ⟨5853899222523608774355595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7805198963364811699140793 5853899222523608774355595)
            ·
              refine ⟨8780848833785413161533393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853899222523608774355595 8780848833785413161533393)
              ·
                refine ⟨6585636625339059871150045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8780848833785413161533393 6585636625339059871150045)
                ·
                  refine ⟨2469613734502147451681267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6585636625339059871150045 2469613734502147451681267)
                  ·
                    refine ⟨3704420601753221177521901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469613734502147451681267 3704420601753221177521901)
                    ·
                      refine ⟨1389157725657457941570713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704420601753221177521901 1389157725657457941570713)
                      ·
                        rfl

theorem cell23_2705375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_2705375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705375 prefixEnd_2705375 := by exact prefixLift 2705375
  have htrace : WordTrace (prefixWord ++ tailWord_2705375) baseStart_2705375 baseEnd_2705375 := by
    simpa [prefixWord, tailWord_2705375, baseEnd_2705375] using wordTrace_append hprefix tailTrace_2705375
  have hstable : (prefixWord ++ tailWord_2705375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705375).length < 2 ^ (prefixWord ++ tailWord_2705375).sum := by decide
  have hdescent : baseEnd_2705375 < baseStart_2705375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705391 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 1, 6]
def baseStart_2705391 : Nat := 118140960795 + 2705391 * 2 ^ 59
def prefixEnd_2705391 : Nat := 4983230072969 + 3 ^ 40 * 2705391 * 2
def baseEnd_2705391 : Nat := 463055313782643292990213

theorem tailTrace_2705391 : CollatzResearch.WordTrace tailWord_2705391 prefixEnd_2705391 463055313782643292990213 := by
  unfold tailWord_2705391
  simp only [CollatzResearch.WordTrace]
  refine ⟨98673716141837925842708027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65782477427891950561805351 98673716141837925842708027)
  ·
    refine ⟨148010574212756888764062041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98673716141837925842708027 148010574212756888764062041)
    ·
      refine ⟨111007930659567666573046531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148010574212756888764062041 111007930659567666573046531)
      ·
        refine ⟨166511895989351499859569797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111007930659567666573046531 166511895989351499859569797)
        ·
          refine ⟨31220980498003406223669337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166511895989351499859569797 31220980498003406223669337)
          ·
            refine ⟨23415735373502554667752003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31220980498003406223669337 23415735373502554667752003)
            ·
              refine ⟨35123603060253832001628005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23415735373502554667752003 35123603060253832001628005)
              ·
                refine ⟨6585675573797593500305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35123603060253832001628005 6585675573797593500305251)
                ·
                  refine ⟨9878513360696390250457877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585675573797593500305251 9878513360696390250457877)
                  ·
                    refine ⟨463055313782643292990213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9878513360696390250457877 463055313782643292990213)
                    ·
                      rfl

theorem cell23_2705391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_2705391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705391 prefixEnd_2705391 := by exact prefixLift 2705391
  have htrace : WordTrace (prefixWord ++ tailWord_2705391) baseStart_2705391 baseEnd_2705391 := by
    simpa [prefixWord, tailWord_2705391, baseEnd_2705391] using wordTrace_append hprefix tailTrace_2705391
  have hstable : (prefixWord ++ tailWord_2705391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705391).length < 2 ^ (prefixWord ++ tailWord_2705391).sum := by decide
  have hdescent : baseEnd_2705391 < baseStart_2705391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705408 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_2705408 : Nat := 118140960795 + 2705408 * 2 ^ 59
def prefixEnd_2705408 : Nat := 4983230072969 + 3 ^ 40 * 2705408 * 2
def baseEnd_2705408 : Nat := 463058223506352104152687

theorem tailTrace_2705408 : CollatzResearch.WordTrace tailWord_2705408 prefixEnd_2705408 463058223506352104152687 := by
  unfold tailWord_2705408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49337168091388168873038439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65782890788517558497384585 49337168091388168873038439)
  ·
    refine ⟨74005752137082253309557659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49337168091388168873038439 74005752137082253309557659)
    ·
      refine ⟨111008628205623379964336489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74005752137082253309557659 111008628205623379964336489)
      ·
        refine ⟨83256471154217534973252367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111008628205623379964336489 83256471154217534973252367)
        ·
          refine ⟨124884706731326302459878551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83256471154217534973252367 124884706731326302459878551)
          ·
            refine ⟨187327060096989453689817827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124884706731326302459878551 187327060096989453689817827)
            ·
              refine ⟨280990590145484180534726741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187327060096989453689817827 280990590145484180534726741)
              ·
                refine ⟨3292858478267392740641329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 280990590145484180534726741 3292858478267392740641329)
                ·
                  refine ⟨2469643858700544555480997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3292858478267392740641329 2469643858700544555480997)
                  ·
                    refine ⟨463058223506352104152687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469643858700544555480997 463058223506352104152687)
                    ·
                      rfl

theorem cell23_2705408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_2705408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705408 prefixEnd_2705408 := by exact prefixLift 2705408
  have htrace : WordTrace (prefixWord ++ tailWord_2705408) baseStart_2705408 baseEnd_2705408 := by
    simpa [prefixWord, tailWord_2705408, baseEnd_2705408] using wordTrace_append hprefix tailTrace_2705408
  have hstable : (prefixWord ++ tailWord_2705408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705408).length < 2 ^ (prefixWord ++ tailWord_2705408).sum := by decide
  have hdescent : baseEnd_2705408 < baseStart_2705408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705411 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_2705411 : Nat := 118140960795 + 2705411 * 2 ^ 59
def prefixEnd_2705411 : Nat := 4983230072969 + 3 ^ 40 * 2705411 * 2
def baseEnd_2705411 : Nat := 1389176210961019800720547

theorem tailTrace_2705411 : CollatzResearch.WordTrace tailWord_2705411 prefixEnd_2705411 1389176210961019800720547 := by
  unfold tailWord_2705411
  simp only [CollatzResearch.WordTrace]
  refine ⟨98674445601765469258436087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65782963734510312838957391 98674445601765469258436087)
  ·
    refine ⟨148011668402648203887654131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98674445601765469258436087 148011668402648203887654131)
    ·
      refine ⟨222017502603972305831481197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148011668402648203887654131 222017502603972305831481197)
      ·
        refine ⟨83256563476489614686805449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222017502603972305831481197 83256563476489614686805449)
        ·
          refine ⟨62442422607367211015104087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83256563476489614686805449 62442422607367211015104087)
          ·
            refine ⟨93663633911050816522656131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62442422607367211015104087 93663633911050816522656131)
            ·
              refine ⟨140495450866576224783984197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93663633911050816522656131 140495450866576224783984197)
              ·
                refine ⟨26342897037483042146997037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140495450866576224783984197 26342897037483042146997037)
                ·
                  refine ⟨9878586389056140805123889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26342897037483042146997037 9878586389056140805123889)
                  ·
                    refine ⟨7408939791792105603842917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9878586389056140805123889 7408939791792105603842917)
                    ·
                      refine ⟨1389176210961019800720547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7408939791792105603842917 1389176210961019800720547)
                      ·
                        rfl

theorem cell23_2705411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_2705411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705411 prefixEnd_2705411 := by exact prefixLift 2705411
  have htrace : WordTrace (prefixWord ++ tailWord_2705411) baseStart_2705411 baseEnd_2705411 := by
    simpa [prefixWord, tailWord_2705411, baseEnd_2705411] using wordTrace_append hprefix tailTrace_2705411
  have hstable : (prefixWord ++ tailWord_2705411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705411).length < 2 ^ (prefixWord ++ tailWord_2705411).sum := by decide
  have hdescent : baseEnd_2705411 < baseStart_2705411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705481 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_2705481 : Nat := 118140960795 + 2705481 * 2 ^ 59
def prefixEnd_2705481 : Nat := 4983230072969 + 3 ^ 40 * 2705481 * 2
def baseEnd_2705481 : Nat := 463070718202278175615075

theorem tailTrace_2705481 : CollatzResearch.WordTrace tailWord_2705481 prefixEnd_2705481 463070718202278175615075 := by
  unfold tailWord_2705481
  simp only [CollatzResearch.WordTrace]
  refine ⟨98676998711511871213484297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65784665807674580808989531 98676998711511871213484297)
  ·
    refine ⟨74007749033633903410113223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98676998711511871213484297 74007749033633903410113223)
    ·
      refine ⟨111011623550450855115169835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74007749033633903410113223 111011623550450855115169835)
      ·
        refine ⟨166517435325676282672754753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111011623550450855115169835 166517435325676282672754753)
        ·
          refine ⟨124888076494257212004566065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166517435325676282672754753 124888076494257212004566065)
          ·
            refine ⟨93666057370692909003424549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124888076494257212004566065 93666057370692909003424549)
            ·
              refine ⟨17562385757004920438142103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93666057370692909003424549 17562385757004920438142103)
              ·
                refine ⟨26343578635507380657213155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17562385757004920438142103 26343578635507380657213155)
                ·
                  refine ⟨39515367953261070985819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26343578635507380657213155 39515367953261070985819733)
                  ·
                    refine ⟨463070718202278175615075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 39515367953261070985819733 463070718202278175615075)
                    ·
                      rfl

theorem cell23_2705481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_2705481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705481 prefixEnd_2705481 := by exact prefixLift 2705481
  have htrace : WordTrace (prefixWord ++ tailWord_2705481) baseStart_2705481 baseEnd_2705481 := by
    simpa [prefixWord, tailWord_2705481, baseEnd_2705481] using wordTrace_append hprefix tailTrace_2705481
  have hstable : (prefixWord ++ tailWord_2705481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705481).length < 2 ^ (prefixWord ++ tailWord_2705481).sum := by decide
  have hdescent : baseEnd_2705481 < baseStart_2705481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705508 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_2705508 : Nat := 118140960795 + 2705508 * 2 ^ 59
def prefixEnd_2705508 : Nat := 4983230072969 + 3 ^ 40 * 2705508 * 2
def baseEnd_2705508 : Nat := 1389226018584505921207601

theorem tailTrace_2705508 : CollatzResearch.WordTrace tailWord_2705508 prefixEnd_2705508 1389226018584505921207601 := by
  unfold tailWord_2705508
  simp only [CollatzResearch.WordTrace]
  refine ⟨49338991741207027412358589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65785322321609369883144785 49338991741207027412358589)
  ·
    refine ⟨18502121902952635279634471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49338991741207027412358589 18502121902952635279634471)
    ·
      refine ⟨27753182854428952919451707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18502121902952635279634471 27753182854428952919451707)
      ·
        refine ⟨41629774281643429379177561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27753182854428952919451707 41629774281643429379177561)
        ·
          refine ⟨31222330711232572034383171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41629774281643429379177561 31222330711232572034383171)
          ·
            refine ⟨46833496066848858051574757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31222330711232572034383171 46833496066848858051574757)
            ·
              refine ⟨8781280512534160884670267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46833496066848858051574757 8781280512534160884670267)
              ·
                refine ⟨13171920768801241327005401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8781280512534160884670267 13171920768801241327005401)
                ·
                  refine ⟨9878940576600930995254051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13171920768801241327005401 9878940576600930995254051)
                  ·
                    refine ⟨14818410864901396492881077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9878940576600930995254051 14818410864901396492881077)
                    ·
                      refine ⟨1389226018584505921207601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14818410864901396492881077 1389226018584505921207601)
                      ·
                        rfl

theorem cell23_2705508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_2705508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705508 prefixEnd_2705508 := by exact prefixLift 2705508
  have htrace : WordTrace (prefixWord ++ tailWord_2705508) baseStart_2705508 baseEnd_2705508 := by
    simpa [prefixWord, tailWord_2705508, baseEnd_2705508] using wordTrace_append hprefix tailTrace_2705508
  have hstable : (prefixWord ++ tailWord_2705508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705508).length < 2 ^ (prefixWord ++ tailWord_2705508).sum := by decide
  have hdescent : baseEnd_2705508 < baseStart_2705508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705509 : List Nat := [1, 3, 1, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_2705509 : Nat := 118140960795 + 2705509 * 2 ^ 59
def prefixEnd_2705509 : Nat := 4983230072969 + 3 ^ 40 * 2705509 * 2
def baseEnd_2705509 : Nat := 1389226532065160417295097

theorem tailTrace_2705509 : CollatzResearch.WordTrace tailWord_2705509 prefixEnd_2705509 1389226532065160417295097 := by
  unfold tailWord_2705509
  simp only [CollatzResearch.WordTrace]
  refine ⟨98678019955410431995503581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65785346636940287997002387 98678019955410431995503581)
  ·
    refine ⟨37004257483278911998313843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98678019955410431995503581 37004257483278911998313843)
    ·
      refine ⟨55506386224918367997470765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37004257483278911998313843 55506386224918367997470765)
      ·
        refine ⟨20814894834344387999051537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55506386224918367997470765 20814894834344387999051537)
        ·
          refine ⟨15611171125758290999288653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20814894834344387999051537 15611171125758290999288653)
          ·
            refine ⟨5854189172159359124733245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15611171125758290999288653 5854189172159359124733245)
            ·
              refine ⟨2195320939559759671774967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5854189172159359124733245 2195320939559759671774967)
              ·
                refine ⟨3292981409339639507662451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195320939559759671774967 3292981409339639507662451)
                ·
                  refine ⟨4939472114009459261493677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292981409339639507662451 4939472114009459261493677)
                  ·
                    refine ⟨1852302042753547223060129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4939472114009459261493677 1852302042753547223060129)
                    ·
                      refine ⟨1389226532065160417295097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852302042753547223060129 1389226532065160417295097)
                      ·
                        rfl

theorem cell23_2705509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_2705509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705509 prefixEnd_2705509 := by exact prefixLift 2705509
  have htrace : WordTrace (prefixWord ++ tailWord_2705509) baseStart_2705509 baseEnd_2705509 := by
    simpa [prefixWord, tailWord_2705509, baseEnd_2705509] using wordTrace_append hprefix tailTrace_2705509
  have hstable : (prefixWord ++ tailWord_2705509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705509).length < 2 ^ (prefixWord ++ tailWord_2705509).sum := by decide
  have hdescent : baseEnd_2705509 < baseStart_2705509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705531 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8]
def baseStart_2705531 : Nat := 118140960795 + 2705531 * 2 ^ 59
def prefixEnd_2705531 : Nat := 4983230072969 + 3 ^ 40 * 2705531 * 2
def baseEnd_2705531 : Nat := 1389237828639559331219995

theorem tailTrace_2705531 : CollatzResearch.WordTrace tailWord_2705531 prefixEnd_2705531 1389237828639559331219995 := by
  unfold tailWord_2705531
  simp only [CollatzResearch.WordTrace]
  refine ⟨98678822361330729752804447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65785881574220486501869631 98678822361330729752804447)
  ·
    refine ⟨148018233541996094629206671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98678822361330729752804447 148018233541996094629206671)
    ·
      refine ⟨222027350312994141943810007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148018233541996094629206671 222027350312994141943810007)
      ·
        refine ⟨333041025469491212915715011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222027350312994141943810007 333041025469491212915715011)
        ·
          refine ⟨499561538204236819373572517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333041025469491212915715011 499561538204236819373572517)
          ·
            refine ⟨93667788413294403632544847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 499561538204236819373572517 93667788413294403632544847)
            ·
              refine ⟨140501682619941605448817271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93667788413294403632544847 140501682619941605448817271)
              ·
                refine ⟨210752523929912408173225907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140501682619941605448817271 210752523929912408173225907)
                ·
                  refine ⟨316128785894868612259838861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210752523929912408173225907 316128785894868612259838861)
                  ·
                    refine ⟨118548294710575729597439573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316128785894868612259838861 118548294710575729597439573)
                    ·
                      refine ⟨1389237828639559331219995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 118548294710575729597439573 1389237828639559331219995)
                      ·
                        rfl

theorem cell23_2705531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_2705531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705531 prefixEnd_2705531 := by exact prefixLift 2705531
  have htrace : WordTrace (prefixWord ++ tailWord_2705531) baseStart_2705531 baseEnd_2705531 := by
    simpa [prefixWord, tailWord_2705531, baseEnd_2705531] using wordTrace_append hprefix tailTrace_2705531
  have hstable : (prefixWord ++ tailWord_2705531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705531).length < 2 ^ (prefixWord ++ tailWord_2705531).sum := by decide
  have hdescent : baseEnd_2705531 < baseStart_2705531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705595 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 2, 4, 2]
def baseStart_2705595 : Nat := 118140960795 + 2705595 * 2 ^ 59
def prefixEnd_2705595 : Nat := 4983230072969 + 3 ^ 40 * 2705595 * 2
def baseEnd_2705595 : Nat := 1389270691401447080819701

theorem tailTrace_2705595 : CollatzResearch.WordTrace tailWord_2705595 prefixEnd_2705595 1389270691401447080819701 := by
  unfold tailWord_2705595
  simp only [CollatzResearch.WordTrace]
  refine ⟨98681156633098868683134239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65787437755399245788756159 98681156633098868683134239)
  ·
    refine ⟨148021734949648303024701359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98681156633098868683134239 148021734949648303024701359)
    ·
      refine ⟨222032602424472454537052039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148021734949648303024701359 222032602424472454537052039)
      ·
        refine ⟨333048903636708681805578059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222032602424472454537052039 333048903636708681805578059)
        ·
          refine ⟨499573355455063022708367089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333048903636708681805578059 499573355455063022708367089)
          ·
            refine ⟨374680016591297267031275317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499573355455063022708367089 374680016591297267031275317)
            ·
              refine ⟨35126251555434118784182061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 374680016591297267031275317 35126251555434118784182061)
              ·
                refine ⟨13172344333287794544068273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35126251555434118784182061 13172344333287794544068273)
                ·
                  refine ⟨9879258249965845908051205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13172344333287794544068273 9879258249965845908051205)
                  ·
                    refine ⟨1852360921868596107759601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9879258249965845908051205 1852360921868596107759601)
                    ·
                      refine ⟨1389270691401447080819701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852360921868596107759601 1389270691401447080819701)
                      ·
                        rfl

theorem cell23_2705595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 4, 2].length) (baseStart_2705595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705595 prefixEnd_2705595 := by exact prefixLift 2705595
  have htrace : WordTrace (prefixWord ++ tailWord_2705595) baseStart_2705595 baseEnd_2705595 := by
    simpa [prefixWord, tailWord_2705595, baseEnd_2705595] using wordTrace_append hprefix tailTrace_2705595
  have hstable : (prefixWord ++ tailWord_2705595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705595).length < 2 ^ (prefixWord ++ tailWord_2705595).sum := by decide
  have hdescent : baseEnd_2705595 < baseStart_2705595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705605 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_2705605 : Nat := 118140960795 + 2705605 * 2 ^ 59
def prefixEnd_2705605 : Nat := 4983230072969 + 3 ^ 40 * 2705605 * 2
def baseEnd_2705605 : Nat := 463091942069330680564885

theorem tailTrace_2705605 : CollatzResearch.WordTrace tailWord_2705605 prefixEnd_2705605 463091942069330680564885 := by
  unfold tailWord_2705605
  simp only [CollatzResearch.WordTrace]
  refine ⟨98681521363062640390998269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65787680908708426927332179 98681521363062640390998269)
  ·
    refine ⟨37005570511148490146624351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98681521363062640390998269 37005570511148490146624351)
    ·
      refine ⟨55508355766722735219936527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37005570511148490146624351 55508355766722735219936527)
      ·
        refine ⟨83262533650084102829904791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55508355766722735219936527 83262533650084102829904791)
        ·
          refine ⟨124893800475126154244857187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83262533650084102829904791 124893800475126154244857187)
          ·
            refine ⟨187340700712689231367285781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124893800475126154244857187 187340700712689231367285781)
            ·
              refine ⟨8781595345907307720341521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187340700712689231367285781 8781595345907307720341521)
              ·
                refine ⟨6586196509430480790256141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781595345907307720341521 6586196509430480790256141)
                ·
                  refine ⟨2469823691036430296346053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6586196509430480790256141 2469823691036430296346053)
                  ·
                    refine ⟨463091942069330680564885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469823691036430296346053 463091942069330680564885)
                    ·
                      rfl

theorem cell23_2705605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_2705605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705605 prefixEnd_2705605 := by exact prefixLift 2705605
  have htrace : WordTrace (prefixWord ++ tailWord_2705605) baseStart_2705605 baseEnd_2705605 := by
    simpa [prefixWord, tailWord_2705605, baseEnd_2705605] using wordTrace_append hprefix tailTrace_2705605
  have hstable : (prefixWord ++ tailWord_2705605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705605).length < 2 ^ (prefixWord ++ tailWord_2705605).sum := by decide
  have hdescent : baseEnd_2705605 < baseStart_2705605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705608 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_2705608 : Nat := 118140960795 + 2705608 * 2 ^ 59
def prefixEnd_2705608 : Nat := 4983230072969 + 3 ^ 40 * 2705608 * 2
def baseEnd_2705608 : Nat := 1389277366649955529957141

theorem tailTrace_2705608 : CollatzResearch.WordTrace tailWord_2705608 prefixEnd_2705608 1389277366649955529957141 := by
  unfold tailWord_2705608
  simp only [CollatzResearch.WordTrace]
  refine ⟨49340815391025885951678739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65787753854701181268904985 49340815391025885951678739)
  ·
    refine ⟨74011223086538828927518109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49340815391025885951678739 74011223086538828927518109)
    ·
      refine ⟨27754208657452060847819291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74011223086538828927518109 27754208657452060847819291)
      ·
        refine ⟨41631312986178091271728937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27754208657452060847819291 41631312986178091271728937)
        ·
          refine ⟨31223484739633568453796703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41631312986178091271728937 31223484739633568453796703)
          ·
            refine ⟨46835227109450352680695055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31223484739633568453796703 46835227109450352680695055)
            ·
              refine ⟨70252840664175529021042583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46835227109450352680695055 70252840664175529021042583)
              ·
                refine ⟨105379260996263293531563875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70252840664175529021042583 105379260996263293531563875)
                ·
                  refine ⟨158068891494394940297345813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105379260996263293531563875 158068891494394940297345813)
                  ·
                    refine ⟨7409479288799762826438085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 158068891494394940297345813 7409479288799762826438085)
                    ·
                      refine ⟨1389277366649955529957141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7409479288799762826438085 1389277366649955529957141)
                      ·
                        rfl

theorem cell23_2705608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_2705608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705608 prefixEnd_2705608 := by exact prefixLift 2705608
  have htrace : WordTrace (prefixWord ++ tailWord_2705608) baseStart_2705608 baseEnd_2705608 := by
    simpa [prefixWord, tailWord_2705608, baseEnd_2705608] using wordTrace_append hprefix tailTrace_2705608
  have hstable : (prefixWord ++ tailWord_2705608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705608).length < 2 ^ (prefixWord ++ tailWord_2705608).sum := by decide
  have hdescent : baseEnd_2705608 < baseStart_2705608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705615 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_2705615 : Nat := 118140960795 + 2705615 * 2 ^ 59
def prefixEnd_2705615 : Nat := 4983230072969 + 3 ^ 40 * 2705615 * 2
def baseEnd_2705615 : Nat := 1389280961014537002569609

theorem tailTrace_2705615 : CollatzResearch.WordTrace tailWord_2705615 prefixEnd_2705615 1389280961014537002569609 := by
  unfold tailWord_2705615
  simp only [CollatzResearch.WordTrace]
  refine ⟨98681886093026412098862299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65787924062017608065908199 98681886093026412098862299)
  ·
    refine ⟨148022829139539618148293449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98681886093026412098862299 148022829139539618148293449)
    ·
      refine ⟨111017121854654713611220087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148022829139539618148293449 111017121854654713611220087)
      ·
        refine ⟨166525682781982070416830131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111017121854654713611220087 166525682781982070416830131)
        ·
          refine ⟨249788524172973105625245197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166525682781982070416830131 249788524172973105625245197)
          ·
            refine ⟨93670696564864914609466949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249788524172973105625245197 93670696564864914609466949)
            ·
              refine ⟨17563255605912171489275053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93670696564864914609466949 17563255605912171489275053)
              ·
                refine ⟨6586220852217064308478145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17563255605912171489275053 6586220852217064308478145)
                ·
                  refine ⟨4939665639162798231358609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586220852217064308478145 4939665639162798231358609)
                  ·
                    refine ⟨3704749229372098673518957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939665639162798231358609 3704749229372098673518957)
                    ·
                      refine ⟨1389280961014537002569609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704749229372098673518957 1389280961014537002569609)
                      ·
                        rfl

theorem cell23_2705615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_2705615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705615 prefixEnd_2705615 := by exact prefixLift 2705615
  have htrace : WordTrace (prefixWord ++ tailWord_2705615) baseStart_2705615 baseEnd_2705615 := by
    simpa [prefixWord, tailWord_2705615, baseEnd_2705615] using wordTrace_append hprefix tailTrace_2705615
  have hstable : (prefixWord ++ tailWord_2705615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705615).length < 2 ^ (prefixWord ++ tailWord_2705615).sum := by decide
  have hdescent : baseEnd_2705615 < baseStart_2705615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705639 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 3, 4]
def baseStart_2705639 : Nat := 118140960795 + 2705639 * 2 ^ 59
def prefixEnd_2705639 : Nat := 4983230072969 + 3 ^ 40 * 2705639 * 2
def baseEnd_2705639 : Nat := 463097761516748302889833

theorem tailTrace_2705639 : CollatzResearch.WordTrace tailWord_2705639 prefixEnd_2705639 463097761516748302889833 := by
  unfold tailWord_2705639
  simp only [CollatzResearch.WordTrace]
  refine ⟨98682761444939464197735971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65788507629959642798490647 98682761444939464197735971)
  ·
    refine ⟨148024142167409196296603957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98682761444939464197735971 148024142167409196296603957)
    ·
      refine ⟨13877263328194612152806621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148024142167409196296603957 13877263328194612152806621)
      ·
        refine ⟨5203973748072979557302483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13877263328194612152806621 5203973748072979557302483)
        ·
          refine ⟨7805960622109469335953725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5203973748072979557302483 7805960622109469335953725)
          ·
            refine ⟨2927235233291051000982647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7805960622109469335953725 2927235233291051000982647)
            ·
              refine ⟨4390852849936576501473971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927235233291051000982647 4390852849936576501473971)
              ·
                refine ⟨6586279274904864752210957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390852849936576501473971 6586279274904864752210957)
                ·
                  refine ⟨2469854728089324282079109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6586279274904864752210957 2469854728089324282079109)
                  ·
                    refine ⟨463097761516748302889833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2469854728089324282079109 463097761516748302889833)
                    ·
                      rfl

theorem cell23_2705639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_2705639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705639 prefixEnd_2705639 := by exact prefixLift 2705639
  have htrace : WordTrace (prefixWord ++ tailWord_2705639) baseStart_2705639 baseEnd_2705639 := by
    simpa [prefixWord, tailWord_2705639, baseEnd_2705639] using wordTrace_append hprefix tailTrace_2705639
  have hstable : (prefixWord ++ tailWord_2705639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705639).length < 2 ^ (prefixWord ++ tailWord_2705639).sum := by decide
  have hdescent : baseEnd_2705639 < baseStart_2705639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705665 : List Nat := [1, 2, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_2705665 : Nat := 118140960795 + 2705665 * 2 ^ 59
def prefixEnd_2705665 : Nat := 4983230072969 + 3 ^ 40 * 2705665 * 2
def baseEnd_2705665 : Nat := 463102211682420602314793

theorem tailTrace_2705665 : CollatzResearch.WordTrace tailWord_2705665 prefixEnd_2705665 463102211682420602314793 := by
  unfold tailWord_2705665
  simp only [CollatzResearch.WordTrace]
  refine ⟨98683709742845270638182449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65789139828563513758788299 98683709742845270638182449)
  ·
    refine ⟨74012782307133952978636837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98683709742845270638182449 74012782307133952978636837)
    ·
      refine ⟨13877396682587616183494407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74012782307133952978636837 13877396682587616183494407)
      ·
        refine ⟨20816095023881424275241611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13877396682587616183494407 20816095023881424275241611)
        ·
          refine ⟨31224142535822136412862417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20816095023881424275241611 31224142535822136412862417)
          ·
            refine ⟨23418106901866602309646813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31224142535822136412862417 23418106901866602309646813)
            ·
              refine ⟨8781790088199975866117555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23418106901866602309646813 8781790088199975866117555)
              ·
                refine ⟨13172685132299963799176333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8781790088199975866117555 13172685132299963799176333)
                ·
                  refine ⟨4939756924612486424691125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13172685132299963799176333 4939756924612486424691125)
                  ·
                    refine ⟨463102211682420602314793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4939756924612486424691125 463102211682420602314793)
                    ·
                      rfl

theorem cell23_2705665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_2705665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705665 prefixEnd_2705665 := by exact prefixLift 2705665
  have htrace : WordTrace (prefixWord ++ tailWord_2705665) baseStart_2705665 baseEnd_2705665 := by
    simpa [prefixWord, tailWord_2705665, baseEnd_2705665] using wordTrace_append hprefix tailTrace_2705665
  have hstable : (prefixWord ++ tailWord_2705665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705665).length < 2 ^ (prefixWord ++ tailWord_2705665).sum := by decide
  have hdescent : baseEnd_2705665 < baseStart_2705665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705696 : List Nat := [2, 1, 1, 5, 2, 2, 1, 4, 1, 1, 3]
def baseStart_2705696 : Nat := 118140960795 + 2705696 * 2 ^ 59
def prefixEnd_2705696 : Nat := 4983230072969 + 3 ^ 40 * 2705696 * 2
def baseEnd_2705696 : Nat := 1389322552947551185656737

theorem tailTrace_2705696 : CollatzResearch.WordTrace tailWord_2705696 prefixEnd_2705696 1389322552947551185656737 := by
  unfold tailWord_2705696
  simp only [CollatzResearch.WordTrace]
  refine ⟨49342420202866481466280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65789893603821975288373961 49342420202866481466280471)
  ·
    refine ⟨74013630304299722199420707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49342420202866481466280471 74013630304299722199420707)
    ·
      refine ⟨111020445456449583299131061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74013630304299722199420707 111020445456449583299131061)
      ·
        refine ⟨10408166761542148434293537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111020445456449583299131061 10408166761542148434293537)
        ·
          refine ⟨7806125071156611325720153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10408166761542148434293537 7806125071156611325720153)
          ·
            refine ⟨5854593803367458494290115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806125071156611325720153 5854593803367458494290115)
            ·
              refine ⟨8781890705051187741435173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854593803367458494290115 8781890705051187741435173)
              ·
                refine ⟨1646604507197097701519095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8781890705051187741435173 1646604507197097701519095)
                ·
                  refine ⟨2469906760795646552278643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646604507197097701519095 2469906760795646552278643)
                  ·
                    refine ⟨3704860141193469828417965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2469906760795646552278643 3704860141193469828417965)
                    ·
                      refine ⟨1389322552947551185656737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704860141193469828417965 1389322552947551185656737)
                      ·
                        rfl

theorem cell23_2705696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_2705696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705696 prefixEnd_2705696 := by exact prefixLift 2705696
  have htrace : WordTrace (prefixWord ++ tailWord_2705696) baseStart_2705696 baseEnd_2705696 := by
    simpa [prefixWord, tailWord_2705696, baseEnd_2705696] using wordTrace_append hprefix tailTrace_2705696
  have hstable : (prefixWord ++ tailWord_2705696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705696).length < 2 ^ (prefixWord ++ tailWord_2705696).sum := by decide
  have hdescent : baseEnd_2705696 < baseStart_2705696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705722 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_2705722 : Nat := 118140960795 + 2705722 * 2 ^ 59
def prefixEnd_2705722 : Nat := 4983230072969 + 3 ^ 40 * 2705722 * 2
def baseEnd_2705722 : Nat := 1389335903444568083931617

theorem tailTrace_2705722 : CollatzResearch.WordTrace tailWord_2705722 prefixEnd_2705722 1389335903444568083931617 := by
  unfold tailWord_2705722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24671447175909692343251855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65790525802425846248671613 24671447175909692343251855)
  ·
    refine ⟨37007170763864538514877783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24671447175909692343251855 37007170763864538514877783)
    ·
      refine ⟨55510756145796807772316675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37007170763864538514877783 55510756145796807772316675)
      ·
        refine ⟨83266134218695211658475013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55510756145796807772316675 83266134218695211658475013)
        ·
          refine ⟨15612400166005352185964065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83266134218695211658475013 15612400166005352185964065)
          ·
            refine ⟨11709300124504014139473049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15612400166005352185964065 11709300124504014139473049)
            ·
              refine ⟨8781975093378010604604787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11709300124504014139473049 8781975093378010604604787)
              ·
                refine ⟨13172962640067015906907181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8781975093378010604604787 13172962640067015906907181)
                ·
                  refine ⟨4939860990025130965090193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13172962640067015906907181 4939860990025130965090193)
                  ·
                    refine ⟨3704895742518848223817645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4939860990025130965090193 3704895742518848223817645)
                    ·
                      refine ⟨1389335903444568083931617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3704895742518848223817645 1389335903444568083931617)
                      ·
                        rfl

theorem cell23_2705722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_2705722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705722 prefixEnd_2705722 := by exact prefixLift 2705722
  have htrace : WordTrace (prefixWord ++ tailWord_2705722) baseStart_2705722 baseEnd_2705722 := by
    simpa [prefixWord, tailWord_2705722, baseEnd_2705722] using wordTrace_append hprefix tailTrace_2705722
  have hstable : (prefixWord ++ tailWord_2705722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705722).length < 2 ^ (prefixWord ++ tailWord_2705722).sum := by decide
  have hdescent : baseEnd_2705722 < baseStart_2705722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705736 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_2705736 : Nat := 118140960795 + 2705736 * 2 ^ 59
def prefixEnd_2705736 : Nat := 4983230072969 + 3 ^ 40 * 2705736 * 2
def baseEnd_2705736 : Nat := 1389343092173731029156553

theorem tailTrace_2705736 : CollatzResearch.WordTrace tailWord_2705736 prefixEnd_2705736 1389343092173731029156553 := by
  unfold tailWord_2705736
  simp only [CollatzResearch.WordTrace]
  refine ⟨49343149662794024882008531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65790866217058699842678041 49343149662794024882008531)
  ·
    refine ⟨74014724494191037323012797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49343149662794024882008531 74014724494191037323012797)
    ·
      refine ⟨27755521685321638996129799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74014724494191037323012797 27755521685321638996129799)
      ·
        refine ⟨41633282527982458494194699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27755521685321638996129799 41633282527982458494194699)
        ·
          refine ⟨62449923791973687741292049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41633282527982458494194699 62449923791973687741292049)
          ·
            refine ⟨46837442843980265805969037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62449923791973687741292049 46837442843980265805969037)
            ·
              refine ⟨17564041066492599677238389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46837442843980265805969037 17564041066492599677238389)
              ·
                refine ⟨1646628849983681219741099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17564041066492599677238389 1646628849983681219741099)
                ·
                  refine ⟨2469943274975521829611649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646628849983681219741099 2469943274975521829611649)
                  ·
                    refine ⟨1852457456231641372208737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2469943274975521829611649 1852457456231641372208737)
                    ·
                      refine ⟨1389343092173731029156553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852457456231641372208737 1389343092173731029156553)
                      ·
                        rfl

theorem cell23_2705736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_2705736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705736 prefixEnd_2705736 := by exact prefixLift 2705736
  have htrace : WordTrace (prefixWord ++ tailWord_2705736) baseStart_2705736 baseEnd_2705736 := by
    simpa [prefixWord, tailWord_2705736, baseEnd_2705736] using wordTrace_append hprefix tailTrace_2705736
  have hstable : (prefixWord ++ tailWord_2705736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705736).length < 2 ^ (prefixWord ++ tailWord_2705736).sum := by decide
  have hdescent : baseEnd_2705736 < baseStart_2705736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705814 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2705814 : Nat := 118140960795 + 2705814 * 2 ^ 59
def prefixEnd_2705814 : Nat := 4983230072969 + 3 ^ 40 * 2705814 * 2
def baseEnd_2705814 : Nat := 463127714554927241327065

theorem tailTrace_2705814 : CollatzResearch.WordTrace tailWord_2705814 prefixEnd_2705814 463127714554927241327065 := by
  unfold tailWord_2705814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168071513706591817834781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65792762812870312723570997 6168071513706591817834781)
  ·
    refine ⟨2313026817639971931688043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6168071513706591817834781 2313026817639971931688043)
    ·
      refine ⟨3469540226459957897532065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2313026817639971931688043 3469540226459957897532065)
      ·
        refine ⟨2602155169844968423149049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3469540226459957897532065 2602155169844968423149049)
        ·
          refine ⟨1951616377383726317361787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2602155169844968423149049 1951616377383726317361787)
          ·
            refine ⟨2927424566075589476042681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951616377383726317361787 2927424566075589476042681)
            ·
              refine ⟨2195568424556692107032011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927424566075589476042681 2195568424556692107032011)
              ·
                refine ⟨3293352636835038160548017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195568424556692107032011 3293352636835038160548017)
                ·
                  refine ⟨2470014477626278620411013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293352636835038160548017 2470014477626278620411013)
                  ·
                    refine ⟨463127714554927241327065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470014477626278620411013 463127714554927241327065)
                    ·
                      rfl

theorem cell23_2705814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2705814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705814 prefixEnd_2705814 := by exact prefixLift 2705814
  have htrace : WordTrace (prefixWord ++ tailWord_2705814) baseStart_2705814 baseEnd_2705814 := by
    simpa [prefixWord, tailWord_2705814, baseEnd_2705814] using wordTrace_append hprefix tailTrace_2705814
  have hstable : (prefixWord ++ tailWord_2705814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705814).length < 2 ^ (prefixWord ++ tailWord_2705814).sum := by decide
  have hdescent : baseEnd_2705814 < baseStart_2705814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705860 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_2705860 : Nat := 118140960795 + 2705860 * 2 ^ 59
def prefixEnd_2705860 : Nat := 4983230072969 + 3 ^ 40 * 2705860 * 2
def baseEnd_2705860 : Nat := 1389406763774888544005983

theorem tailTrace_2705860 : CollatzResearch.WordTrace tailWord_2705860 prefixEnd_2705860 1389406763774888544005983 := by
  unfold tailWord_2705860
  simp only [CollatzResearch.WordTrace]
  refine ⟨49345410988569409470765517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65793881318092545961020689 49345410988569409470765517)
  ·
    refine ⟨18504529120713528551537069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49345410988569409470765517 18504529120713528551537069)
    ·
      refine ⟨6939198420267573206826401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18504529120713528551537069 6939198420267573206826401)
      ·
        refine ⟨5204398815200679905119801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6939198420267573206826401 5204398815200679905119801)
        ·
          refine ⟨3903299111400509928839851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5204398815200679905119801 3903299111400509928839851)
          ·
            refine ⟨5854948667100764893259777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903299111400509928839851 5854948667100764893259777)
            ·
              refine ⟨4391211500325573669944833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854948667100764893259777 4391211500325573669944833)
              ·
                refine ⟨3293408625244180252458625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391211500325573669944833 3293408625244180252458625)
                ·
                  refine ⟨2470056468933135189343969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293408625244180252458625 2470056468933135189343969)
                  ·
                    refine ⟨1852542351699851392007977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2470056468933135189343969 1852542351699851392007977)
                    ·
                      refine ⟨1389406763774888544005983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852542351699851392007977 1389406763774888544005983)
                      ·
                        rfl

theorem cell23_2705860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_2705860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705860 prefixEnd_2705860 := by exact prefixLift 2705860
  have htrace : WordTrace (prefixWord ++ tailWord_2705860) baseStart_2705860 baseEnd_2705860 := by
    simpa [prefixWord, tailWord_2705860, baseEnd_2705860] using wordTrace_append hprefix tailTrace_2705860
  have hstable : (prefixWord ++ tailWord_2705860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705860).length < 2 ^ (prefixWord ++ tailWord_2705860).sum := by decide
  have hdescent : baseEnd_2705860 < baseStart_2705860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705882 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_2705882 : Nat := 118140960795 + 2705882 * 2 ^ 59
def prefixEnd_2705882 : Nat := 4983230072969 + 3 ^ 40 * 2705882 * 2
def baseEnd_2705882 : Nat := 1389418060349287457930881

theorem tailTrace_2705882 : CollatzResearch.WordTrace tailWord_2705882 prefixEnd_2705882 1389418060349287457930881 := by
  unfold tailWord_2705882
  simp only [CollatzResearch.WordTrace]
  refine ⟨24672906095764779174707975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65794416255372744465887933 24672906095764779174707975)
  ·
    refine ⟨37009359143647168762061963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24672906095764779174707975 37009359143647168762061963)
    ·
      refine ⟨55514038715470753143092945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37009359143647168762061963 55514038715470753143092945)
      ·
        refine ⟨41635529036603064857319709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55514038715470753143092945 41635529036603064857319709)
        ·
          refine ⟨15613323388726149321494891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41635529036603064857319709 15613323388726149321494891)
          ·
            refine ⟨23419985083089223982242337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15613323388726149321494891 23419985083089223982242337)
            ·
              refine ⟨17564988812316917986681753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23419985083089223982242337 17564988812316917986681753)
              ·
                refine ⟨13173741609237688490011315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17564988812316917986681753 13173741609237688490011315)
                ·
                  refine ⟨19760612413856532735016973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13173741609237688490011315 19760612413856532735016973)
                  ·
                    refine ⟨7410229655196199775631365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19760612413856532735016973 7410229655196199775631365)
                    ·
                      refine ⟨1389418060349287457930881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7410229655196199775631365 1389418060349287457930881)
                      ·
                        rfl

theorem cell23_2705882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_2705882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705882 prefixEnd_2705882 := by exact prefixLift 2705882
  have htrace : WordTrace (prefixWord ++ tailWord_2705882) baseStart_2705882 baseEnd_2705882 := by
    simpa [prefixWord, tailWord_2705882, baseEnd_2705882] using wordTrace_append hprefix tailTrace_2705882
  have hstable : (prefixWord ++ tailWord_2705882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705882).length < 2 ^ (prefixWord ++ tailWord_2705882).sum := by decide
  have hdescent : baseEnd_2705882 < baseStart_2705882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705939 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 6]
def baseStart_2705939 : Nat := 118140960795 + 2705939 * 2 ^ 59
def prefixEnd_2705939 : Nat := 4983230072969 + 3 ^ 40 * 2705939 * 2
def baseEnd_2705939 : Nat := 154383036527399303879791

theorem tailTrace_2705939 : CollatzResearch.WordTrace tailWord_2705939 prefixEnd_2705939 154383036527399303879791 := by
  unfold tailWord_2705939
  simp only [CollatzResearch.WordTrace]
  refine ⟨98693703343852615433656871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65795802229235076955771247 98693703343852615433656871)
  ·
    refine ⟨148040555015778923150485307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98693703343852615433656871 148040555015778923150485307)
    ·
      refine ⟨222060832523668384725727961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148040555015778923150485307 222060832523668384725727961)
      ·
        refine ⟨166545624392751288544295971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222060832523668384725727961 166545624392751288544295971)
        ·
          refine ⟨249818436589126932816443957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166545624392751288544295971 249818436589126932816443957)
          ·
            refine ⟨23420478430230649951541621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 249818436589126932816443957 23420478430230649951541621)
            ·
              refine ⟨2195669852834123432957027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23420478430230649951541621 2195669852834123432957027)
              ·
                refine ⟨3293504779251185149435541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195669852834123432957027 3293504779251185149435541)
                ·
                  refine ⟨154383036527399303879791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293504779251185149435541 154383036527399303879791)
                  ·
                    rfl

theorem cell23_2705939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 6].length) (baseStart_2705939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705939 prefixEnd_2705939 := by exact prefixLift 2705939
  have htrace : WordTrace (prefixWord ++ tailWord_2705939) baseStart_2705939 baseEnd_2705939 := by
    simpa [prefixWord, tailWord_2705939, baseEnd_2705939] using wordTrace_append hprefix tailTrace_2705939
  have hstable : (prefixWord ++ tailWord_2705939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705939).length < 2 ^ (prefixWord ++ tailWord_2705939).sum := by decide
  have hdescent : baseEnd_2705939 < baseStart_2705939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705960 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 1, 4]
def baseStart_2705960 : Nat := 118140960795 + 2705960 * 2 ^ 59
def prefixEnd_2705960 : Nat := 4983230072969 + 3 ^ 40 * 2705960 * 2
def baseEnd_2705960 : Nat := 463152703946779384251841

theorem tailTrace_2705960 : CollatzResearch.WordTrace tailWord_2705960 prefixEnd_2705960 463152703946779384251841 := by
  unfold tailWord_2705960
  simp only [CollatzResearch.WordTrace]
  refine ⟨49347234638388268010085667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65796312851184357346780889 49347234638388268010085667)
  ·
    refine ⟨74020851957582402015128501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49347234638388268010085667 74020851957582402015128501)
    ·
      refine ⟨6939454871023350188918297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74020851957582402015128501 6939454871023350188918297)
      ·
        refine ⟨5204591153267512641688723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6939454871023350188918297 5204591153267512641688723)
        ·
          refine ⟨7806886729901268962533085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204591153267512641688723 7806886729901268962533085)
          ·
            refine ⟨2927582523712975860949907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7806886729901268962533085 2927582523712975860949907)
            ·
              refine ⟨4391373785569463791424861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927582523712975860949907 4391373785569463791424861)
              ·
                refine ⟨1646765169588548921784323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4391373785569463791424861 1646765169588548921784323)
                ·
                  refine ⟨2470147754382823382676485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646765169588548921784323 2470147754382823382676485)
                  ·
                    refine ⟨463152703946779384251841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470147754382823382676485 463152703946779384251841)
                    ·
                      rfl

theorem cell23_2705960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_2705960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705960 prefixEnd_2705960 := by exact prefixLift 2705960
  have htrace : WordTrace (prefixWord ++ tailWord_2705960) baseStart_2705960 baseEnd_2705960 := by
    simpa [prefixWord, tailWord_2705960, baseEnd_2705960] using wordTrace_append hprefix tailTrace_2705960
  have hstable : (prefixWord ++ tailWord_2705960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705960).length < 2 ^ (prefixWord ++ tailWord_2705960).sum := by decide
  have hdescent : baseEnd_2705960 < baseStart_2705960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705969 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_2705969 : Nat := 118140960795 + 2705969 * 2 ^ 59
def prefixEnd_2705969 : Nat := 4983230072969 + 3 ^ 40 * 2705969 * 2
def baseEnd_2705969 : Nat := 463154244388742872514327

theorem tailTrace_2705969 : CollatzResearch.WordTrace tailWord_2705969 prefixEnd_2705969 463154244388742872514327 := by
  unfold tailWord_2705969
  simp only [CollatzResearch.WordTrace]
  refine ⟨98694797533743930557248961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65796531689162620371499307 98694797533743930557248961)
  ·
    refine ⟨74021098150307947917936721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98694797533743930557248961 74021098150307947917936721)
    ·
      refine ⟨55515823612730960938452541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74021098150307947917936721 55515823612730960938452541)
      ·
        refine ⟨20818433854774110351919703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55515823612730960938452541 20818433854774110351919703)
        ·
          refine ⟨31227650782161165527879555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20818433854774110351919703 31227650782161165527879555)
          ·
            refine ⟨46841476173241748291819333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31227650782161165527879555 46841476173241748291819333)
            ·
              refine ⟨8782776782482827804716125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46841476173241748291819333 8782776782482827804716125)
              ·
                refine ⟨3293541293431060426768547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8782776782482827804716125 3293541293431060426768547)
                ·
                  refine ⟨4940311940146590640152821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293541293431060426768547 4940311940146590640152821)
                  ·
                    refine ⟨463154244388742872514327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4940311940146590640152821 463154244388742872514327)
                    ·
                      rfl

theorem cell23_2705969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_2705969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705969 prefixEnd_2705969 := by exact prefixLift 2705969
  have htrace : WordTrace (prefixWord ++ tailWord_2705969) baseStart_2705969 baseEnd_2705969 := by
    simpa [prefixWord, tailWord_2705969, baseEnd_2705969] using wordTrace_append hprefix tailTrace_2705969
  have hstable : (prefixWord ++ tailWord_2705969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705969).length < 2 ^ (prefixWord ++ tailWord_2705969).sum := by decide
  have hdescent : baseEnd_2705969 < baseStart_2705969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705976 : List Nat := [2, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_2705976 : Nat := 118140960795 + 2705976 * 2 ^ 59
def prefixEnd_2705976 : Nat := 4983230072969 + 3 ^ 40 * 2705976 * 2
def baseEnd_2705976 : Nat := 1389466327530810090155449

theorem tailTrace_2705976 : CollatzResearch.WordTrace tailWord_2705976 prefixEnd_2705976 1389466327530810090155449 := by
  unfold tailWord_2705976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49347526422359285376376891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65796701896479047168502521 49347526422359285376376891)
  ·
    refine ⟨74021289633538928064565337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49347526422359285376376891 74021289633538928064565337)
    ·
      refine ⟨55515967225154196048424003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74021289633538928064565337 55515967225154196048424003)
      ·
        refine ⟨83273950837731294072636005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55515967225154196048424003 83273950837731294072636005)
        ·
          refine ⟨15613865782074617638619251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83273950837731294072636005 15613865782074617638619251)
          ·
            refine ⟨23420798673111926457928877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15613865782074617638619251 23420798673111926457928877)
            ·
              refine ⟨8782799502416972421723329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23420798673111926457928877 8782799502416972421723329)
              ·
                refine ⟨6587099626812729316292497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8782799502416972421723329 6587099626812729316292497)
                ·
                  refine ⟨4940324720109546987219373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6587099626812729316292497 4940324720109546987219373)
                  ·
                    refine ⟨1852621770041080120207265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4940324720109546987219373 1852621770041080120207265)
                    ·
                      refine ⟨1389466327530810090155449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852621770041080120207265 1389466327530810090155449)
                      ·
                        rfl

theorem cell23_2705976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_2705976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705976 prefixEnd_2705976 := by exact prefixLift 2705976
  have htrace : WordTrace (prefixWord ++ tailWord_2705976) baseStart_2705976 baseEnd_2705976 := by
    simpa [prefixWord, tailWord_2705976, baseEnd_2705976] using wordTrace_append hprefix tailTrace_2705976
  have hstable : (prefixWord ++ tailWord_2705976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705976).length < 2 ^ (prefixWord ++ tailWord_2705976).sum := by decide
  have hdescent : baseEnd_2705976 < baseStart_2705976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2705990 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2705990 : Nat := 118140960795 + 2705990 * 2 ^ 59
def prefixEnd_2705990 : Nat := 4983230072969 + 3 ^ 40 * 2705990 * 2
def baseEnd_2705990 : Nat := 154385946251108115042265

theorem tailTrace_2705990 : CollatzResearch.WordTrace tailWord_2705990 prefixEnd_2705990 154385946251108115042265 := by
  unfold tailWord_2705990
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084236358333370348242607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65797042311111900762508949 3084236358333370348242607)
  ·
    refine ⟨4626354537500055522363911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3084236358333370348242607 4626354537500055522363911)
    ·
      refine ⟨6939531806250083283545867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626354537500055522363911 6939531806250083283545867)
      ·
        refine ⟨10409297709375124925318801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6939531806250083283545867 10409297709375124925318801)
        ·
          refine ⟨7806973282031343693989101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10409297709375124925318801 7806973282031343693989101)
          ·
            refine ⟨2927614980761753885245913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7806973282031343693989101 2927614980761753885245913)
            ·
              refine ⟨2195711235571315413934435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927614980761753885245913 2195711235571315413934435)
              ·
                refine ⟨3293566853356973120901653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195711235571315413934435 3293566853356973120901653)
                ·
                  refine ⟨154385946251108115042265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293566853356973120901653 154385946251108115042265)
                  ·
                    rfl

theorem cell23_2705990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2705990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2705990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2705990 prefixEnd_2705990 := by exact prefixLift 2705990
  have htrace : WordTrace (prefixWord ++ tailWord_2705990) baseStart_2705990 baseEnd_2705990 := by
    simpa [prefixWord, tailWord_2705990, baseEnd_2705990] using wordTrace_append hprefix tailTrace_2705990
  have hstable : (prefixWord ++ tailWord_2705990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2705990).length < 2 ^ (prefixWord ++ tailWord_2705990).sum := by decide
  have hdescent : baseEnd_2705990 < baseStart_2705990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2705990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706019 : List Nat := [1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4]
def baseStart_2706019 : Nat := 118140960795 + 2706019 * 2 ^ 59
def prefixEnd_2706019 : Nat := 4983230072969 + 3 ^ 40 * 2706019 * 2
def baseEnd_2706019 : Nat := 1389488407198953421917751

theorem tailTrace_2706019 : CollatzResearch.WordTrace tailWord_2706019 prefixEnd_2706019 1389488407198953421917751 := by
  unfold tailWord_2706019
  simp only [CollatzResearch.WordTrace]
  refine ⟨98696621183562789096569111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65797747455708526064379407 98696621183562789096569111)
  ·
    refine ⟨148044931775344183644853667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98696621183562789096569111 148044931775344183644853667)
    ·
      refine ⟨222067397663016275467280501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148044931775344183644853667 222067397663016275467280501)
      ·
        refine ⟨20818818530907775825057547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222067397663016275467280501 20818818530907775825057547)
        ·
          refine ⟨31228227796361663737586321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20818818530907775825057547 31228227796361663737586321)
          ·
            refine ⟨23421170847271247803189741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31228227796361663737586321 23421170847271247803189741)
            ·
              refine ⟨8782939067726717926196153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23421170847271247803189741 8782939067726717926196153)
              ·
                refine ⟨6587204300795038444647115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8782939067726717926196153 6587204300795038444647115)
                ·
                  refine ⟨9880806451192557666970673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587204300795038444647115 9880806451192557666970673)
                  ·
                    refine ⟨7410604838394418250228005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9880806451192557666970673 7410604838394418250228005)
                    ·
                      refine ⟨1389488407198953421917751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7410604838394418250228005 1389488407198953421917751)
                      ·
                        rfl

theorem cell23_2706019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_2706019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706019 prefixEnd_2706019 := by exact prefixLift 2706019
  have htrace : WordTrace (prefixWord ++ tailWord_2706019) baseStart_2706019 baseEnd_2706019 := by
    simpa [prefixWord, tailWord_2706019, baseEnd_2706019] using wordTrace_append hprefix tailTrace_2706019
  have hstable : (prefixWord ++ tailWord_2706019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706019).length < 2 ^ (prefixWord ++ tailWord_2706019).sum := by decide
  have hdescent : baseEnd_2706019 < baseStart_2706019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706034 : List Nat := [3, 2, 1, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_2706034 : Nat := 118140960795 + 2706034 * 2 ^ 59
def prefixEnd_2706034 : Nat := 4983230072969 + 3 ^ 40 * 2706034 * 2
def baseEnd_2706034 : Nat := 1389496109408770863230183

theorem tailTrace_2706034 : CollatzResearch.WordTrace tailWord_2706034 prefixEnd_2706034 1389496109408770863230183 := by
  unfold tailWord_2706034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24674292069627111664591289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65798112185672297772243437 24674292069627111664591289)
  ·
    refine ⟨18505719052220333748443467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24674292069627111664591289 18505719052220333748443467)
    ·
      refine ⟨27758578578330500622665201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18505719052220333748443467 27758578578330500622665201)
      ·
        refine ⟨20818933933747875466998901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27758578578330500622665201 20818933933747875466998901)
        ·
          refine ⟨1951775056288863325031147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20818933933747875466998901 1951775056288863325031147)
          ·
            refine ⟨2927662584433294987546721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951775056288863325031147 2927662584433294987546721)
            ·
              refine ⟨2195746938324971240660041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927662584433294987546721 2195746938324971240660041)
              ·
                refine ⟨1646810203743728430495031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195746938324971240660041 1646810203743728430495031)
                ·
                  refine ⟨2470215305615592645742547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646810203743728430495031 2470215305615592645742547)
                  ·
                    refine ⟨3705322958423388968613821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470215305615592645742547 3705322958423388968613821)
                    ·
                      refine ⟨1389496109408770863230183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3705322958423388968613821 1389496109408770863230183)
                      ·
                        rfl

theorem cell23_2706034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_2706034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706034 prefixEnd_2706034 := by exact prefixLift 2706034
  have htrace : WordTrace (prefixWord ++ tailWord_2706034) baseStart_2706034 baseEnd_2706034 := by
    simpa [prefixWord, tailWord_2706034, baseEnd_2706034] using wordTrace_append hprefix tailTrace_2706034
  have hstable : (prefixWord ++ tailWord_2706034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706034).length < 2 ^ (prefixWord ++ tailWord_2706034).sum := by decide
  have hdescent : baseEnd_2706034 < baseStart_2706034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706074 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2706074 : Nat := 118140960795 + 2706074 * 2 ^ 59
def prefixEnd_2706074 : Nat := 4983230072969 + 3 ^ 40 * 2706074 * 2
def baseEnd_2706074 : Nat := 1389516648634950706729999

theorem tailTrace_2706074 : CollatzResearch.WordTrace tailWord_2706074 prefixEnd_2706074 1389516648634950706729999 := by
  unfold tailWord_2706074
  simp only [CollatzResearch.WordTrace]
  refine ⟨24674656799590883372455319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65799084798909022326547517 24674656799590883372455319)
  ·
    refine ⟨37011985199386325058682979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24674656799590883372455319 37011985199386325058682979)
    ·
      refine ⟨55517977799079487588024469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37011985199386325058682979 55517977799079487588024469)
      ·
        refine ⟨2602405209331850980688647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55517977799079487588024469 2602405209331850980688647)
        ·
          refine ⟨3903607813997776471032971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602405209331850980688647 3903607813997776471032971)
          ·
            refine ⟨5855411720996664706549457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903607813997776471032971 5855411720996664706549457)
            ·
              refine ⟨4391558790747498529912093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855411720996664706549457 4391558790747498529912093)
              ·
                refine ⟨1646834546530311948717035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4391558790747498529912093 1646834546530311948717035)
                ·
                  refine ⟨2470251819795467923075553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646834546530311948717035 2470251819795467923075553)
                  ·
                    refine ⟨1852688864846600942306665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2470251819795467923075553 1852688864846600942306665)
                    ·
                      refine ⟨1389516648634950706729999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852688864846600942306665 1389516648634950706729999)
                      ·
                        rfl

theorem cell23_2706074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2706074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706074 prefixEnd_2706074 := by exact prefixLift 2706074
  have htrace : WordTrace (prefixWord ++ tailWord_2706074) baseStart_2706074 baseEnd_2706074 := by
    simpa [prefixWord, tailWord_2706074, baseEnd_2706074] using wordTrace_append hprefix tailTrace_2706074
  have hstable : (prefixWord ++ tailWord_2706074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706074).length < 2 ^ (prefixWord ++ tailWord_2706074).sum := by decide
  have hdescent : baseEnd_2706074 < baseStart_2706074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706133 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2706133 : Nat := 118140960795 + 2706133 * 2 ^ 59
def prefixEnd_2706133 : Nat := 4983230072969 + 3 ^ 40 * 2706133 * 2
def baseEnd_2706133 : Nat := 1389546943993565975892227

theorem tailTrace_2706133 : CollatzResearch.WordTrace tailWord_2706133 prefixEnd_2706133 1389546943993565975892227 := by
  unfold tailWord_2706133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98700779105149786566219053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65800519403433191044146035 98700779105149786566219053)
  ·
    refine ⟨37012792164431169962332145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98700779105149786566219053 37012792164431169962332145)
    ·
      refine ⟨27759594123323377471749109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37012792164431169962332145 27759594123323377471749109)
      ·
        refine ⟨2602461949061566637976479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27759594123323377471749109 2602461949061566637976479)
        ·
          refine ⟨3903692923592349956964719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602461949061566637976479 3903692923592349956964719)
          ·
            refine ⟨5855539385388524935447079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903692923592349956964719 5855539385388524935447079)
            ·
              refine ⟨8783309078082787403170619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5855539385388524935447079 8783309078082787403170619)
              ·
                refine ⟨13174963617124181104755929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783309078082787403170619 13174963617124181104755929)
                ·
                  refine ⟨9881222712843135828566947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13174963617124181104755929 9881222712843135828566947)
                  ·
                    refine ⟨14821834069264703742850421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9881222712843135828566947 14821834069264703742850421)
                    ·
                      refine ⟨1389546943993565975892227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14821834069264703742850421 1389546943993565975892227)
                      ·
                        rfl

theorem cell23_2706133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2706133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706133 prefixEnd_2706133 := by exact prefixLift 2706133
  have htrace : WordTrace (prefixWord ++ tailWord_2706133) baseStart_2706133 baseEnd_2706133 := by
    simpa [prefixWord, tailWord_2706133, baseEnd_2706133] using wordTrace_append hprefix tailTrace_2706133
  have hstable : (prefixWord ++ tailWord_2706133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706133).length < 2 ^ (prefixWord ++ tailWord_2706133).sum := by decide
  have hdescent : baseEnd_2706133 < baseStart_2706133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706156 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_2706156 : Nat := 118140960795 + 2706156 * 2 ^ 59
def prefixEnd_2706156 : Nat := 4983230072969 + 3 ^ 40 * 2706156 * 2
def baseEnd_2706156 : Nat := 1389558754048619385904621

theorem tailTrace_2706156 : CollatzResearch.WordTrace tailWord_2706156 prefixEnd_2706156 1389558754048619385904621 := by
  unfold tailWord_2706156
  simp only [CollatzResearch.WordTrace]
  refine ⟨49350808992033230747153161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65801078656044307662870881 49350808992033230747153161)
  ·
    refine ⟨37013106744024923060364871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49350808992033230747153161 37013106744024923060364871)
    ·
      refine ⟨55519660116037384590547307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37013106744024923060364871 55519660116037384590547307)
      ·
        refine ⟨83279490174056076885820961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55519660116037384590547307 83279490174056076885820961)
        ·
          refine ⟨62459617630542057664365721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83279490174056076885820961 62459617630542057664365721)
          ·
            refine ⟨46844713222906543248274291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62459617630542057664365721 46844713222906543248274291)
            ·
              refine ⟨70267069834359814872411437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46844713222906543248274291 70267069834359814872411437)
              ·
                refine ⟨26350151187884930577154289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70267069834359814872411437 26350151187884930577154289)
                ·
                  refine ⟨19762613390913697932865717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26350151187884930577154289 19762613390913697932865717)
                  ·
                    refine ⟨1852745005398159181206161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19762613390913697932865717 1852745005398159181206161)
                    ·
                      refine ⟨1389558754048619385904621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852745005398159181206161 1389558754048619385904621)
                      ·
                        rfl

theorem cell23_2706156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_2706156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706156 prefixEnd_2706156 := by exact prefixLift 2706156
  have htrace : WordTrace (prefixWord ++ tailWord_2706156) baseStart_2706156 baseEnd_2706156 := by
    simpa [prefixWord, tailWord_2706156, baseEnd_2706156] using wordTrace_append hprefix tailTrace_2706156
  have hstable : (prefixWord ++ tailWord_2706156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706156).length < 2 ^ (prefixWord ++ tailWord_2706156).sum := by decide
  have hdescent : baseEnd_2706156 < baseStart_2706156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706159 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_2706159 : Nat := 118140960795 + 2706159 * 2 ^ 59
def prefixEnd_2706159 : Nat := 4983230072969 + 3 ^ 40 * 2706159 * 2
def baseEnd_2706159 : Nat := 1389560294490582874167107

theorem tailTrace_2706159 : CollatzResearch.WordTrace tailWord_2706159 prefixEnd_2706159 1389560294490582874167107 := by
  unfold tailWord_2706159
  simp only [CollatzResearch.WordTrace]
  refine ⟨98701727403055593006665531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65801151602037062004443687 98701727403055593006665531)
  ·
    refine ⟨148052591104583389509998297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98701727403055593006665531 148052591104583389509998297)
    ·
      refine ⟨111039443328437542132498723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148052591104583389509998297 111039443328437542132498723)
      ·
        refine ⟨166559164992656313198748085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111039443328437542132498723 166559164992656313198748085)
        ·
          refine ⟨15614921718061529362382633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166559164992656313198748085 15614921718061529362382633)
          ·
            refine ⟨11711191288546147021786975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15614921718061529362382633 11711191288546147021786975)
            ·
              refine ⟨17566786932819220532680463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711191288546147021786975 17566786932819220532680463)
              ·
                refine ⟨26350180399228830799020695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17566786932819220532680463 26350180399228830799020695)
                ·
                  refine ⟨39525270598843246198531043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26350180399228830799020695 39525270598843246198531043)
                  ·
                    refine ⟨59287905898264869297796565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39525270598843246198531043 59287905898264869297796565)
                    ·
                      refine ⟨1389560294490582874167107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59287905898264869297796565 1389560294490582874167107)
                      ·
                        rfl

theorem cell23_2706159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_2706159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706159 prefixEnd_2706159 := by exact prefixLift 2706159
  have htrace : WordTrace (prefixWord ++ tailWord_2706159) baseStart_2706159 baseEnd_2706159 := by
    simpa [prefixWord, tailWord_2706159, baseEnd_2706159] using wordTrace_append hprefix tailTrace_2706159
  have hstable : (prefixWord ++ tailWord_2706159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706159).length < 2 ^ (prefixWord ++ tailWord_2706159).sum := by decide
  have hdescent : baseEnd_2706159 < baseStart_2706159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706166 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_2706166 : Nat := 118140960795 + 2706166 * 2 ^ 59
def prefixEnd_2706166 : Nat := 4983230072969 + 3 ^ 40 * 2706166 * 2
def baseEnd_2706166 : Nat := 463187962951721448926525

theorem tailTrace_2706166 : CollatzResearch.WordTrace tailWord_2706166 prefixEnd_2706166 463187962951721448926525 := by
  unfold tailWord_2706166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168873919626889575135647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65801321809353488801446901 6168873919626889575135647)
  ·
    refine ⟨9253310879440334362703471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6168873919626889575135647 9253310879440334362703471)
    ·
      refine ⟨13879966319160501544055207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253310879440334362703471 13879966319160501544055207)
      ·
        refine ⟨20819949478740752316082811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13879966319160501544055207 20819949478740752316082811)
        ·
          refine ⟨31229924218111128474124217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20819949478740752316082811 31229924218111128474124217)
          ·
            refine ⟨23422443163583346355593163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31229924218111128474124217 23422443163583346355593163)
            ·
              refine ⟨35133664745375019533389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23422443163583346355593163 35133664745375019533389745)
              ·
                refine ⟨26350248559031264650042309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35133664745375019533389745 26350248559031264650042309)
                ·
                  refine ⟨4940671604818362121882933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26350248559031264650042309 4940671604818362121882933)
                  ·
                    refine ⟨463187962951721448926525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4940671604818362121882933 463187962951721448926525)
                    ·
                      rfl

theorem cell23_2706166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_2706166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706166 prefixEnd_2706166 := by exact prefixLift 2706166
  have htrace : WordTrace (prefixWord ++ tailWord_2706166) baseStart_2706166 baseEnd_2706166 := by
    simpa [prefixWord, tailWord_2706166, baseEnd_2706166] using wordTrace_append hprefix tailTrace_2706166
  have hstable : (prefixWord ++ tailWord_2706166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706166).length < 2 ^ (prefixWord ++ tailWord_2706166).sum := by decide
  have hdescent : baseEnd_2706166 < baseStart_2706166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706169 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_2706169 : Nat := 118140960795 + 2706169 * 2 ^ 59
def prefixEnd_2706169 : Nat := 4983230072969 + 3 ^ 40 * 2706169 * 2
def baseEnd_2706169 : Nat := 1389565429297127835042061

theorem tailTrace_2706169 : CollatzResearch.WordTrace tailWord_2706169 prefixEnd_2706169 1389565429297127835042061 := by
  unfold tailWord_2706169
  simp only [CollatzResearch.WordTrace]
  refine ⟨98702092133019364714529561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65801394755346243143019707 98702092133019364714529561)
  ·
    refine ⟨74026569099764523535897171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98702092133019364714529561 74026569099764523535897171)
    ·
      refine ⟨111039853649646785303845757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74026569099764523535897171 111039853649646785303845757)
      ·
        refine ⟨41639945118617544488942159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111039853649646785303845757 41639945118617544488942159)
        ·
          refine ⟨62459917677926316733413239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41639945118617544488942159 62459917677926316733413239)
          ·
            refine ⟨93689876516889475100119859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62459917677926316733413239 93689876516889475100119859)
            ·
              refine ⟨140534814775334212650179789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93689876516889475100119859 140534814775334212650179789)
              ·
                refine ⟨52700555540750329743817421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140534814775334212650179789 52700555540750329743817421)
                ·
                  refine ⟨19762708327781373653931533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52700555540750329743817421 19762708327781373653931533)
                  ·
                    refine ⟨7411015622918015120224325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19762708327781373653931533 7411015622918015120224325)
                    ·
                      refine ⟨1389565429297127835042061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7411015622918015120224325 1389565429297127835042061)
                      ·
                        rfl

theorem cell23_2706169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_2706169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706169 prefixEnd_2706169 := by exact prefixLift 2706169
  have htrace : WordTrace (prefixWord ++ tailWord_2706169) baseStart_2706169 baseEnd_2706169 := by
    simpa [prefixWord, tailWord_2706169, baseEnd_2706169] using wordTrace_append hprefix tailTrace_2706169
  have hstable : (prefixWord ++ tailWord_2706169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706169).length < 2 ^ (prefixWord ++ tailWord_2706169).sum := by decide
  have hdescent : baseEnd_2706169 < baseStart_2706169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706183 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 2, 5]
def baseStart_2706183 : Nat := 118140960795 + 2706183 * 2 ^ 59
def prefixEnd_2706183 : Nat := 4983230072969 + 3 ^ 40 * 2706183 * 2
def baseEnd_2706183 : Nat := 463190872675430260088999

theorem tailTrace_2706183 : CollatzResearch.WordTrace tailWord_2706183 prefixEnd_2706183 463190872675430260088999 := by
  unfold tailWord_2706183
  simp only [CollatzResearch.WordTrace]
  refine ⟨98702602754968645105539203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65801735169979096737026135 98702602754968645105539203)
  ·
    refine ⟨148053904132452967658308805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98702602754968645105539203 148053904132452967658308805)
    ·
      refine ⟨27760107024834931435932901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148053904132452967658308805 27760107024834931435932901)
      ·
        refine ⟨5205020067156549644237419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27760107024834931435932901 5205020067156549644237419)
        ·
          refine ⟨7807530100734824466356129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205020067156549644237419 7807530100734824466356129)
          ·
            refine ⟨5855647575551118349767097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7807530100734824466356129 5855647575551118349767097)
            ·
              refine ⟨4391735681663338762325323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855647575551118349767097 4391735681663338762325323)
              ·
                refine ⟨6587603522495008143487985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391735681663338762325323 6587603522495008143487985)
                ·
                  refine ⟨4940702641871256107615989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6587603522495008143487985 4940702641871256107615989)
                  ·
                    refine ⟨463190872675430260088999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4940702641871256107615989 463190872675430260088999)
                    ·
                      rfl

theorem cell23_2706183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_2706183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706183 prefixEnd_2706183 := by exact prefixLift 2706183
  have htrace : WordTrace (prefixWord ++ tailWord_2706183) baseStart_2706183 baseEnd_2706183 := by
    simpa [prefixWord, tailWord_2706183, baseEnd_2706183] using wordTrace_append hprefix tailTrace_2706183
  have hstable : (prefixWord ++ tailWord_2706183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706183).length < 2 ^ (prefixWord ++ tailWord_2706183).sum := by decide
  have hdescent : baseEnd_2706183 < baseStart_2706183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706226 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_2706226 : Nat := 118140960795 + 2706226 * 2 ^ 59
def prefixEnd_2706226 : Nat := 4983230072969 + 3 ^ 40 * 2706226 * 2
def baseEnd_2706226 : Nat := 154399410854937123558811

theorem tailTrace_2706226 : CollatzResearch.WordTrace tailWord_2706226 prefixEnd_2706226 154399410854937123558811 := by
  unfold tailWord_2706226
  simp only [CollatzResearch.WordTrace]
  refine ⟨24676042773453215862338633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65802780729208575632903021 24676042773453215862338633)
  ·
    refine ⟨18507032080089911896753975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24676042773453215862338633 18507032080089911896753975)
    ·
      refine ⟨27760548120134867845130963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18507032080089911896753975 27760548120134867845130963)
      ·
        refine ⟨41640822180202301767696445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27760548120134867845130963 41640822180202301767696445)
        ·
          refine ⟨15615308317575863162886167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41640822180202301767696445 15615308317575863162886167)
          ·
            refine ⟨23422962476363794744329251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15615308317575863162886167 23422962476363794744329251)
            ·
              refine ⟨35134443714545692116493877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23422962476363794744329251 35134443714545692116493877)
              ·
                refine ⟨3293854098238658635921301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35134443714545692116493877 3293854098238658635921301)
                ·
                  refine ⟨154399410854937123558811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293854098238658635921301 154399410854937123558811)
                  ·
                    rfl

theorem cell23_2706226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_2706226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706226 prefixEnd_2706226 := by exact prefixLift 2706226
  have htrace : WordTrace (prefixWord ++ tailWord_2706226) baseStart_2706226 baseEnd_2706226 := by
    simpa [prefixWord, tailWord_2706226, baseEnd_2706226] using wordTrace_append hprefix tailTrace_2706226
  have hstable : (prefixWord ++ tailWord_2706226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706226).length < 2 ^ (prefixWord ++ tailWord_2706226).sum := by decide
  have hdescent : baseEnd_2706226 < baseStart_2706226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706237 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2706237 : Nat := 118140960795 + 2706237 * 2 ^ 59
def prefixEnd_2706237 : Nat := 4983230072969 + 3 ^ 40 * 2706237 * 2
def baseEnd_2706237 : Nat := 1389600345981633568991749

theorem tailTrace_2706237 : CollatzResearch.WordTrace tailWord_2706237 prefixEnd_2706237 1389600345981633568991749 := by
  unfold tailWord_2706237
  simp only [CollatzResearch.WordTrace]
  refine ⟨98704572296773012328004965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65803048197848674885336643 98704572296773012328004965)
  ·
    refine ⟨18507107305644939811500931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98704572296773012328004965 18507107305644939811500931)
    ·
      refine ⟨27760660958467409717251397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18507107305644939811500931 27760660958467409717251397)
      ·
        refine ⟨5205123929712639321984637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27760660958467409717251397 5205123929712639321984637)
        ·
          refine ⟨1951921473642239745744239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5205123929712639321984637 1951921473642239745744239)
          ·
            refine ⟨2927882210463359618616359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951921473642239745744239 2927882210463359618616359)
            ·
              refine ⟨4391823315695039427924539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927882210463359618616359 4391823315695039427924539)
              ·
                refine ⟨6587734973542559141886809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391823315695039427924539 6587734973542559141886809)
                ·
                  refine ⟨4940801230156919356415107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6587734973542559141886809 4940801230156919356415107)
                  ·
                    refine ⟨7411201845235379034622661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4940801230156919356415107 7411201845235379034622661)
                    ·
                      refine ⟨1389600345981633568991749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7411201845235379034622661 1389600345981633568991749)
                      ·
                        rfl

theorem cell23_2706237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2706237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706237 prefixEnd_2706237 := by exact prefixLift 2706237
  have htrace : WordTrace (prefixWord ++ tailWord_2706237) baseStart_2706237 baseEnd_2706237 := by
    simpa [prefixWord, tailWord_2706237, baseEnd_2706237] using wordTrace_append hprefix tailTrace_2706237
  have hstable : (prefixWord ++ tailWord_2706237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706237).length < 2 ^ (prefixWord ++ tailWord_2706237).sum := by decide
  have hdescent : baseEnd_2706237 < baseStart_2706237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706260 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2706260 : Nat := 118140960795 + 2706260 * 2 ^ 59
def prefixEnd_2706260 : Nat := 4983230072969 + 3 ^ 40 * 2706260 * 2
def baseEnd_2706260 : Nat := 154401350670742997667127

theorem tailTrace_2706260 : CollatzResearch.WordTrace tailWord_2706260 prefixEnd_2706260 154401350670742997667127 := by
  unfold tailWord_2706260
  simp only [CollatzResearch.WordTrace]
  refine ⟨49352705587844843628046117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65803607450459791504061489 49352705587844843628046117)
  ·
    refine ⟨9253632297720908180258647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49352705587844843628046117 9253632297720908180258647)
    ·
      refine ⟨13880448446581362270387971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253632297720908180258647 13880448446581362270387971)
      ·
        refine ⟨20820672669872043405581957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880448446581362270387971 20820672669872043405581957)
        ·
          refine ⟨3903876125601008138546617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20820672669872043405581957 3903876125601008138546617)
          ·
            refine ⟨2927907094200756103909963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3903876125601008138546617 2927907094200756103909963)
            ·
              refine ⟨4391860641301134155864945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927907094200756103909963 4391860641301134155864945)
              ·
                refine ⟨3293895480975850616898709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391860641301134155864945 3293895480975850616898709)
                ·
                  refine ⟨154401350670742997667127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3293895480975850616898709 154401350670742997667127)
                  ·
                    rfl

theorem cell23_2706260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2706260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706260 prefixEnd_2706260 := by exact prefixLift 2706260
  have htrace : WordTrace (prefixWord ++ tailWord_2706260) baseStart_2706260 baseEnd_2706260 := by
    simpa [prefixWord, tailWord_2706260, baseEnd_2706260] using wordTrace_append hprefix tailTrace_2706260
  have hstable : (prefixWord ++ tailWord_2706260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706260).length < 2 ^ (prefixWord ++ tailWord_2706260).sum := by decide
  have hdescent : baseEnd_2706260 < baseStart_2706260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706313 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_2706313 : Nat := 118140960795 + 2706313 * 2 ^ 59
def prefixEnd_2706313 : Nat := 4983230072969 + 3 ^ 40 * 2706313 * 2
def baseEnd_2706313 : Nat := 1389639370511375271641399

theorem tailTrace_2706313 : CollatzResearch.WordTrace tailWord_2706313 prefixEnd_2706313 1389639370511375271641399 := by
  unfold tailWord_2706313
  simp only [CollatzResearch.WordTrace]
  refine ⟨98707344244497677307771593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65804896162998451538514395 98707344244497677307771593)
  ·
    refine ⟨74030508183373257980828695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98707344244497677307771593 74030508183373257980828695)
    ·
      refine ⟨111045762275059886971243043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74030508183373257980828695 111045762275059886971243043)
      ·
        refine ⟨166568643412589830456864565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111045762275059886971243043 166568643412589830456864565)
        ·
          refine ⟨15615810319930296605331053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166568643412589830456864565 15615810319930296605331053)
          ·
            refine ⟨5855928869973861226999145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15615810319930296605331053 5855928869973861226999145)
            ·
              refine ⟨4391946652480395920249359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855928869973861226999145 4391946652480395920249359)
              ·
                refine ⟨6587919978720593880374039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4391946652480395920249359 6587919978720593880374039)
                ·
                  refine ⟨9881879968080890820561059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6587919978720593880374039 9881879968080890820561059)
                  ·
                    refine ⟨14822819952121336230841589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9881879968080890820561059 14822819952121336230841589)
                    ·
                      refine ⟨1389639370511375271641399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14822819952121336230841589 1389639370511375271641399)
                      ·
                        rfl

theorem cell23_2706313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_2706313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706313 prefixEnd_2706313 := by exact prefixLift 2706313
  have htrace : WordTrace (prefixWord ++ tailWord_2706313) baseStart_2706313 baseEnd_2706313 := by
    simpa [prefixWord, tailWord_2706313, baseEnd_2706313] using wordTrace_append hprefix tailTrace_2706313
  have hstable : (prefixWord ++ tailWord_2706313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706313).length < 2 ^ (prefixWord ++ tailWord_2706313).sum := by decide
  have hdescent : baseEnd_2706313 < baseStart_2706313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706337 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2706337 : Nat := 118140960795 + 2706337 * 2 ^ 59
def prefixEnd_2706337 : Nat := 4983230072969 + 3 ^ 40 * 2706337 * 2
def baseEnd_2706337 : Nat := 463217231349027725913763

theorem tailTrace_2706337 : CollatzResearch.WordTrace tailWord_2706337 prefixEnd_2706337 463217231349027725913763 := by
  unfold tailWord_2706337
  simp only [CollatzResearch.WordTrace]
  refine ⟨98708219596410729406645265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65805479730940486271096843 98708219596410729406645265)
  ·
    refine ⟨74031164697308047054983949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98708219596410729406645265 74031164697308047054983949)
    ·
      refine ⟨27761686761490517645618981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74031164697308047054983949 27761686761490517645618981)
      ·
        refine ⟨5205316267779472058553559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27761686761490517645618981 5205316267779472058553559)
        ·
          refine ⟨7807974401669208087830339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5205316267779472058553559 7807974401669208087830339)
          ·
            refine ⟨11711961602503812131745509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807974401669208087830339 11711961602503812131745509)
            ·
              refine ⟨2195992800469464774702283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11711961602503812131745509 2195992800469464774702283)
              ·
                refine ⟨3293989200704197162053425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195992800469464774702283 3293989200704197162053425)
                ·
                  refine ⟨2470491900528147871540069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293989200704197162053425 2470491900528147871540069)
                  ·
                    refine ⟨463217231349027725913763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470491900528147871540069 463217231349027725913763)
                    ·
                      rfl

theorem cell23_2706337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2706337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706337 prefixEnd_2706337 := by exact prefixLift 2706337
  have htrace : WordTrace (prefixWord ++ tailWord_2706337) baseStart_2706337 baseEnd_2706337 := by
    simpa [prefixWord, tailWord_2706337, baseEnd_2706337] using wordTrace_append hprefix tailTrace_2706337
  have hstable : (prefixWord ++ tailWord_2706337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706337).length < 2 ^ (prefixWord ++ tailWord_2706337).sum := by decide
  have hdescent : baseEnd_2706337 < baseStart_2706337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706393 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_2706393 : Nat := 118140960795 + 2706393 * 2 ^ 59
def prefixEnd_2706393 : Nat := 4983230072969 + 3 ^ 40 * 2706393 * 2
def baseEnd_2706393 : Nat := 463226816321244986213677

theorem tailTrace_2706393 : CollatzResearch.WordTrace tailWord_2706393 prefixEnd_2706393 463226816321244986213677 := by
  unfold tailWord_2706393
  simp only [CollatzResearch.WordTrace]
  refine ⟨98710262084207850970683833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65806841389471900647122555 98710262084207850970683833)
  ·
    refine ⟨74032696563155888228012875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98710262084207850970683833 74032696563155888228012875)
    ·
      refine ⟨111049044844733832342019313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74032696563155888228012875 111049044844733832342019313)
      ·
        refine ⟨83286783633550374256514485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111049044844733832342019313 83286783633550374256514485)
        ·
          refine ⟨7808135965645347586548233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83286783633550374256514485 7808135965645347586548233)
          ·
            refine ⟨5856101974234010689911175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7808135965645347586548233 5856101974234010689911175)
            ·
              refine ⟨8784152961351016034866763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856101974234010689911175 8784152961351016034866763)
              ·
                refine ⟨13176229442026524052300145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8784152961351016034866763 13176229442026524052300145)
                ·
                  refine ⟨9882172081519893039225109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13176229442026524052300145 9882172081519893039225109)
                  ·
                    refine ⟨463226816321244986213677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9882172081519893039225109 463226816321244986213677)
                    ·
                      rfl

theorem cell23_2706393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_2706393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706393 prefixEnd_2706393 := by exact prefixLift 2706393
  have htrace : WordTrace (prefixWord ++ tailWord_2706393) baseStart_2706393 baseEnd_2706393 := by
    simpa [prefixWord, tailWord_2706393, baseEnd_2706393] using wordTrace_append hprefix tailTrace_2706393
  have hstable : (prefixWord ++ tailWord_2706393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706393).length < 2 ^ (prefixWord ++ tailWord_2706393).sum := by decide
  have hdescent : baseEnd_2706393 < baseStart_2706393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706400 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2]
def baseStart_2706400 : Nat := 118140960795 + 2706400 * 2 ^ 59
def prefixEnd_2706400 : Nat := 4983230072969 + 3 ^ 40 * 2706400 * 2
def baseEnd_2706400 : Nat := 1389684043328316431253499

theorem tailTrace_2706400 : CollatzResearch.WordTrace tailWord_2706400 prefixEnd_2706400 1389684043328316431253499 := by
  unfold tailWord_2706400
  simp only [CollatzResearch.WordTrace]
  refine ⟨49355258697591245583094327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65807011596788327444125769 49355258697591245583094327)
  ·
    refine ⟨74032888046386868374641491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49355258697591245583094327 74032888046386868374641491)
    ·
      refine ⟨111049332069580302561962237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74032888046386868374641491 111049332069580302561962237)
      ·
        refine ⟨41643499526092613460735839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111049332069580302561962237 41643499526092613460735839)
        ·
          refine ⟨62465249289138920191103759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41643499526092613460735839 62465249289138920191103759)
          ·
            refine ⟨93697873933708380286655639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62465249289138920191103759 93697873933708380286655639)
            ·
              refine ⟨140546810900562570429983459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93697873933708380286655639 140546810900562570429983459)
              ·
                refine ⟨210820216350843855644975189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140546810900562570429983459 210820216350843855644975189)
                ·
                  refine ⟨2470549410361451433339553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 210820216350843855644975189 2470549410361451433339553)
                  ·
                    refine ⟨1852912057771088575004665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2470549410361451433339553 1852912057771088575004665)
                    ·
                      refine ⟨1389684043328316431253499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852912057771088575004665 1389684043328316431253499)
                      ·
                        rfl

theorem cell23_2706400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_2706400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706400 prefixEnd_2706400 := by exact prefixLift 2706400
  have htrace : WordTrace (prefixWord ++ tailWord_2706400) baseStart_2706400 baseEnd_2706400 := by
    simpa [prefixWord, tailWord_2706400, baseEnd_2706400] using wordTrace_append hprefix tailTrace_2706400
  have hstable : (prefixWord ++ tailWord_2706400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706400).length < 2 ^ (prefixWord ++ tailWord_2706400).sum := by decide
  have hdescent : baseEnd_2706400 < baseStart_2706400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706403 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2706403 : Nat := 118140960795 + 2706403 * 2 ^ 59
def prefixEnd_2706403 : Nat := 4983230072969 + 3 ^ 40 * 2706403 * 2
def baseEnd_2706403 : Nat := 1389685583770279919515985

theorem tailTrace_2706403 : CollatzResearch.WordTrace tailWord_2706403 prefixEnd_2706403 1389685583770279919515985 := by
  unfold tailWord_2706403
  simp only [CollatzResearch.WordTrace]
  refine ⟨98710626814171622678547863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65807084542781081785698575 98710626814171622678547863)
  ·
    refine ⟨148065940221257434017821795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98710626814171622678547863 148065940221257434017821795)
    ·
      refine ⟨222098910331886151026732693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148065940221257434017821795 222098910331886151026732693)
      ·
        refine ⟨10410886421807163329378095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222098910331886151026732693 10410886421807163329378095)
        ·
          refine ⟨15616329632710744994067143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10410886421807163329378095 15616329632710744994067143)
          ·
            refine ⟨23424494449066117491100715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15616329632710744994067143 23424494449066117491100715)
            ·
              refine ⟨35136741673599176236651073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23424494449066117491100715 35136741673599176236651073)
              ·
                refine ⟨26352556255199382177488305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35136741673599176236651073 26352556255199382177488305)
                ·
                  refine ⟨19764417191399536633116229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26352556255199382177488305 19764417191399536633116229)
                  ·
                    refine ⟨3705828223387413118709293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19764417191399536633116229 3705828223387413118709293)
                    ·
                      refine ⟨1389685583770279919515985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3705828223387413118709293 1389685583770279919515985)
                      ·
                        rfl

theorem cell23_2706403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2706403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706403 prefixEnd_2706403 := by exact prefixLift 2706403
  have htrace : WordTrace (prefixWord ++ tailWord_2706403) baseStart_2706403 baseEnd_2706403 := by
    simpa [prefixWord, tailWord_2706403, baseEnd_2706403] using wordTrace_append hprefix tailTrace_2706403
  have hstable : (prefixWord ++ tailWord_2706403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706403).length < 2 ^ (prefixWord ++ tailWord_2706403).sum := by decide
  have hdescent : baseEnd_2706403 < baseStart_2706403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706416 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_2706416 : Nat := 118140960795 + 2706416 * 2 ^ 59
def prefixEnd_2706416 : Nat := 4983230072969 + 3 ^ 40 * 2706416 * 2
def baseEnd_2706416 : Nat := 1389692259018788368653425

theorem tailTrace_2706416 : CollatzResearch.WordTrace tailWord_2706416 prefixEnd_2706416 1389692259018788368653425 := by
  unfold tailWord_2706416
  simp only [CollatzResearch.WordTrace]
  refine ⟨49355550481562262949385551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65807400642083017265847401 49355550481562262949385551)
  ·
    refine ⟨74033325722343394424078327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49355550481562262949385551 74033325722343394424078327)
    ·
      refine ⟨111049988583515091636117491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74033325722343394424078327 111049988583515091636117491)
      ·
        refine ⟨166574982875272637454176237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111049988583515091636117491 166574982875272637454176237)
        ·
          refine ⟨62465618578227239045316089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166574982875272637454176237 62465618578227239045316089)
          ·
            refine ⟨46849213933670429283987067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62465618578227239045316089 46849213933670429283987067)
            ·
              refine ⟨70273820900505643925980601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46849213933670429283987067 70273820900505643925980601)
              ·
                refine ⟨52705365675379232944485451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70273820900505643925980601 52705365675379232944485451)
                ·
                  refine ⟨79058048513068849416728177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52705365675379232944485451 79058048513068849416728177)
                  ·
                    refine ⟨59293536384801637062546133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79058048513068849416728177 59293536384801637062546133)
                    ·
                      refine ⟨1389692259018788368653425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59293536384801637062546133 1389692259018788368653425)
                      ·
                        rfl

theorem cell23_2706416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_2706416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706416 prefixEnd_2706416 := by exact prefixLift 2706416
  have htrace : WordTrace (prefixWord ++ tailWord_2706416) baseStart_2706416 baseEnd_2706416 := by
    simpa [prefixWord, tailWord_2706416, baseEnd_2706416] using wordTrace_append hprefix tailTrace_2706416
  have hstable : (prefixWord ++ tailWord_2706416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706416).length < 2 ^ (prefixWord ++ tailWord_2706416).sum := by decide
  have hdescent : baseEnd_2706416 < baseStart_2706416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706421 : List Nat := [1, 3, 5, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2706421 : Nat := 118140960795 + 2706421 * 2 ^ 59
def prefixEnd_2706421 : Nat := 4983230072969 + 3 ^ 40 * 2706421 * 2
def baseEnd_2706421 : Nat := 1389694826422060849090903

theorem tailTrace_2706421 : CollatzResearch.WordTrace tailWord_2706421 prefixEnd_2706421 1389694826422060849090903 := by
  unfold tailWord_2706421
  simp only [CollatzResearch.WordTrace]
  refine ⟨98711283328106411752703117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65807522218737607835135411 98711283328106411752703117)
  ·
    refine ⟨37016731248039904407263669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98711283328106411752703117 37016731248039904407263669)
    ·
      refine ⟨3470318554503741038180969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37016731248039904407263669 3470318554503741038180969)
      ·
        refine ⟨2602738915877805778635727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3470318554503741038180969 2602738915877805778635727)
        ·
          refine ⟨3904108373816708667953591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602738915877805778635727 3904108373816708667953591)
          ·
            refine ⟨5856162560725063001930387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904108373816708667953591 5856162560725063001930387)
            ·
              refine ⟨8784243841087594502895581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856162560725063001930387 8784243841087594502895581)
              ·
                refine ⟨3294091440407847938585843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8784243841087594502895581 3294091440407847938585843)
                ·
                  refine ⟨4941137160611771907878765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294091440407847938585843 4941137160611771907878765)
                  ·
                    refine ⟨1852926435229414465454537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4941137160611771907878765 1852926435229414465454537)
                    ·
                      refine ⟨1389694826422060849090903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852926435229414465454537 1389694826422060849090903)
                      ·
                        rfl

theorem cell23_2706421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2706421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706421 prefixEnd_2706421 := by exact prefixLift 2706421
  have htrace : WordTrace (prefixWord ++ tailWord_2706421) baseStart_2706421 baseEnd_2706421 := by
    simpa [prefixWord, tailWord_2706421, baseEnd_2706421] using wordTrace_append hprefix tailTrace_2706421
  have hstable : (prefixWord ++ tailWord_2706421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706421).length < 2 ^ (prefixWord ++ tailWord_2706421).sum := by decide
  have hdescent : baseEnd_2706421 < baseStart_2706421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706440 : List Nat := [2, 1, 3, 2, 1, 3, 2, 4, 5]
def baseStart_2706440 : Nat := 118140960795 + 2706440 * 2 ^ 59
def prefixEnd_2706440 : Nat := 4983230072969 + 3 ^ 40 * 2706440 * 2
def baseEnd_2706440 : Nat := 154411620283832919417035

theorem tailTrace_2706440 : CollatzResearch.WordTrace tailWord_2706440 prefixEnd_2706440 154411620283832919417035 := by
  unfold tailWord_2706440
  simp only [CollatzResearch.WordTrace]
  refine ⟨49355988157518788998822387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65807984210025051998429849 49355988157518788998822387)
  ·
    refine ⟨74033982236278183498233581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49355988157518788998822387 74033982236278183498233581)
    ·
      refine ⟨27762743338604318811837593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74033982236278183498233581 27762743338604318811837593)
      ·
        refine ⟨20822057503953239108878195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27762743338604318811837593 20822057503953239108878195)
        ·
          refine ⟨31233086255929858663317293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20822057503953239108878195 31233086255929858663317293)
          ·
            refine ⟨11712407345973696998743985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31233086255929858663317293 11712407345973696998743985)
            ·
              refine ⟨8784305509480272749057989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11712407345973696998743985 8784305509480272749057989)
              ·
                refine ⟨1647057283027551140448373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8784305509480272749057989 1647057283027551140448373)
                ·
                  refine ⟨154411620283832919417035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647057283027551140448373 154411620283832919417035)
                  ·
                    rfl

theorem cell23_2706440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 4, 5].length) (baseStart_2706440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706440 prefixEnd_2706440 := by exact prefixLift 2706440
  have htrace : WordTrace (prefixWord ++ tailWord_2706440) baseStart_2706440 baseEnd_2706440 := by
    simpa [prefixWord, tailWord_2706440, baseEnd_2706440] using wordTrace_append hprefix tailTrace_2706440
  have hstable : (prefixWord ++ tailWord_2706440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706440).length < 2 ^ (prefixWord ++ tailWord_2706440).sum := by decide
  have hdescent : baseEnd_2706440 < baseStart_2706440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706453 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2706453 : Nat := 118140960795 + 2706453 * 2 ^ 59
def prefixEnd_2706453 : Nat := 4983230072969 + 3 ^ 40 * 2706453 * 2
def baseEnd_2706453 : Nat := 463237085934334907963585

theorem tailTrace_2706453 : CollatzResearch.WordTrace tailWord_2706453 prefixEnd_2706453 463237085934334907963585 := by
  unfold tailWord_2706453
  simp only [CollatzResearch.WordTrace]
  refine ⟨98712450463990481217868013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65808300309326987478578675 98712450463990481217868013)
  ·
    refine ⟨37017168923996430456700505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98712450463990481217868013 37017168923996430456700505)
    ·
      refine ⟨27762876692997322842525379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37017168923996430456700505 27762876692997322842525379)
      ·
        refine ⟨41644315039495984263788069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27762876692997322842525379 41644315039495984263788069)
        ·
          refine ⟨7808309069905497049460263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41644315039495984263788069 7808309069905497049460263)
          ·
            refine ⟨11712463604858245574190395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7808309069905497049460263 11712463604858245574190395)
            ·
              refine ⟨17568695407287368361285593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11712463604858245574190395 17568695407287368361285593)
              ·
                refine ⟨13176521555465526270964195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17568695407287368361285593 13176521555465526270964195)
                ·
                  refine ⟨19764782333198289406446293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13176521555465526270964195 19764782333198289406446293)
                  ·
                    refine ⟨463237085934334907963585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19764782333198289406446293 463237085934334907963585)
                    ·
                      rfl

theorem cell23_2706453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2706453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706453 prefixEnd_2706453 := by exact prefixLift 2706453
  have htrace : WordTrace (prefixWord ++ tailWord_2706453) baseStart_2706453 baseEnd_2706453 := by
    simpa [prefixWord, tailWord_2706453, baseEnd_2706453] using wordTrace_append hprefix tailTrace_2706453
  have hstable : (prefixWord ++ tailWord_2706453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706453).length < 2 ^ (prefixWord ++ tailWord_2706453).sum := by decide
  have hdescent : baseEnd_2706453 < baseStart_2706453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706474 : List Nat := [3, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_2706474 : Nat := 118140960795 + 2706474 * 2 ^ 59
def prefixEnd_2706474 : Nat := 4983230072969 + 3 ^ 40 * 2706474 * 2
def baseEnd_2706474 : Nat := 154413560099638793525351

theorem tailTrace_2706474 : CollatzResearch.WordTrace tailWord_2706474 prefixEnd_2706474 154413560099638793525351 := by
  unfold tailWord_2706474
  simp only [CollatzResearch.WordTrace]
  refine ⟨24678304099228600451095619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65808810931276267869588317 24678304099228600451095619)
  ·
    refine ⟨37017456148842900676643429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24678304099228600451095619 37017456148842900676643429)
    ·
      refine ⟨6940773027908043876870643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37017456148842900676643429 6940773027908043876870643)
      ·
        refine ⟨10411159541862065815305965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6940773027908043876870643 10411159541862065815305965)
        ·
          refine ⟨3904184828198274680739737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10411159541862065815305965 3904184828198274680739737)
          ·
            refine ⟨2928138621148706010554803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904184828198274680739737 2928138621148706010554803)
            ·
              refine ⟨4392207931723059015832205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928138621148706010554803 4392207931723059015832205)
              ·
                refine ⟨1647077974396147130937077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392207931723059015832205 1647077974396147130937077)
                ·
                  refine ⟨154413560099638793525351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1647077974396147130937077 154413560099638793525351)
                  ·
                    rfl

theorem cell23_2706474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_2706474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706474 prefixEnd_2706474 := by exact prefixLift 2706474
  have htrace : WordTrace (prefixWord ++ tailWord_2706474) baseStart_2706474 baseEnd_2706474 := by
    simpa [prefixWord, tailWord_2706474, baseEnd_2706474] using wordTrace_append hprefix tailTrace_2706474
  have hstable : (prefixWord ++ tailWord_2706474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706474).length < 2 ^ (prefixWord ++ tailWord_2706474).sum := by decide
  have hdescent : baseEnd_2706474 < baseStart_2706474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706490 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_2706490 : Nat := 118140960795 + 2706490 * 2 ^ 59
def prefixEnd_2706490 : Nat := 4983230072969 + 3 ^ 40 * 2706490 * 2
def baseEnd_2706490 : Nat := 1389730256587221079128085

theorem tailTrace_2706490 : CollatzResearch.WordTrace tailWord_2706490 prefixEnd_2706490 1389730256587221079128085 := by
  unfold tailWord_2706490
  simp only [CollatzResearch.WordTrace]
  refine ⟨24678449991214109134241231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65809199976570957691309949 24678449991214109134241231)
  ·
    refine ⟨37017674986821163701361847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24678449991214109134241231 37017674986821163701361847)
    ·
      refine ⟨55526512480231745552042771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37017674986821163701361847 55526512480231745552042771)
      ·
        refine ⟨83289768720347618328064157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55526512480231745552042771 83289768720347618328064157)
        ·
          refine ⟨31233663270130356873024059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83289768720347618328064157 31233663270130356873024059)
          ·
            refine ⟨46850494905195535309536089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31233663270130356873024059 46850494905195535309536089)
            ·
              refine ⟨35137871178896651482152067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46850494905195535309536089 35137871178896651482152067)
              ·
                refine ⟨52706806768344977223228101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35137871178896651482152067 52706806768344977223228101)
                ·
                  refine ⟨9882526269064683229355269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52706806768344977223228101 9882526269064683229355269)
                  ·
                    refine ⟨1852973675449628105504113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9882526269064683229355269 1852973675449628105504113)
                    ·
                      refine ⟨1389730256587221079128085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1852973675449628105504113 1389730256587221079128085)
                      ·
                        rfl

theorem cell23_2706490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_2706490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706490 prefixEnd_2706490 := by exact prefixLift 2706490
  have htrace : WordTrace (prefixWord ++ tailWord_2706490) baseStart_2706490 baseEnd_2706490 := by
    simpa [prefixWord, tailWord_2706490, baseEnd_2706490] using wordTrace_append hprefix tailTrace_2706490
  have hstable : (prefixWord ++ tailWord_2706490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706490).length < 2 ^ (prefixWord ++ tailWord_2706490).sum := by decide
  have hdescent : baseEnd_2706490 < baseStart_2706490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706510 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3]
def baseStart_2706510 : Nat := 118140960795 + 2706510 * 2 ^ 59
def prefixEnd_2706510 : Nat := 4983230072969 + 3 ^ 40 * 2706510 * 2
def baseEnd_2706510 : Nat := 1389740526200311000877993

theorem tailTrace_2706510 : CollatzResearch.WordTrace tailWord_2706510 prefixEnd_2706510 1389740526200311000877993 := by
  unfold tailWord_2706510
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339316178097997494086623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65809686283189319968461989 12339316178097997494086623)
  ·
    refine ⟨18508974267146996241129935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12339316178097997494086623 18508974267146996241129935)
    ·
      refine ⟨27763461400720494361694903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18508974267146996241129935 27763461400720494361694903)
      ·
        refine ⟨41645192101080741542542355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27763461400720494361694903 41645192101080741542542355)
        ·
          refine ⟨62467788151621112313813533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41645192101080741542542355 62467788151621112313813533)
          ·
            refine ⟨23425420556857917117680075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62467788151621112313813533 23425420556857917117680075)
            ·
              refine ⟨35138130835286875676520113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23425420556857917117680075 35138130835286875676520113)
              ·
                refine ⟨26353598126465156757390085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35138130835286875676520113 26353598126465156757390085)
                ·
                  refine ⟨4941299648712216892010641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26353598126465156757390085 4941299648712216892010641)
                  ·
                    refine ⟨3705974736534162669007981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4941299648712216892010641 3705974736534162669007981)
                    ·
                      refine ⟨1389740526200311000877993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3705974736534162669007981 1389740526200311000877993)
                      ·
                        rfl

theorem cell23_2706510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_2706510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706510 prefixEnd_2706510 := by exact prefixLift 2706510
  have htrace : WordTrace (prefixWord ++ tailWord_2706510) baseStart_2706510 baseEnd_2706510 := by
    simpa [prefixWord, tailWord_2706510, baseEnd_2706510] using wordTrace_append hprefix tailTrace_2706510
  have hstable : (prefixWord ++ tailWord_2706510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706510).length < 2 ^ (prefixWord ++ tailWord_2706510).sum := by decide
  have hdescent : baseEnd_2706510 < baseStart_2706510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706550 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2706550 : Nat := 118140960795 + 2706550 * 2 ^ 59
def prefixEnd_2706550 : Nat := 4983230072969 + 3 ^ 40 * 2706550 * 2
def baseEnd_2706550 : Nat := 1389761065426490844377809

theorem tailTrace_2706550 : CollatzResearch.WordTrace tailWord_2706550 prefixEnd_2706550 1389761065426490844377809 := by
  unfold tailWord_2706550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169749271539941674009319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65810658896426044522766069 6169749271539941674009319)
  ·
    refine ⟨9254623907309912511013979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6169749271539941674009319 9254623907309912511013979)
    ·
      refine ⟨13881935860964868766520969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254623907309912511013979 13881935860964868766520969)
      ·
        refine ⟨10411451895723651574890727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13881935860964868766520969 10411451895723651574890727)
        ·
          refine ⟨15617177843585477362336091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10411451895723651574890727 15617177843585477362336091)
          ·
            refine ⟨23425766765378216043504137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15617177843585477362336091 23425766765378216043504137)
            ·
              refine ⟨17569325074033662032628103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23425766765378216043504137 17569325074033662032628103)
              ·
                refine ⟨26353987611050493048942155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17569325074033662032628103 26353987611050493048942155)
                ·
                  refine ⟨39530981416575739573413233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26353987611050493048942155 39530981416575739573413233)
                  ·
                    refine ⟨29648236062431804680059925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39530981416575739573413233 29648236062431804680059925)
                    ·
                      refine ⟨1389761065426490844377809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29648236062431804680059925 1389761065426490844377809)
                      ·
                        rfl

theorem cell23_2706550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2706550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706550 prefixEnd_2706550 := by exact prefixLift 2706550
  have htrace : WordTrace (prefixWord ++ tailWord_2706550) baseStart_2706550 baseEnd_2706550 := by
    simpa [prefixWord, tailWord_2706550, baseEnd_2706550] using wordTrace_append hprefix tailTrace_2706550
  have hstable : (prefixWord ++ tailWord_2706550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706550).length < 2 ^ (prefixWord ++ tailWord_2706550).sum := by decide
  have hdescent : baseEnd_2706550 < baseStart_2706550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706557 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_2706557 : Nat := 118140960795 + 2706557 * 2 ^ 59
def prefixEnd_2706557 : Nat := 4983230072969 + 3 ^ 40 * 2706557 * 2
def baseEnd_2706557 : Nat := 1389764659791072316990277

theorem tailTrace_2706557 : CollatzResearch.WordTrace tailWord_2706557 prefixEnd_2706557 1389764659791072316990277 := by
  unfold tailWord_2706557
  simp only [CollatzResearch.WordTrace]
  refine ⟨98716243655613706979653925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65810829103742471319769283 98716243655613706979653925)
  ·
    refine ⟨18509295685427570058685111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98716243655613706979653925 18509295685427570058685111)
    ·
      refine ⟨27763943528141355088027667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18509295685427570058685111 27763943528141355088027667)
      ·
        refine ⟨41645915292212032632041501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27763943528141355088027667 41645915292212032632041501)
        ·
          refine ⟨15617218234579512237015563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41645915292212032632041501 15617218234579512237015563)
          ·
            refine ⟨23425827351869268355523345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15617218234579512237015563 23425827351869268355523345)
            ·
              refine ⟨17569370513901951266642509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23425827351869268355523345 17569370513901951266642509)
              ·
                refine ⟨6588513942713231724990941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17569370513901951266642509 6588513942713231724990941)
                ·
                  refine ⟨2470692728517461896871603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6588513942713231724990941 2470692728517461896871603)
                  ·
                    refine ⟨3706039092776192845307405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470692728517461896871603 3706039092776192845307405)
                    ·
                      refine ⟨1389764659791072316990277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706039092776192845307405 1389764659791072316990277)
                      ·
                        rfl

theorem cell23_2706557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_2706557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706557 prefixEnd_2706557 := by exact prefixLift 2706557
  have htrace : WordTrace (prefixWord ++ tailWord_2706557) baseStart_2706557 baseEnd_2706557 := by
    simpa [prefixWord, tailWord_2706557, baseEnd_2706557] using wordTrace_append hprefix tailTrace_2706557
  have hstable : (prefixWord ++ tailWord_2706557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706557).length < 2 ^ (prefixWord ++ tailWord_2706557).sum := by decide
  have hdescent : baseEnd_2706557 < baseStart_2706557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706558 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2706558 : Nat := 118140960795 + 2706558 * 2 ^ 59
def prefixEnd_2706558 : Nat := 4983230072969 + 3 ^ 40 * 2706558 * 2
def baseEnd_2706558 : Nat := 1389765173271726813077773

theorem tailTrace_2706558 : CollatzResearch.WordTrace tailWord_2706558 prefixEnd_2706558 1389765173271726813077773 := by
  unfold tailWord_2706558
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339535016076260518805041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65810853419073389433626885 12339535016076260518805041)
  ·
    refine ⟨9254651262057195389103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12339535016076260518805041 9254651262057195389103781)
    ·
      refine ⟨1735247111635724135456959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9254651262057195389103781 1735247111635724135456959)
      ·
        refine ⟨2602870667453586203185439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735247111635724135456959 2602870667453586203185439)
        ·
          refine ⟨3904306001180379304778159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602870667453586203185439 3904306001180379304778159)
          ·
            refine ⟨5856459001770568957167239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904306001180379304778159 5856459001770568957167239)
            ·
              refine ⟨8784688502655853435750859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856459001770568957167239 8784688502655853435750859)
              ·
                refine ⟨13177032753983780153626289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8784688502655853435750859 13177032753983780153626289)
                ·
                  refine ⟨9882774565487835115219717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13177032753983780153626289 9882774565487835115219717)
                  ·
                    refine ⟨1853020231028969084103697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9882774565487835115219717 1853020231028969084103697)
                    ·
                      refine ⟨1389765173271726813077773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853020231028969084103697 1389765173271726813077773)
                      ·
                        rfl

theorem cell23_2706558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2706558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706558 prefixEnd_2706558 := by exact prefixLift 2706558
  have htrace : WordTrace (prefixWord ++ tailWord_2706558) baseStart_2706558 baseEnd_2706558 := by
    simpa [prefixWord, tailWord_2706558, baseEnd_2706558] using wordTrace_append hprefix tailTrace_2706558
  have hstable : (prefixWord ++ tailWord_2706558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706558).length < 2 ^ (prefixWord ++ tailWord_2706558).sum := by decide
  have hdescent : baseEnd_2706558 < baseStart_2706558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706574 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3]
def baseStart_2706574 : Nat := 118140960795 + 2706574 * 2 ^ 59
def prefixEnd_2706574 : Nat := 4983230072969 + 3 ^ 40 * 2706574 * 2
def baseEnd_2706574 : Nat := 1389773388962198750477699

theorem tailTrace_2706574 : CollatzResearch.WordTrace tailWord_2706574 prefixEnd_2706574 1389773388962198750477699 := by
  unfold tailWord_2706574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12339607962069014860377847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65811242464368079255348517 12339607962069014860377847)
  ·
    refine ⟨18509411943103522290566771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12339607962069014860377847 18509411943103522290566771)
    ·
      refine ⟨27764117914655283435850157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18509411943103522290566771 27764117914655283435850157)
      ·
        refine ⟨10411544217995731288443809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27764117914655283435850157 10411544217995731288443809)
        ·
          refine ⟨7808658163496798466332857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10411544217995731288443809 7808658163496798466332857)
          ·
            refine ⟨5856493622622598849749643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7808658163496798466332857 5856493622622598849749643)
            ·
              refine ⟨8784740433933898274624465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856493622622598849749643 8784740433933898274624465)
              ·
                refine ⟨6588555325450423705968349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8784740433933898274624465 6588555325450423705968349)
                ·
                  refine ⟨2470708247043908889738131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6588555325450423705968349 2470708247043908889738131)
                  ·
                    refine ⟨3706062370565863334607197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470708247043908889738131 3706062370565863334607197)
                    ·
                      refine ⟨1389773388962198750477699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706062370565863334607197 1389773388962198750477699)
                      ·
                        rfl

theorem cell23_2706574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_2706574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706574 prefixEnd_2706574 := by exact prefixLift 2706574
  have htrace : WordTrace (prefixWord ++ tailWord_2706574) baseStart_2706574 baseEnd_2706574 := by
    simpa [prefixWord, tailWord_2706574, baseEnd_2706574] using wordTrace_append hprefix tailTrace_2706574
  have hstable : (prefixWord ++ tailWord_2706574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706574).length < 2 ^ (prefixWord ++ tailWord_2706574).sum := by decide
  have hdescent : baseEnd_2706574 < baseStart_2706574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706584 : List Nat := [2, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_2706584 : Nat := 118140960795 + 2706584 * 2 ^ 59
def prefixEnd_2706584 : Nat := 4983230072969 + 3 ^ 40 * 2706584 * 2
def baseEnd_2706584 : Nat := 1389778523768743711352653

theorem tailTrace_2706584 : CollatzResearch.WordTrace tailWord_2706584 prefixEnd_2706584 1389778523768743711352653 := by
  unfold tailWord_2706584
  simp only [CollatzResearch.WordTrace]
  refine ⟨49358614213257945295443403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65811485617677260393924537 49358614213257945295443403)
  ·
    refine ⟨74037921319886917943165105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49358614213257945295443403 74037921319886917943165105)
    ·
      refine ⟨55528440989915188457373829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74037921319886917943165105 55528440989915188457373829)
      ·
        refine ⟨10411582685609097835757593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55528440989915188457373829 10411582685609097835757593)
        ·
          refine ⟨7808687014206823376818195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10411582685609097835757593 7808687014206823376818195)
          ·
            refine ⟨11713030521310235065227293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7808687014206823376818195 11713030521310235065227293)
            ·
              refine ⟨4392386445491338149460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11713030521310235065227293 4392386445491338149460235)
              ·
                refine ⟨6588579668237007224190353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392386445491338149460235 6588579668237007224190353)
                ·
                  refine ⟨4941434751177755418142765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6588579668237007224190353 4941434751177755418142765)
                  ·
                    refine ⟨1853038031691658281803537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4941434751177755418142765 1853038031691658281803537)
                    ·
                      refine ⟨1389778523768743711352653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853038031691658281803537 1389778523768743711352653)
                      ·
                        rfl

theorem cell23_2706584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_2706584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706584 prefixEnd_2706584 := by exact prefixLift 2706584
  have htrace : WordTrace (prefixWord ++ tailWord_2706584) baseStart_2706584 baseEnd_2706584 := by
    simpa [prefixWord, tailWord_2706584, baseEnd_2706584] using wordTrace_append hprefix tailTrace_2706584
  have hstable : (prefixWord ++ tailWord_2706584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706584).length < 2 ^ (prefixWord ++ tailWord_2706584).sum := by decide
  have hdescent : baseEnd_2706584 < baseStart_2706584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706594 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2706594 : Nat := 118140960795 + 2706594 * 2 ^ 59
def prefixEnd_2706594 : Nat := 4983230072969 + 3 ^ 40 * 2706594 * 2
def baseEnd_2706594 : Nat := 463261219525096224075869

theorem tailTrace_2706594 : CollatzResearch.WordTrace tailWord_2706594 prefixEnd_2706594 463261219525096224075869 := by
  unfold tailWord_2706594
  simp only [CollatzResearch.WordTrace]
  refine ⟨24679398289119915574687709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65811728770986441532500557 24679398289119915574687709)
  ·
    refine ⟨9254774358419968340507891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24679398289119915574687709 9254774358419968340507891)
    ·
      refine ⟨13882161537629952510761837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254774358419968340507891 13882161537629952510761837)
      ·
        refine ⟨5205810576611232191535689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13882161537629952510761837 5205810576611232191535689)
        ·
          refine ⟨3904357932458424143651767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5205810576611232191535689 3904357932458424143651767)
          ·
            refine ⟨5856536898687636215477651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904357932458424143651767 5856536898687636215477651)
            ·
              refine ⟨8784805348031454323216477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856536898687636215477651 8784805348031454323216477)
              ·
                refine ⟨3294302005511795371206179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8784805348031454323216477 3294302005511795371206179)
                ·
                  refine ⟨4941453008267693056809269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294302005511795371206179 4941453008267693056809269)
                  ·
                    refine ⟨463261219525096224075869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4941453008267693056809269 463261219525096224075869)
                    ·
                      rfl

theorem cell23_2706594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2706594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706594 prefixEnd_2706594 := by exact prefixLift 2706594
  have htrace : WordTrace (prefixWord ++ tailWord_2706594) baseStart_2706594 baseEnd_2706594 := by
    simpa [prefixWord, tailWord_2706594, baseEnd_2706594] using wordTrace_append hprefix tailTrace_2706594
  have hstable : (prefixWord ++ tailWord_2706594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706594).length < 2 ^ (prefixWord ++ tailWord_2706594).sum := by decide
  have hdescent : baseEnd_2706594 < baseStart_2706594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706597 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_2706597 : Nat := 118140960795 + 2706597 * 2 ^ 59
def prefixEnd_2706597 : Nat := 4983230072969 + 3 ^ 40 * 2706597 * 2
def baseEnd_2706597 : Nat := 1389785199017252160490093

theorem tailTrace_2706597 : CollatzResearch.WordTrace tailWord_2706597 prefixEnd_2706597 1389785199017252160490093 := by
  unfold tailWord_2706597
  simp only [CollatzResearch.WordTrace]
  refine ⟨98717702575468793811110045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65811801716979195874073363 98717702575468793811110045)
  ·
    refine ⟨37019138465800797679166267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98717702575468793811110045 37019138465800797679166267)
    ·
      refine ⟨55528707698701196518749401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37019138465800797679166267 55528707698701196518749401)
      ·
        refine ⟨41646530774025897389062051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55528707698701196518749401 41646530774025897389062051)
        ·
          refine ⟨62469796161038846083593077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41646530774025897389062051 62469796161038846083593077)
          ·
            refine ⟨5856543390097391820336851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62469796161038846083593077 5856543390097391820336851)
            ·
              refine ⟨8784815085146087730505277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856543390097391820336851 8784815085146087730505277)
              ·
                refine ⟨3294305656929782898939479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8784815085146087730505277 3294305656929782898939479)
                ·
                  refine ⟨4941458485394674348409219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294305656929782898939479 4941458485394674348409219)
                  ·
                    refine ⟨7412187728092011522613829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4941458485394674348409219 7412187728092011522613829)
                    ·
                      refine ⟨1389785199017252160490093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7412187728092011522613829 1389785199017252160490093)
                      ·
                        rfl

theorem cell23_2706597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_2706597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706597 prefixEnd_2706597 := by exact prefixLift 2706597
  have htrace : WordTrace (prefixWord ++ tailWord_2706597) baseStart_2706597 baseEnd_2706597 := by
    simpa [prefixWord, tailWord_2706597, baseEnd_2706597] using wordTrace_append hprefix tailTrace_2706597
  have hstable : (prefixWord ++ tailWord_2706597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706597).length < 2 ^ (prefixWord ++ tailWord_2706597).sum := by decide
  have hdescent : baseEnd_2706597 < baseStart_2706597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706607 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 2, 4]
def baseStart_2706607 : Nat := 118140960795 + 2706607 * 2 ^ 59
def prefixEnd_2706607 : Nat := 4983230072969 + 3 ^ 40 * 2706607 * 2
def baseEnd_2706607 : Nat := 463263444607932373788349

theorem tailTrace_2706607 : CollatzResearch.WordTrace tailWord_2706607 prefixEnd_2706607 463263444607932373788349 := by
  unfold tailWord_2706607
  simp only [CollatzResearch.WordTrace]
  refine ⟨98718067305432565518974075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65812044870288377012649383 98718067305432565518974075)
  ·
    refine ⟨148077100958148848278461113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98718067305432565518974075 148077100958148848278461113)
    ·
      refine ⟨111057825718611636208845835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148077100958148848278461113 111057825718611636208845835)
      ·
        refine ⟨166586738577917454313268753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111057825718611636208845835 166586738577917454313268753)
        ·
          refine ⟨124940053933438090734951565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166586738577917454313268753 124940053933438090734951565)
          ·
            refine ⟨46852520225039284025606837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 124940053933438090734951565 46852520225039284025606837)
            ·
              refine ⟨4392423771097432877400641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46852520225039284025606837 4392423771097432877400641)
              ·
                refine ⟨3294317828323074658050481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392423771097432877400641 3294317828323074658050481)
                ·
                  refine ⟨2470738371242305993537861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294317828323074658050481 2470738371242305993537861)
                  ·
                    refine ⟨463263444607932373788349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470738371242305993537861 463263444607932373788349)
                    ·
                      rfl

theorem cell23_2706607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_2706607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706607 prefixEnd_2706607 := by exact prefixLift 2706607
  have htrace : WordTrace (prefixWord ++ tailWord_2706607) baseStart_2706607 baseEnd_2706607 := by
    simpa [prefixWord, tailWord_2706607, baseEnd_2706607] using wordTrace_append hprefix tailTrace_2706607
  have hstable : (prefixWord ++ tailWord_2706607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706607).length < 2 ^ (prefixWord ++ tailWord_2706607).sum := by decide
  have hdescent : baseEnd_2706607 < baseStart_2706607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706624 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 1, 6]
def baseStart_2706624 : Nat := 118140960795 + 2706624 * 2 ^ 59
def prefixEnd_2706624 : Nat := 4983230072969 + 3 ^ 40 * 2706624 * 2
def baseEnd_2706624 : Nat := 463266354331641184950823

theorem tailTrace_2706624 : CollatzResearch.WordTrace tailWord_2706624 prefixEnd_2706624 463266354331641184950823 := by
  unfold tailWord_2706624
  simp only [CollatzResearch.WordTrace]
  refine ⟨49359343673185488711171463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65812458230913984948228617 49359343673185488711171463)
  ·
    refine ⟨74039015509778233066757195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49359343673185488711171463 74039015509778233066757195)
    ·
      refine ⟨111058523264667349600135793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74039015509778233066757195 111058523264667349600135793)
      ·
        refine ⟨83293892448500512200101845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111058523264667349600135793 83293892448500512200101845)
        ·
          refine ⟨1952200604261730754689887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 83293892448500512200101845 1952200604261730754689887)
          ·
            refine ⟨2928300906392596132034831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952200604261730754689887 2928300906392596132034831)
            ·
              refine ⟨4392451359588894198052247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928300906392596132034831 4392451359588894198052247)
              ·
                refine ⟨6588677039383341297078371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392451359588894198052247 6588677039383341297078371)
                ·
                  refine ⟨9883015559075011945617557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6588677039383341297078371 9883015559075011945617557)
                  ·
                    refine ⟨463266354331641184950823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9883015559075011945617557 463266354331641184950823)
                    ·
                      rfl

theorem cell23_2706624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_2706624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706624 prefixEnd_2706624 := by exact prefixLift 2706624
  have htrace : WordTrace (prefixWord ++ tailWord_2706624) baseStart_2706624 baseEnd_2706624 := by
    simpa [prefixWord, tailWord_2706624, baseEnd_2706624] using wordTrace_append hprefix tailTrace_2706624
  have hstable : (prefixWord ++ tailWord_2706624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706624).length < 2 ^ (prefixWord ++ tailWord_2706624).sum := by decide
  have hdescent : baseEnd_2706624 < baseStart_2706624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706633 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_2706633 : Nat := 118140960795 + 2706633 * 2 ^ 59
def prefixEnd_2706633 : Nat := 4983230072969 + 3 ^ 40 * 2706633 * 2
def baseEnd_2706633 : Nat := 463267894773604673213309

theorem tailTrace_2706633 : CollatzResearch.WordTrace tailWord_2706633 prefixEnd_2706633 463267894773604673213309 := by
  unfold tailWord_2706633
  simp only [CollatzResearch.WordTrace]
  refine ⟨98719015603338371959420553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65812677068892247972947035 98719015603338371959420553)
  ·
    refine ⟨74039261702503778969565415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98719015603338371959420553 74039261702503778969565415)
    ·
      refine ⟨111058892553755668454348123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74039261702503778969565415 111058892553755668454348123)
      ·
        refine ⟨166588338830633502681522185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111058892553755668454348123 166588338830633502681522185)
        ·
          refine ⟨124941254122975127011141639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166588338830633502681522185 124941254122975127011141639)
          ·
            refine ⟨187411881184462690516712459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124941254122975127011141639 187411881184462690516712459)
            ·
              refine ⟨281117821776694035775068689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187411881184462690516712459 281117821776694035775068689)
              ·
                refine ⟨210838366332520526831301517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281117821776694035775068689 210838366332520526831301517)
                ·
                  refine ⟨79064387374695197561738069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210838366332520526831301517 79064387374695197561738069)
                  ·
                    refine ⟨463267894773604673213309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 79064387374695197561738069 463267894773604673213309)
                    ·
                      rfl

theorem cell23_2706633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_2706633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706633 prefixEnd_2706633 := by exact prefixLift 2706633
  have htrace : WordTrace (prefixWord ++ tailWord_2706633) baseStart_2706633 baseEnd_2706633 := by
    simpa [prefixWord, tailWord_2706633, baseEnd_2706633] using wordTrace_append hprefix tailTrace_2706633
  have hstable : (prefixWord ++ tailWord_2706633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706633).length < 2 ^ (prefixWord ++ tailWord_2706633).sum := by decide
  have hdescent : baseEnd_2706633 < baseStart_2706633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706634 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_2706634 : Nat := 118140960795 + 2706634 * 2 ^ 59
def prefixEnd_2706634 : Nat := 4983230072969 + 3 ^ 40 * 2706634 * 2
def baseEnd_2706634 : Nat := 1389804197801468515727423

theorem tailTrace_2706634 : CollatzResearch.WordTrace tailWord_2706634 prefixEnd_2706634 1389804197801468515727423 := by
  unfold tailWord_2706634
  simp only [CollatzResearch.WordTrace]
  refine ⟨24679763019083687282551739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65812701384223166086804637 24679763019083687282551739)
  ·
    refine ⟨37019644528625530923827609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24679763019083687282551739 37019644528625530923827609)
    ·
      refine ⟨27764733396469148192870707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37019644528625530923827609 27764733396469148192870707)
      ·
        refine ⟨41647100094703722289306061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27764733396469148192870707 41647100094703722289306061)
        ·
          refine ⟨15617662535513895858489773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41647100094703722289306061 15617662535513895858489773)
          ·
            refine ⟨5856623450817710946933665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15617662535513895858489773 5856623450817710946933665)
            ·
              refine ⟨4392467588113283210200249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5856623450817710946933665 4392467588113283210200249)
              ·
                refine ⟨3294350691084962407650187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392467588113283210200249 3294350691084962407650187)
                ·
                  refine ⟨4941526036627443611475281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294350691084962407650187 4941526036627443611475281)
                  ·
                    refine ⟨3706144527470582708606461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4941526036627443611475281 3706144527470582708606461)
                    ·
                      refine ⟨1389804197801468515727423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706144527470582708606461 1389804197801468515727423)
                      ·
                        rfl

theorem cell23_2706634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_2706634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706634 prefixEnd_2706634 := by exact prefixLift 2706634
  have htrace : WordTrace (prefixWord ++ tailWord_2706634) baseStart_2706634 baseEnd_2706634 := by
    simpa [prefixWord, tailWord_2706634, baseEnd_2706634] using wordTrace_append hprefix tailTrace_2706634
  have hstable : (prefixWord ++ tailWord_2706634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706634).length < 2 ^ (prefixWord ++ tailWord_2706634).sum := by decide
  have hdescent : baseEnd_2706634 < baseStart_2706634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706647 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_2706647 : Nat := 118140960795 + 2706647 * 2 ^ 59
def prefixEnd_2706647 : Nat := 4983230072969 + 3 ^ 40 * 2706647 * 2
def baseEnd_2706647 : Nat := 1389810873049976964864863

theorem tailTrace_2706647 : CollatzResearch.WordTrace tailWord_2706647 prefixEnd_2706647 1389810873049976964864863 := by
  unfold tailWord_2706647
  simp only [CollatzResearch.WordTrace]
  refine ⟨98719526225287652350430195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65813017483525101566953463 98719526225287652350430195)
  ·
    refine ⟨148079289337931478525645293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98719526225287652350430195 148079289337931478525645293)
    ·
      refine ⟨55529733501724304447116985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148079289337931478525645293 55529733501724304447116985)
      ·
        refine ⟨41647300126293228335337739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55529733501724304447116985 41647300126293228335337739)
        ·
          refine ⟨62470950189439842503006609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41647300126293228335337739 62470950189439842503006609)
          ·
            refine ⟨46853212642079881877254957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62470950189439842503006609 46853212642079881877254957)
            ·
              refine ⟨17569954740779955703970609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46853212642079881877254957 17569954740779955703970609)
              ·
                refine ⟨13177466055584966777977957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17569954740779955703970609 13177466055584966777977957)
                ·
                  refine ⟨2470774885422181270870867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13177466055584966777977957 2470774885422181270870867)
                  ·
                    refine ⟨3706162328133271906306301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470774885422181270870867 3706162328133271906306301)
                    ·
                      refine ⟨1389810873049976964864863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706162328133271906306301 1389810873049976964864863)
                      ·
                        rfl

theorem cell23_2706647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_2706647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706647 prefixEnd_2706647 := by exact prefixLift 2706647
  have htrace : WordTrace (prefixWord ++ tailWord_2706647) baseStart_2706647 baseEnd_2706647 := by
    simpa [prefixWord, tailWord_2706647, baseEnd_2706647] using wordTrace_append hprefix tailTrace_2706647
  have hstable : (prefixWord ++ tailWord_2706647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706647).length < 2 ^ (prefixWord ++ tailWord_2706647).sum := by decide
  have hdescent : baseEnd_2706647 < baseStart_2706647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706664 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_2706664 : Nat := 118140960795 + 2706664 * 2 ^ 59
def prefixEnd_2706664 : Nat := 4983230072969 + 3 ^ 40 * 2706664 * 2
def baseEnd_2706664 : Nat := 1389819602221103398352285

theorem tailTrace_2706664 : CollatzResearch.WordTrace tailWord_2706664 prefixEnd_2706664 1389819602221103398352285 := by
  unfold tailWord_2706664
  simp only [CollatzResearch.WordTrace]
  refine ⟨49360073133113032126899523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65813430844150709502532697 49360073133113032126899523)
  ·
    refine ⟨74040109699669548190349285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49360073133113032126899523 74040109699669548190349285)
    ·
      refine ⟨13882520568688040285690491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74040109699669548190349285 13882520568688040285690491)
      ·
        refine ⟨20823780853032060428535737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882520568688040285690491 20823780853032060428535737)
        ·
          refine ⟨15617835639774045321401803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20823780853032060428535737 15617835639774045321401803)
          ·
            refine ⟨23426753459661067982102705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15617835639774045321401803 23426753459661067982102705)
            ·
              refine ⟨17570065094745800986577029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23426753459661067982102705 17570065094745800986577029)
              ·
                refine ⟨3294387205264837684983193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17570065094745800986577029 3294387205264837684983193)
                ·
                  refine ⟨2470790403948628263737395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294387205264837684983193 2470790403948628263737395)
                  ·
                    refine ⟨3706185605922942395606093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470790403948628263737395 3706185605922942395606093)
                    ·
                      refine ⟨1389819602221103398352285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706185605922942395606093 1389819602221103398352285)
                      ·
                        rfl

theorem cell23_2706664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_2706664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706664 prefixEnd_2706664 := by exact prefixLift 2706664
  have htrace : WordTrace (prefixWord ++ tailWord_2706664) baseStart_2706664 baseEnd_2706664 := by
    simpa [prefixWord, tailWord_2706664, baseEnd_2706664] using wordTrace_append hprefix tailTrace_2706664
  have hstable : (prefixWord ++ tailWord_2706664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706664).length < 2 ^ (prefixWord ++ tailWord_2706664).sum := by decide
  have hdescent : baseEnd_2706664 < baseStart_2706664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706691 : List Nat := [1, 1, 1, 3, 2, 6, 1, 2, 1, 3, 2]
def baseStart_2706691 : Nat := 118140960795 + 2706691 * 2 ^ 59
def prefixEnd_2706691 : Nat := 4983230072969 + 3 ^ 40 * 2706691 * 2
def baseEnd_2706691 : Nat := 1389833466198774792714661

theorem tailTrace_2706691 : CollatzResearch.WordTrace tailWord_2706691 prefixEnd_2706691 1389833466198774792714661 := by
  unfold tailWord_2706691
  simp only [CollatzResearch.WordTrace]
  refine ⟨98721131037128247865031927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65814087358085498576687951 98721131037128247865031927)
  ·
    refine ⟨148081696555692371797547891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98721131037128247865031927 148081696555692371797547891)
    ·
      refine ⟨222122544833538557696321837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148081696555692371797547891 222122544833538557696321837)
      ·
        refine ⟨83295954312576959136120689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222122544833538557696321837 83295954312576959136120689)
        ·
          refine ⟨62471965734432719352090517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83295954312576959136120689 62471965734432719352090517)
          ·
            refine ⟨2928373393801533719629243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62471965734432719352090517 2928373393801533719629243)
            ·
              refine ⟨4392560090702300579443865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928373393801533719629243 4392560090702300579443865)
              ·
                refine ⟨3294420068026725434582899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392560090702300579443865 3294420068026725434582899)
                ·
                  refine ⟨4941630102040088151874349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294420068026725434582899 4941630102040088151874349)
                  ·
                    refine ⟨1853111288265033056952881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4941630102040088151874349 1853111288265033056952881)
                    ·
                      refine ⟨1389833466198774792714661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853111288265033056952881 1389833466198774792714661)
                      ·
                        rfl

theorem cell23_2706691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_2706691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706691 prefixEnd_2706691 := by exact prefixLift 2706691
  have htrace : WordTrace (prefixWord ++ tailWord_2706691) baseStart_2706691 baseEnd_2706691 := by
    simpa [prefixWord, tailWord_2706691, baseEnd_2706691] using wordTrace_append hprefix tailTrace_2706691
  have hstable : (prefixWord ++ tailWord_2706691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706691).length < 2 ^ (prefixWord ++ tailWord_2706691).sum := by decide
  have hdescent : baseEnd_2706691 < baseStart_2706691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706737 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_2706737 : Nat := 118140960795 + 2706737 * 2 ^ 59
def prefixEnd_2706737 : Nat := 4983230072969 + 3 ^ 40 * 2706737 * 2
def baseEnd_2706737 : Nat := 1389857086308881612739449

theorem tailTrace_2706737 : CollatzResearch.WordTrace tailWord_2706737 prefixEnd_2706737 1389857086308881612739449 := by
  unfold tailWord_2706737
  simp only [CollatzResearch.WordTrace]
  refine ⟨98722808794961597721206465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65815205863307731814137643 98722808794961597721206465)
  ·
    refine ⟨74042106596221198290904849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98722808794961597721206465 74042106596221198290904849)
    ·
      refine ⟨55531579947165898718178637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74042106596221198290904849 55531579947165898718178637)
      ·
        refine ⟨20824342480187212019316989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55531579947165898718178637 20824342480187212019316989)
        ·
          refine ⟨7809128430070204507243871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20824342480187212019316989 7809128430070204507243871)
          ·
            refine ⟨11713692645105306760865807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809128430070204507243871 11713692645105306760865807)
            ·
              refine ⟨17570538967657960141298711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11713692645105306760865807 17570538967657960141298711)
              ·
                refine ⟨26355808451486940211948067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17570538967657960141298711 26355808451486940211948067)
                ·
                  refine ⟨39533712677230410317922101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26355808451486940211948067 39533712677230410317922101)
                  ·
                    refine ⟨3706285563490350967305197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39533712677230410317922101 3706285563490350967305197)
                    ·
                      refine ⟨1389857086308881612739449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706285563490350967305197 1389857086308881612739449)
                      ·
                        rfl

theorem cell23_2706737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_2706737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706737 prefixEnd_2706737 := by exact prefixLift 2706737
  have htrace : WordTrace (prefixWord ++ tailWord_2706737) baseStart_2706737 baseEnd_2706737 := by
    simpa [prefixWord, tailWord_2706737, baseEnd_2706737] using wordTrace_append hprefix tailTrace_2706737
  have hstable : (prefixWord ++ tailWord_2706737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706737).length < 2 ^ (prefixWord ++ tailWord_2706737).sum := by decide
  have hdescent : baseEnd_2706737 < baseStart_2706737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706777 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_2706777 : Nat := 118140960795 + 2706777 * 2 ^ 59
def prefixEnd_2706777 : Nat := 4983230072969 + 3 ^ 40 * 2706777 * 2
def baseEnd_2706777 : Nat := 1389877625535061456239265

theorem tailTrace_2706777 : CollatzResearch.WordTrace tailWord_2706777 prefixEnd_2706777 1389877625535061456239265 := by
  unfold tailWord_2706777
  simp only [CollatzResearch.WordTrace]
  refine ⟨98724267714816684552662585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65816178476544456368441723 98724267714816684552662585)
  ·
    refine ⟨74043200786112513414496939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98724267714816684552662585 74043200786112513414496939)
    ·
      refine ⟨111064801179168770121745409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74043200786112513414496939 111064801179168770121745409)
      ·
        refine ⟨83298600884376577591309057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111064801179168770121745409 83298600884376577591309057)
        ·
          refine ⟨62473950663282433193481793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83298600884376577591309057 62473950663282433193481793)
          ·
            refine ⟨46855462997461824895111345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62473950663282433193481793 46855462997461824895111345)
            ·
              refine ⟨35141597248096368671333509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46855462997461824895111345 35141597248096368671333509)
              ·
                refine ⟨6589049484018069125875033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35141597248096368671333509 6589049484018069125875033)
                ·
                  refine ⟨4941787113013551844406275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6589049484018069125875033 4941787113013551844406275)
                  ·
                    refine ⟨7412680669520327766609413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4941787113013551844406275 7412680669520327766609413)
                    ·
                      refine ⟨1389877625535061456239265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7412680669520327766609413 1389877625535061456239265)
                      ·
                        rfl

theorem cell23_2706777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_2706777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706777 prefixEnd_2706777 := by exact prefixLift 2706777
  have htrace : WordTrace (prefixWord ++ tailWord_2706777) baseStart_2706777 baseEnd_2706777 := by
    simpa [prefixWord, tailWord_2706777, baseEnd_2706777] using wordTrace_append hprefix tailTrace_2706777
  have hstable : (prefixWord ++ tailWord_2706777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706777).length < 2 ^ (prefixWord ++ tailWord_2706777).sum := by decide
  have hdescent : baseEnd_2706777 < baseStart_2706777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706821 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_2706821 : Nat := 118140960795 + 2706821 * 2 ^ 59
def prefixEnd_2706821 : Nat := 4983230072969 + 3 ^ 40 * 2706821 * 2
def baseEnd_2706821 : Nat := 463300072894619761363021

theorem tailTrace_2706821 : CollatzResearch.WordTrace tailWord_2706821 prefixEnd_2706821 463300072894619761363021 := by
  unfold tailWord_2706821
  simp only [CollatzResearch.WordTrace]
  refine ⟨98725872526657280067264317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65817248351104853378176211 98725872526657280067264317)
  ·
    refine ⟨37022202197496480025224119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98725872526657280067264317 37022202197496480025224119)
    ·
      refine ⟨55533303296244720037836179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37022202197496480025224119 55533303296244720037836179)
      ·
        refine ⟨83299954944367080056754269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55533303296244720037836179 83299954944367080056754269)
        ·
          refine ⟨31237483104137655021282851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83299954944367080056754269 31237483104137655021282851)
          ·
            refine ⟨46856224656206482531924277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31237483104137655021282851 46856224656206482531924277)
            ·
              refine ⟨4392771061519357737367901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46856224656206482531924277 4392771061519357737367901)
              ·
                refine ⟨1647289148069759151512963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392771061519357737367901 1647289148069759151512963)
                ·
                  refine ⟨2470933722104638727269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647289148069759151512963 2470933722104638727269445)
                  ·
                    refine ⟨463300072894619761363021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2470933722104638727269445 463300072894619761363021)
                    ·
                      rfl

theorem cell23_2706821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_2706821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706821 prefixEnd_2706821 := by exact prefixLift 2706821
  have htrace : WordTrace (prefixWord ++ tailWord_2706821) baseStart_2706821 baseEnd_2706821 := by
    simpa [prefixWord, tailWord_2706821, baseEnd_2706821] using wordTrace_append hprefix tailTrace_2706821
  have hstable : (prefixWord ++ tailWord_2706821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706821).length < 2 ^ (prefixWord ++ tailWord_2706821).sum := by decide
  have hdescent : baseEnd_2706821 < baseStart_2706821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706871 : List Nat := [1, 1, 3, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_2706871 : Nat := 118140960795 + 2706871 * 2 ^ 59
def prefixEnd_2706871 : Nat := 4983230072969 + 3 ^ 40 * 2706871 * 2
def baseEnd_2706871 : Nat := 1389925892716584088463833

theorem tailTrace_2706871 : CollatzResearch.WordTrace tailWord_2706871 prefixEnd_2706871 1389925892716584088463833 := by
  unfold tailWord_2706871
  simp only [CollatzResearch.WordTrace]
  refine ⟨98727696176476138606584467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65818464117650759071056311 98727696176476138606584467)
  ·
    refine ⟨148091544264714207909876701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98727696176476138606584467 148091544264714207909876701)
    ·
      refine ⟨55534329099267827966203763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148091544264714207909876701 55534329099267827966203763)
      ·
        refine ⟨83301493648901741949305645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55534329099267827966203763 83301493648901741949305645)
        ·
          refine ⟨31238060118338153230989617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83301493648901741949305645 31238060118338153230989617)
          ·
            refine ⟨23428545088753614923242213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31238060118338153230989617 23428545088753614923242213)
            ·
              refine ⟨4392852204141302798107915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23428545088753614923242213 4392852204141302798107915)
              ·
                refine ⟨6589278306211954197161873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392852204141302798107915 6589278306211954197161873)
                ·
                  refine ⟨4941958729658965647871405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6589278306211954197161873 4941958729658965647871405)
                  ·
                    refine ⟨1853234523622112117951777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4941958729658965647871405 1853234523622112117951777)
                    ·
                      refine ⟨1389925892716584088463833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853234523622112117951777 1389925892716584088463833)
                      ·
                        rfl

theorem cell23_2706871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_2706871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706871 prefixEnd_2706871 := by exact prefixLift 2706871
  have htrace : WordTrace (prefixWord ++ tailWord_2706871) baseStart_2706871 baseEnd_2706871 := by
    simpa [prefixWord, tailWord_2706871, baseEnd_2706871] using wordTrace_append hprefix tailTrace_2706871
  have hstable : (prefixWord ++ tailWord_2706871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706871).length < 2 ^ (prefixWord ++ tailWord_2706871).sum := by decide
  have hdescent : baseEnd_2706871 < baseStart_2706871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706878 : List Nat := [4, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_2706878 : Nat := 118140960795 + 2706878 * 2 ^ 59
def prefixEnd_2706878 : Nat := 4983230072969 + 3 ^ 40 * 2706878 * 2
def baseEnd_2706878 : Nat := 1389929487081165561076301

theorem tailTrace_2706878 : CollatzResearch.WordTrace tailWord_2706878 prefixEnd_2706878 1389929487081165561076301 := by
  unfold tailWord_2706878
  simp only [CollatzResearch.WordTrace]
  refine ⟨12340993935931347350261161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65818634324967185868059525 12340993935931347350261161)
  ·
    refine ⟨9255745451948510512695871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12340993935931347350261161 9255745451948510512695871)
    ·
      refine ⟨13883618177922765769043807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9255745451948510512695871 13883618177922765769043807)
      ·
        refine ⟨20825427266884148653565711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13883618177922765769043807 20825427266884148653565711)
        ·
          refine ⟨31238140900326222980348567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20825427266884148653565711 31238140900326222980348567)
          ·
            refine ⟨46857211350489334470522851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31238140900326222980348567 46857211350489334470522851)
            ·
              refine ⟨70285817025734001705784277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46857211350489334470522851 70285817025734001705784277)
              ·
                refine ⟨1647323836540640664979319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70285817025734001705784277 1647323836540640664979319)
                ·
                  refine ⟨2470985754810960997468979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647323836540640664979319 2470985754810960997468979)
                  ·
                    refine ⟨3706478632216441496203469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470985754810960997468979 3706478632216441496203469)
                    ·
                      refine ⟨1389929487081165561076301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706478632216441496203469 1389929487081165561076301)
                      ·
                        rfl

theorem cell23_2706878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_2706878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706878 prefixEnd_2706878 := by exact prefixLift 2706878
  have htrace : WordTrace (prefixWord ++ tailWord_2706878) baseStart_2706878 baseEnd_2706878 := by
    simpa [prefixWord, tailWord_2706878, baseEnd_2706878] using wordTrace_append hprefix tailTrace_2706878
  have hstable : (prefixWord ++ tailWord_2706878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706878).length < 2 ^ (prefixWord ++ tailWord_2706878).sum := by decide
  have hdescent : baseEnd_2706878 < baseStart_2706878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706894 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_2706894 : Nat := 118140960795 + 2706894 * 2 ^ 59
def prefixEnd_2706894 : Nat := 4983230072969 + 3 ^ 40 * 2706894 * 2
def baseEnd_2706894 : Nat := 463312567590545832825409

theorem tailTrace_2706894 : CollatzResearch.WordTrace tailWord_2706894 prefixEnd_2706894 463312567590545832825409 := by
  unfold tailWord_2706894
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341066881924101691833967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65819023370261875689781157 12341066881924101691833967)
  ·
    refine ⟨18511600322886152537750951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12341066881924101691833967 18511600322886152537750951)
    ·
      refine ⟨27767400484329228806626427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18511600322886152537750951 27767400484329228806626427)
      ·
        refine ⟨41651100726493843209939641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27767400484329228806626427 41651100726493843209939641)
        ·
          refine ⟨31238325544870382407454731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41651100726493843209939641 31238325544870382407454731)
          ·
            refine ⟨46857488317305573611182097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31238325544870382407454731 46857488317305573611182097)
            ·
              refine ⟨35143116237979180208386573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46857488317305573611182097 35143116237979180208386573)
              ·
                refine ⟨13178668589242192578144965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35143116237979180208386573 13178668589242192578144965)
                ·
                  refine ⟨2471000360482911108402181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13178668589242192578144965 2471000360482911108402181)
                  ·
                    refine ⟨463312567590545832825409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471000360482911108402181 463312567590545832825409)
                    ·
                      rfl

theorem cell23_2706894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_2706894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706894 prefixEnd_2706894 := by exact prefixLift 2706894
  have htrace : WordTrace (prefixWord ++ tailWord_2706894) baseStart_2706894 baseEnd_2706894 := by
    simpa [prefixWord, tailWord_2706894, baseEnd_2706894] using wordTrace_append hprefix tailTrace_2706894
  have hstable : (prefixWord ++ tailWord_2706894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706894).length < 2 ^ (prefixWord ++ tailWord_2706894).sum := by decide
  have hdescent : baseEnd_2706894 < baseStart_2706894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706904 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_2706904 : Nat := 118140960795 + 2706904 * 2 ^ 59
def prefixEnd_2706904 : Nat := 4983230072969 + 3 ^ 40 * 2706904 * 2
def baseEnd_2706904 : Nat := 1389942837578182459351181

theorem tailTrace_2706904 : CollatzResearch.WordTrace tailWord_2706904 prefixEnd_2706904 1389942837578182459351181 := by
  unfold tailWord_2706904
  simp only [CollatzResearch.WordTrace]
  refine ⟨49364449892678292621267883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65819266523571056828357177 49364449892678292621267883)
  ·
    refine ⟨74046674839017438931901825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49364449892678292621267883 74046674839017438931901825)
    ·
      refine ⟨55535006129263079198926369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74046674839017438931901825 55535006129263079198926369)
      ·
        refine ⟨41651254596947309399194777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55535006129263079198926369 41651254596947309399194777)
        ·
          refine ⟨31238440947710482049396083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41651254596947309399194777 31238440947710482049396083)
          ·
            refine ⟨46857661421565723074094125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31238440947710482049396083 46857661421565723074094125)
            ·
              refine ⟨17571623033087146152785297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46857661421565723074094125 17571623033087146152785297)
              ·
                refine ⟨13178717274815359614588973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17571623033087146152785297 13178717274815359614588973)
                ·
                  refine ⟨4942018978055759855470865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13178717274815359614588973 4942018978055759855470865)
                  ·
                    refine ⟨3706514233541819891603149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4942018978055759855470865 3706514233541819891603149)
                    ·
                      refine ⟨1389942837578182459351181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706514233541819891603149 1389942837578182459351181)
                      ·
                        rfl

theorem cell23_2706904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_2706904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706904 prefixEnd_2706904 := by exact prefixLift 2706904
  have htrace : WordTrace (prefixWord ++ tailWord_2706904) baseStart_2706904 baseEnd_2706904 := by
    simpa [prefixWord, tailWord_2706904, baseEnd_2706904] using wordTrace_append hprefix tailTrace_2706904
  have hstable : (prefixWord ++ tailWord_2706904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706904).length < 2 ^ (prefixWord ++ tailWord_2706904).sum := by decide
  have hdescent : baseEnd_2706904 < baseStart_2706904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706945 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2706945 : Nat := 118140960795 + 2706945 * 2 ^ 59
def prefixEnd_2706945 : Nat := 4983230072969 + 3 ^ 40 * 2706945 * 2
def baseEnd_2706945 : Nat := 463321296761672266312831

theorem tailTrace_2706945 : CollatzResearch.WordTrace tailWord_2706945 prefixEnd_2706945 463321296761672266312831 := by
  unfold tailWord_2706945
  simp only [CollatzResearch.WordTrace]
  refine ⟨98730395178208049244778289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65820263452138699496518859 98730395178208049244778289)
  ·
    refine ⟨74047796383656036933583717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98730395178208049244778289 74047796383656036933583717)
    ·
      refine ⟨13883961821935506925046947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74047796383656036933583717 13883961821935506925046947)
      ·
        refine ⟨20825942732903260387570421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13883961821935506925046947 20825942732903260387570421)
        ·
          refine ⟨1952432131209680661334727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20825942732903260387570421 1952432131209680661334727)
          ·
            refine ⟨2928648196814520992002091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952432131209680661334727 2928648196814520992002091)
            ·
              refine ⟨4392972295221781488003137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928648196814520992002091 4392972295221781488003137)
              ·
                refine ⟨3294729221416336116002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392972295221781488003137 3294729221416336116002353)
                ·
                  refine ⟨2471046916062252087001765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294729221416336116002353 2471046916062252087001765)
                  ·
                    refine ⟨463321296761672266312831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471046916062252087001765 463321296761672266312831)
                    ·
                      rfl

theorem cell23_2706945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2706945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706945 prefixEnd_2706945 := by exact prefixLift 2706945
  have htrace : WordTrace (prefixWord ++ tailWord_2706945) baseStart_2706945 baseEnd_2706945 := by
    simpa [prefixWord, tailWord_2706945, baseEnd_2706945] using wordTrace_append hprefix tailTrace_2706945
  have hstable : (prefixWord ++ tailWord_2706945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706945).length < 2 ^ (prefixWord ++ tailWord_2706945).sum := by decide
  have hdescent : baseEnd_2706945 < baseStart_2706945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706947 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5]
def baseStart_2706947 : Nat := 118140960795 + 2706947 * 2 ^ 59
def prefixEnd_2706947 : Nat := 4983230072969 + 3 ^ 40 * 2706947 * 2
def baseEnd_2706947 : Nat := 1389964917246325791113483

theorem tailTrace_2706947 : CollatzResearch.WordTrace tailWord_2706947 prefixEnd_2706947 1389964917246325791113483 := by
  unfold tailWord_2706947
  simp only [CollatzResearch.WordTrace]
  refine ⟨98730468124200803586351095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65820312082800535724234063 98730468124200803586351095)
  ·
    refine ⟨148095702186301205379526643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98730468124200803586351095 148095702186301205379526643)
    ·
      refine ⟨222143553279451808069289965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148095702186301205379526643 222143553279451808069289965)
      ·
        refine ⟨83303832479794428025983737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222143553279451808069289965 83303832479794428025983737)
        ·
          refine ⟨62477874359845821019487803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83303832479794428025983737 62477874359845821019487803)
          ·
            refine ⟨93716811539768731529231705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62477874359845821019487803 93716811539768731529231705)
            ·
              refine ⟨70287608654826548646923779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93716811539768731529231705 70287608654826548646923779)
              ·
                refine ⟨105431412982239822970385669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70287608654826548646923779 105431412982239822970385669)
                ·
                  refine ⟨19768389934169966806947313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105431412982239822970385669 19768389934169966806947313)
                  ·
                    refine ⟨14826292450627475105210485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19768389934169966806947313 14826292450627475105210485)
                    ·
                      refine ⟨1389964917246325791113483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14826292450627475105210485 1389964917246325791113483)
                      ·
                        rfl

theorem cell23_2706947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_2706947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706947 prefixEnd_2706947 := by exact prefixLift 2706947
  have htrace : WordTrace (prefixWord ++ tailWord_2706947) baseStart_2706947 baseEnd_2706947 := by
    simpa [prefixWord, tailWord_2706947, baseEnd_2706947] using wordTrace_append hprefix tailTrace_2706947
  have hstable : (prefixWord ++ tailWord_2706947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706947).length < 2 ^ (prefixWord ++ tailWord_2706947).sum := by decide
  have hdescent : baseEnd_2706947 < baseStart_2706947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706968 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2706968 : Nat := 118140960795 + 2706968 * 2 ^ 59
def prefixEnd_2706968 : Nat := 4983230072969 + 3 ^ 40 * 2706968 * 2
def baseEnd_2706968 : Nat := 1389975700340070208950887

theorem tailTrace_2706968 : CollatzResearch.WordTrace tailWord_2706968 prefixEnd_2706968 1389975700340070208950887 := by
  unfold tailWord_2706968
  simp only [CollatzResearch.WordTrace]
  refine ⟨49365617028562362086432779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65820822704749816115243705 49365617028562362086432779)
  ·
    refine ⟨74048425542843543129649169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49365617028562362086432779 74048425542843543129649169)
    ·
      refine ⟨55536319157132657347236877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74048425542843543129649169 55536319157132657347236877)
      ·
        refine ⟨20826119683924746505213829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55536319157132657347236877 20826119683924746505213829)
        ·
          refine ⟨3904897440735889969727593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20826119683924746505213829 3904897440735889969727593)
          ·
            refine ⟨2928673080551917477295695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904897440735889969727593 2928673080551917477295695)
            ·
              refine ⟨4393009620827876215943543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928673080551917477295695 4393009620827876215943543)
              ·
                refine ⟨6589514431241814323915315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393009620827876215943543 6589514431241814323915315)
                ·
                  refine ⟨9884271646862721485872973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6589514431241814323915315 9884271646862721485872973)
                  ·
                    refine ⟨3706601867573520557202365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9884271646862721485872973 3706601867573520557202365)
                    ·
                      refine ⟨1389975700340070208950887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706601867573520557202365 1389975700340070208950887)
                      ·
                        rfl

theorem cell23_2706968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2706968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706968 prefixEnd_2706968 := by exact prefixLift 2706968
  have htrace : WordTrace (prefixWord ++ tailWord_2706968) baseStart_2706968 baseEnd_2706968 := by
    simpa [prefixWord, tailWord_2706968, baseEnd_2706968] using wordTrace_append hprefix tailTrace_2706968
  have hstable : (prefixWord ++ tailWord_2706968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706968).length < 2 ^ (prefixWord ++ tailWord_2706968).sum := by decide
  have hdescent : baseEnd_2706968 < baseStart_2706968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706978 : List Nat := [3, 3, 1, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_2706978 : Nat := 118140960795 + 2706978 * 2 ^ 59
def prefixEnd_2706978 : Nat := 4983230072969 + 3 ^ 40 * 2706978 * 2
def baseEnd_2706978 : Nat := 1389980835146615169825841

theorem tailTrace_2706978 : CollatzResearch.WordTrace tailWord_2706978 prefixEnd_2706978 1389980835146615169825841 := by
  unfold tailWord_2706978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24682899696772123970182397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65821065858058997253819725 24682899696772123970182397)
  ·
    refine ⟨9256087386289546488818399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24682899696772123970182397 9256087386289546488818399)
    ·
      refine ⟨13884131079434319733227599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9256087386289546488818399 13884131079434319733227599)
      ·
        refine ⟨20826196619151479599841399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13884131079434319733227599 20826196619151479599841399)
        ·
          refine ⟨31239294928727219399762099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20826196619151479599841399 31239294928727219399762099)
          ·
            refine ⟨46858942393090829099643149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31239294928727219399762099 46858942393090829099643149)
            ·
              refine ⟨17572103397409060912366181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46858942393090829099643149 17572103397409060912366181)
              ·
                refine ⟨3294769387014198921068659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17572103397409060912366181 3294769387014198921068659)
                ·
                  refine ⟨4942154080521298381602989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294769387014198921068659 4942154080521298381602989)
                  ·
                    refine ⟨1853307780195486893101121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4942154080521298381602989 1853307780195486893101121)
                    ·
                      refine ⟨1389980835146615169825841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853307780195486893101121 1389980835146615169825841)
                      ·
                        rfl

theorem cell23_2706978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_2706978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706978 prefixEnd_2706978 := by exact prefixLift 2706978
  have htrace : WordTrace (prefixWord ++ tailWord_2706978) baseStart_2706978 baseEnd_2706978 := by
    simpa [prefixWord, tailWord_2706978, baseEnd_2706978] using wordTrace_append hprefix tailTrace_2706978
  have hstable : (prefixWord ++ tailWord_2706978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706978).length < 2 ^ (prefixWord ++ tailWord_2706978).sum := by decide
  have hdescent : baseEnd_2706978 < baseStart_2706978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2706994 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_2706994 : Nat := 118140960795 + 2706994 * 2 ^ 59
def prefixEnd_2706994 : Nat := 4983230072969 + 3 ^ 40 * 2706994 * 2
def baseEnd_2706994 : Nat := 1389989050837087107225767

theorem tailTrace_2706994 : CollatzResearch.WordTrace tailWord_2706994 prefixEnd_2706994 1389989050837087107225767 := by
  unfold tailWord_2706994
  simp only [CollatzResearch.WordTrace]
  refine ⟨24683045588757632653328009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65821454903353687075541357 24683045588757632653328009)
  ·
    refine ⟨18512284191568224489996007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24683045588757632653328009 18512284191568224489996007)
    ·
      refine ⟨27768426287352336734994011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18512284191568224489996007 27768426287352336734994011)
      ·
        refine ⟨41652639431028505102491017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27768426287352336734994011 41652639431028505102491017)
        ·
          refine ⟨31239479573271378826868263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41652639431028505102491017 31239479573271378826868263)
          ·
            refine ⟨46859219359907068240302395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31239479573271378826868263 46859219359907068240302395)
            ·
              refine ⟨70288829039860602360453593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46859219359907068240302395 70288829039860602360453593)
              ·
                refine ⟨52716621779895451770340195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70288829039860602360453593 52716621779895451770340195)
                ·
                  refine ⟨79074932669843177655510293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52716621779895451770340195 79074932669843177655510293)
                  ·
                    refine ⟨3706637468898898952602045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79074932669843177655510293 3706637468898898952602045)
                    ·
                      refine ⟨1389989050837087107225767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706637468898898952602045 1389989050837087107225767)
                      ·
                        rfl

theorem cell23_2706994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_2706994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2706994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2706994 prefixEnd_2706994 := by exact prefixLift 2706994
  have htrace : WordTrace (prefixWord ++ tailWord_2706994) baseStart_2706994 baseEnd_2706994 := by
    simpa [prefixWord, tailWord_2706994, baseEnd_2706994] using wordTrace_append hprefix tailTrace_2706994
  have hstable : (prefixWord ++ tailWord_2706994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2706994).length < 2 ^ (prefixWord ++ tailWord_2706994).sum := by decide
  have hdescent : baseEnd_2706994 < baseStart_2706994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2706994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707008 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2]
def baseStart_2707008 : Nat := 118140960795 + 2707008 * 2 ^ 59
def prefixEnd_2707008 : Nat := 4983230072969 + 3 ^ 40 * 2707008 * 2
def baseEnd_2707008 : Nat := 1389996239566250052450703

theorem tailTrace_2707008 : CollatzResearch.WordTrace tailWord_2707008 prefixEnd_2707008 1389996239566250052450703 := by
  unfold tailWord_2707008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49366346488489905502160839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65821795317986540669547785 49366346488489905502160839)
  ·
    refine ⟨74049519732734858253241259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49366346488489905502160839 74049519732734858253241259)
    ·
      refine ⟨111074279599102287379861889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74049519732734858253241259 111074279599102287379861889)
      ·
        refine ⟨83305709699326715534896417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111074279599102287379861889 83305709699326715534896417)
        ·
          refine ⟨62479282274495036651172313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83305709699326715534896417 62479282274495036651172313)
          ·
            refine ⟨46859461705871277488379235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62479282274495036651172313 46859461705871277488379235)
            ·
              refine ⟨70289192558806916232568853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46859461705871277488379235 70289192558806916232568853)
              ·
                refine ⟨3294805901194074198401665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70289192558806916232568853 3294805901194074198401665)
                ·
                  refine ⟨2471104425895555648801249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3294805901194074198401665 2471104425895555648801249)
                  ·
                    refine ⟨1853328319421666736600937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2471104425895555648801249 1853328319421666736600937)
                    ·
                      refine ⟨1389996239566250052450703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853328319421666736600937 1389996239566250052450703)
                      ·
                        rfl

theorem cell23_2707008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_2707008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707008 prefixEnd_2707008 := by exact prefixLift 2707008
  have htrace : WordTrace (prefixWord ++ tailWord_2707008) baseStart_2707008 baseEnd_2707008 := by
    simpa [prefixWord, tailWord_2707008, baseEnd_2707008] using wordTrace_append hprefix tailTrace_2707008
  have hstable : (prefixWord ++ tailWord_2707008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707008).length < 2 ^ (prefixWord ++ tailWord_2707008).sum := by decide
  have hdescent : baseEnd_2707008 < baseStart_2707008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707024 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_2707024 : Nat := 118140960795 + 2707024 * 2 ^ 59
def prefixEnd_2707024 : Nat := 4983230072969 + 3 ^ 40 * 2707024 * 2
def baseEnd_2707024 : Nat := 1390004455256721989850629

theorem tailTrace_2707024 : CollatzResearch.WordTrace tailWord_2707024 prefixEnd_2707024 1390004455256721989850629 := by
  unfold tailWord_2707024
  simp only [CollatzResearch.WordTrace]
  refine ⟨49366638272460922868452063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65822184363281230491269417 49366638272460922868452063)
  ·
    refine ⟨74049957408691384302678095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49366638272460922868452063 74049957408691384302678095)
    ·
      refine ⟨111074936113037076454017143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74049957408691384302678095 111074936113037076454017143)
      ·
        refine ⟨166612404169555614681025715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111074936113037076454017143 166612404169555614681025715)
        ·
          refine ⟨249918606254333422021538573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166612404169555614681025715 249918606254333422021538573)
          ·
            refine ⟨93719477345375033258076965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249918606254333422021538573 93719477345375033258076965)
            ·
              refine ⟨17572402002257818735889431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93719477345375033258076965 17572402002257818735889431)
              ·
                refine ⟨26358603003386728103834147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17572402002257818735889431 26358603003386728103834147)
                ·
                  refine ⟨39537904505080092155751221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26358603003386728103834147 39537904505080092155751221)
                  ·
                    refine ⟨3706678547351258639601677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39537904505080092155751221 3706678547351258639601677)
                    ·
                      refine ⟨1390004455256721989850629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706678547351258639601677 1390004455256721989850629)
                      ·
                        rfl

theorem cell23_2707024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_2707024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707024 prefixEnd_2707024 := by exact prefixLift 2707024
  have htrace : WordTrace (prefixWord ++ tailWord_2707024) baseStart_2707024 baseEnd_2707024 := by
    simpa [prefixWord, tailWord_2707024, baseEnd_2707024] using wordTrace_append hprefix tailTrace_2707024
  have hstable : (prefixWord ++ tailWord_2707024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707024).length < 2 ^ (prefixWord ++ tailWord_2707024).sum := by decide
  have hdescent : baseEnd_2707024 < baseStart_2707024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707081 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 6, 2]
def baseStart_2707081 : Nat := 118140960795 + 2707081 * 2 ^ 59
def prefixEnd_2707081 : Nat := 4983230072969 + 3 ^ 40 * 2707081 * 2
def baseEnd_2707081 : Nat := 1390033723654028266837867

theorem tailTrace_2707081 : CollatzResearch.WordTrace tailWord_2707081 prefixEnd_2707081 1390033723654028266837867 := by
  unfold tailWord_2707081
  simp only [CollatzResearch.WordTrace]
  refine ⟨98735355505715344471729097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65823570337143562981152731 98735355505715344471729097)
  ·
    refine ⟨74051516629286508353796823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98735355505715344471729097 74051516629286508353796823)
    ·
      refine ⟨111077274943929762530695235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74051516629286508353796823 111077274943929762530695235)
      ·
        refine ⟨166615912415894643796042853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111077274943929762530695235 166615912415894643796042853)
        ·
          refine ⟨31240483577980245711758035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166615912415894643796042853 31240483577980245711758035)
          ·
            refine ⟨46860725366970368567637053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31240483577980245711758035 46860725366970368567637053)
            ·
              refine ⟨17572772012613888212863895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46860725366970368567637053 17572772012613888212863895)
              ·
                refine ⟨26359158018920832319295843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17572772012613888212863895 26359158018920832319295843)
                ·
                  refine ⟨39538737028381248478943765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26359158018920832319295843 39538737028381248478943765)
                  ·
                    refine ⟨1853378298205371022450489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39538737028381248478943765 1853378298205371022450489)
                    ·
                      refine ⟨1390033723654028266837867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853378298205371022450489 1390033723654028266837867)
                      ·
                        rfl

theorem cell23_2707081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 6, 2].length) (baseStart_2707081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707081 prefixEnd_2707081 := by exact prefixLift 2707081
  have htrace : WordTrace (prefixWord ++ tailWord_2707081) baseStart_2707081 baseEnd_2707081 := by
    simpa [prefixWord, tailWord_2707081, baseEnd_2707081] using wordTrace_append hprefix tailTrace_2707081
  have hstable : (prefixWord ++ tailWord_2707081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707081).length < 2 ^ (prefixWord ++ tailWord_2707081).sum := by decide
  have hdescent : baseEnd_2707081 < baseStart_2707081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707125 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2707125 : Nat := 118140960795 + 2707125 * 2 ^ 59
def prefixEnd_2707125 : Nat := 4983230072969 + 3 ^ 40 * 2707125 * 2
def baseEnd_2707125 : Nat := 463352105600942031562555

theorem tailTrace_2707125 : CollatzResearch.WordTrace tailWord_2707125 prefixEnd_2707125 463352105600942031562555 := by
  unfold tailWord_2707125
  simp only [CollatzResearch.WordTrace]
  refine ⟨98736960317555939986330829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65824640211703959990887219 98736960317555939986330829)
  ·
    refine ⟨37026360119083477494874061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98736960317555939986330829 37026360119083477494874061)
    ·
      refine ⟨13884885044656304060577773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37026360119083477494874061 13884885044656304060577773)
      ·
        refine ⟨5206831891746114022716665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13884885044656304060577773 5206831891746114022716665)
        ·
          refine ⟨3905123918809585517037499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5206831891746114022716665 3905123918809585517037499)
          ·
            refine ⟨5857685878214378275556249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905123918809585517037499 5857685878214378275556249)
            ·
              refine ⟨4393264408660783706667187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5857685878214378275556249 4393264408660783706667187)
              ·
                refine ⟨6589896612991175560000781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393264408660783706667187 6589896612991175560000781)
                ·
                  refine ⟨2471211229871690835000293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6589896612991175560000781 2471211229871690835000293)
                  ·
                    refine ⟨463352105600942031562555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471211229871690835000293 463352105600942031562555)
                    ·
                      rfl

theorem cell23_2707125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2707125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707125 prefixEnd_2707125 := by exact prefixLift 2707125
  have htrace : WordTrace (prefixWord ++ tailWord_2707125) baseStart_2707125 baseEnd_2707125 := by
    simpa [prefixWord, tailWord_2707125, baseEnd_2707125] using wordTrace_append hprefix tailTrace_2707125
  have hstable : (prefixWord ++ tailWord_2707125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707125).length < 2 ^ (prefixWord ++ tailWord_2707125).sum := by decide
  have hdescent : baseEnd_2707125 < baseStart_2707125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707142 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2707142 : Nat := 118140960795 + 2707142 * 2 ^ 59
def prefixEnd_2707142 : Nat := 4983230072969 + 3 ^ 40 * 2707142 * 2
def baseEnd_2707142 : Nat := 463355015324650842725029

theorem tailTrace_2707142 : CollatzResearch.WordTrace tailWord_2707142 prefixEnd_2707142 463355015324650842725029 := by
  unfold tailWord_2707142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085549386202948496553115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65825053572329567926466453 3085549386202948496553115)
  ·
    refine ⟨4628324079304422744829673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085549386202948496553115 4628324079304422744829673)
    ·
      refine ⟨3471243059478317058622255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4628324079304422744829673 3471243059478317058622255)
      ·
        refine ⟨5206864589217475587933383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471243059478317058622255 5206864589217475587933383)
        ·
          refine ⟨7810296883826213381900075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206864589217475587933383 7810296883826213381900075)
          ·
            refine ⟨11715445325739320072850113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7810296883826213381900075 11715445325739320072850113)
            ·
              refine ⟨8786583994304490054637585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11715445325739320072850113 8786583994304490054637585)
              ·
                refine ⟨6589937995728367540978189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8786583994304490054637585 6589937995728367540978189)
                ·
                  refine ⟨2471226748398137827866821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6589937995728367540978189 2471226748398137827866821)
                  ·
                    refine ⟨463355015324650842725029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471226748398137827866821 463355015324650842725029)
                    ·
                      rfl

theorem cell23_2707142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2707142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707142 prefixEnd_2707142 := by exact prefixLift 2707142
  have htrace : WordTrace (prefixWord ++ tailWord_2707142) baseStart_2707142 baseEnd_2707142 := by
    simpa [prefixWord, tailWord_2707142, baseEnd_2707142] using wordTrace_append hprefix tailTrace_2707142
  have hstable : (prefixWord ++ tailWord_2707142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707142).length < 2 ^ (prefixWord ++ tailWord_2707142).sum := by decide
  have hdescent : baseEnd_2707142 < baseStart_2707142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707191 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5]
def baseStart_2707191 : Nat := 118140960795 + 2707191 * 2 ^ 59
def prefixEnd_2707191 : Nat := 4983230072969 + 3 ^ 40 * 2707191 * 2
def baseEnd_2707191 : Nat := 1390090206526022836462361

theorem tailTrace_2707191 : CollatzResearch.WordTrace tailWord_2707191 prefixEnd_2707191 1390090206526022836462361 := by
  unfold tailWord_2707191
  simp only [CollatzResearch.WordTrace]
  refine ⟨98739367535316833258233427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65826245023544555505488951 98739367535316833258233427)
  ·
    refine ⟨148109051302975249887350141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98739367535316833258233427 148109051302975249887350141)
    ·
      refine ⟨55540894238615718707756303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148109051302975249887350141 55540894238615718707756303)
      ·
        refine ⟨83311341357923578061634455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55540894238615718707756303 83311341357923578061634455)
        ·
          refine ⟨124967012036885367092451683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83311341357923578061634455 124967012036885367092451683)
          ·
            refine ⟨187450518055328050638677525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124967012036885367092451683 187450518055328050638677525)
            ·
              refine ⟨8786743033843502373688009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 187450518055328050638677525 8786743033843502373688009)
              ·
                refine ⟨6590057275382626780266007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8786743033843502373688009 6590057275382626780266007)
                ·
                  refine ⟨9885085913073940170399011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590057275382626780266007 9885085913073940170399011)
                  ·
                    refine ⟨14827628869610910255598517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9885085913073940170399011 14827628869610910255598517)
                    ·
                      refine ⟨1390090206526022836462361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14827628869610910255598517 1390090206526022836462361)
                      ·
                        rfl

theorem cell23_2707191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_2707191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707191 prefixEnd_2707191 := by exact prefixLift 2707191
  have htrace : WordTrace (prefixWord ++ tailWord_2707191) baseStart_2707191 baseEnd_2707191 := by
    simpa [prefixWord, tailWord_2707191, baseEnd_2707191] using wordTrace_append hprefix tailTrace_2707191
  have hstable : (prefixWord ++ tailWord_2707191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707191).length < 2 ^ (prefixWord ++ tailWord_2707191).sum := by decide
  have hdescent : baseEnd_2707191 < baseStart_2707191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707201 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2707201 : Nat := 118140960795 + 2707201 * 2 ^ 59
def prefixEnd_2707201 : Nat := 4983230072969 + 3 ^ 40 * 2707201 * 2
def baseEnd_2707201 : Nat := 1390095341332567797337315

theorem tailTrace_2707201 : CollatzResearch.WordTrace tailWord_2707201 prefixEnd_2707201 1390095341332567797337315 := by
  unfold tailWord_2707201
  simp only [CollatzResearch.WordTrace]
  refine ⟨98739732265280604966097457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65826488176853736644064971 98739732265280604966097457)
  ·
    refine ⟨74054799198960453724573093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98739732265280604966097457 74054799198960453724573093)
    ·
      refine ⟨13885274849805085073357455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74054799198960453724573093 13885274849805085073357455)
      ·
        refine ⟨20827912274707627610036183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13885274849805085073357455 20827912274707627610036183)
        ·
          refine ⟨31241868412061441415054275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20827912274707627610036183 31241868412061441415054275)
          ·
            refine ⟨46862802618092162122581413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31241868412061441415054275 46862802618092162122581413)
            ·
              refine ⟨8786775490892280397984015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46862802618092162122581413 8786775490892280397984015)
              ·
                refine ⟨13180163236338420596976023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8786775490892280397984015 13180163236338420596976023)
                ·
                  refine ⟨19770244854507630895464035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13180163236338420596976023 19770244854507630895464035)
                  ·
                    refine ⟨29655367281761446343196053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19770244854507630895464035 29655367281761446343196053)
                    ·
                      refine ⟨1390095341332567797337315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29655367281761446343196053 1390095341332567797337315)
                      ·
                        rfl

theorem cell23_2707201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2707201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707201 prefixEnd_2707201 := by exact prefixLift 2707201
  have htrace : WordTrace (prefixWord ++ tailWord_2707201) baseStart_2707201 baseEnd_2707201 := by
    simpa [prefixWord, tailWord_2707201, baseEnd_2707201] using wordTrace_append hprefix tailTrace_2707201
  have hstable : (prefixWord ++ tailWord_2707201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707201).length < 2 ^ (prefixWord ++ tailWord_2707201).sum := by decide
  have hdescent : baseEnd_2707201 < baseStart_2707201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707208 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_2707208 : Nat := 118140960795 + 2707208 * 2 ^ 59
def prefixEnd_2707208 : Nat := 4983230072969 + 3 ^ 40 * 2707208 * 2
def baseEnd_2707208 : Nat := 1390098935697149269949783

theorem tailTrace_2707208 : CollatzResearch.WordTrace tailWord_2707208 prefixEnd_2707208 1390098935697149269949783 := by
  unfold tailWord_2707208
  simp only [CollatzResearch.WordTrace]
  refine ⟨49369993788127622580801139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65826658384170163441068185 49369993788127622580801139)
  ·
    refine ⟨74054990682191433871201709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49369993788127622580801139 74054990682191433871201709)
    ·
      refine ⟨27770621505821787701700641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74054990682191433871201709 27770621505821787701700641)
      ·
        refine ⟨20827966129366340776275481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27770621505821787701700641 20827966129366340776275481)
        ·
          refine ⟨15620974597024755582206611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20827966129366340776275481 15620974597024755582206611)
          ·
            refine ⟨23431461895537133373309917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15620974597024755582206611 23431461895537133373309917)
            ·
              refine ⟨8786798210826425014991219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23431461895537133373309917 8786798210826425014991219)
              ·
                refine ⟨13180197316239637522486829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8786798210826425014991219 13180197316239637522486829)
                ·
                  refine ⟨4942573993589864070932561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13180197316239637522486829 4942573993589864070932561)
                  ·
                    refine ⟨3706930495192398053199421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4942573993589864070932561 3706930495192398053199421)
                    ·
                      refine ⟨1390098935697149269949783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3706930495192398053199421 1390098935697149269949783)
                      ·
                        rfl

theorem cell23_2707208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_2707208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707208 prefixEnd_2707208 := by exact prefixLift 2707208
  have htrace : WordTrace (prefixWord ++ tailWord_2707208) baseStart_2707208 baseEnd_2707208 := by
    simpa [prefixWord, tailWord_2707208, baseEnd_2707208] using wordTrace_append hprefix tailTrace_2707208
  have hstable : (prefixWord ++ tailWord_2707208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707208).length < 2 ^ (prefixWord ++ tailWord_2707208).sum := by decide
  have hdescent : baseEnd_2707208 < baseStart_2707208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707282 : List Nat := [3, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_2707282 : Nat := 118140960795 + 2707282 * 2 ^ 59
def prefixEnd_2707282 : Nat := 4983230072969 + 3 ^ 40 * 2707282 * 2
def baseEnd_2707282 : Nat := 1390136933265581980424443

theorem tailTrace_2707282 : CollatzResearch.WordTrace tailWord_2707282 prefixEnd_2707282 1390136933265581980424443 := by
  unfold tailWord_2707282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24685671644496788949949025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65828457718658103866530733 24685671644496788949949025)
  ·
    refine ⟨18514253733372591712461769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24685671644496788949949025 18514253733372591712461769)
    ·
      refine ⟨13885690300029443784346327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18514253733372591712461769 13885690300029443784346327)
      ·
        refine ⟨20828535450044165676519491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13885690300029443784346327 20828535450044165676519491)
        ·
          refine ⟨31242803175066248514779237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20828535450044165676519491 31242803175066248514779237)
          ·
            refine ⟨5858025595324921596521107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31242803175066248514779237 5858025595324921596521107)
            ·
              refine ⟨8787038392987382394781661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858025595324921596521107 8787038392987382394781661)
              ·
                refine ⟨3295139397370268398043123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8787038392987382394781661 3295139397370268398043123)
                ·
                  refine ⟨4942709096055402597064685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295139397370268398043123 4942709096055402597064685)
                  ·
                    refine ⟨1853515911020775973899257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4942709096055402597064685 1853515911020775973899257)
                    ·
                      refine ⟨1390136933265581980424443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853515911020775973899257 1390136933265581980424443)
                      ·
                        rfl

theorem cell23_2707282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_2707282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707282 prefixEnd_2707282 := by exact prefixLift 2707282
  have htrace : WordTrace (prefixWord ++ tailWord_2707282) baseStart_2707282 baseEnd_2707282 := by
    simpa [prefixWord, tailWord_2707282, baseEnd_2707282] using wordTrace_append hprefix tailTrace_2707282
  have hstable : (prefixWord ++ tailWord_2707282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707282).length < 2 ^ (prefixWord ++ tailWord_2707282).sum := by decide
  have hdescent : baseEnd_2707282 < baseStart_2707282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707306 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2707306 : Nat := 118140960795 + 2707306 * 2 ^ 59
def prefixEnd_2707306 : Nat := 4983230072969 + 3 ^ 40 * 2707306 * 2
def baseEnd_2707306 : Nat := 1390149256801289886524333

theorem tailTrace_2707306 : CollatzResearch.WordTrace tailWord_2707306 prefixEnd_2707306 1390149256801289886524333 := by
  unfold tailWord_2707306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24685890482475051974667443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65829041286600138599113181 24685890482475051974667443)
  ·
    refine ⟨37028835723712577962001165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24685890482475051974667443 37028835723712577962001165)
    ·
      refine ⟨13885813396392216735750437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37028835723712577962001165 13885813396392216735750437)
      ·
        refine ⟨2603590011823540637953207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13885813396392216735750437 2603590011823540637953207)
        ·
          refine ⟨3905385017735310956929811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603590011823540637953207 3905385017735310956929811)
          ·
            refine ⟨5858077526602966435394717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905385017735310956929811 5858077526602966435394717)
            ·
              refine ⟨2196779072476112413273019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5858077526602966435394717 2196779072476112413273019)
              ·
                refine ⟨3295168608714168619909529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196779072476112413273019 3295168608714168619909529)
                ·
                  refine ⟨2471376456535626464932147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3295168608714168619909529 2471376456535626464932147)
                  ·
                    refine ⟨3707064684803439697398221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2471376456535626464932147 3707064684803439697398221)
                    ·
                      refine ⟨1390149256801289886524333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3707064684803439697398221 1390149256801289886524333)
                      ·
                        rfl

theorem cell23_2707306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2707306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707306 prefixEnd_2707306 := by exact prefixLift 2707306
  have htrace : WordTrace (prefixWord ++ tailWord_2707306) baseStart_2707306 baseEnd_2707306 := by
    simpa [prefixWord, tailWord_2707306, baseEnd_2707306] using wordTrace_append hprefix tailTrace_2707306
  have hstable : (prefixWord ++ tailWord_2707306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707306).length < 2 ^ (prefixWord ++ tailWord_2707306).sum := by decide
  have hdescent : baseEnd_2707306 < baseStart_2707306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707308 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2707308 : Nat := 118140960795 + 2707308 * 2 ^ 59
def prefixEnd_2707308 : Nat := 4983230072969 + 3 ^ 40 * 2707308 * 2
def baseEnd_2707308 : Nat := 1390150283762598878699323

theorem tailTrace_2707308 : CollatzResearch.WordTrace tailWord_2707308 prefixEnd_2707308 1390150283762598878699323 := by
  unfold tailWord_2707308
  simp only [CollatzResearch.WordTrace]
  refine ⟨49371817437946481120121289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65829089917261974826828385 49371817437946481120121289)
  ·
    refine ⟨37028863078459860840090967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49371817437946481120121289 37028863078459860840090967)
    ·
      refine ⟨55543294617689791260136451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37028863078459860840090967 55543294617689791260136451)
      ·
        refine ⟨83314941926534686890204677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55543294617689791260136451 83314941926534686890204677)
        ·
          refine ⟨15621551611225253791913377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83314941926534686890204677 15621551611225253791913377)
          ·
            refine ⟨11716163708418940343935033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15621551611225253791913377 11716163708418940343935033)
            ·
              refine ⟨8787122781314205257951275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11716163708418940343935033 8787122781314205257951275)
              ·
                refine ⟨13180684171971307886926913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8787122781314205257951275 13180684171971307886926913)
                ·
                  refine ⟨9885513128978480915195185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13180684171971307886926913 9885513128978480915195185)
                  ·
                    refine ⟨7414134846733860686396389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9885513128978480915195185 7414134846733860686396389)
                    ·
                      refine ⟨1390150283762598878699323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7414134846733860686396389 1390150283762598878699323)
                      ·
                        rfl

theorem cell23_2707308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2707308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707308 prefixEnd_2707308 := by exact prefixLift 2707308
  have htrace : WordTrace (prefixWord ++ tailWord_2707308) baseStart_2707308 baseEnd_2707308 := by
    simpa [prefixWord, tailWord_2707308, baseEnd_2707308] using wordTrace_append hprefix tailTrace_2707308
  have hstable : (prefixWord ++ tailWord_2707308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707308).length < 2 ^ (prefixWord ++ tailWord_2707308).sum := by decide
  have hdescent : baseEnd_2707308 < baseStart_2707308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707352 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 7]
def baseStart_2707352 : Nat := 118140960795 + 2707352 * 2 ^ 59
def prefixEnd_2707352 : Nat := 4983230072969 + 3 ^ 40 * 2707352 * 2
def baseEnd_2707352 : Nat := 154463652990155189616569

theorem tailTrace_2707352 : CollatzResearch.WordTrace tailWord_2707352 prefixEnd_2707352 154463652990155189616569 := by
  unfold tailWord_2707352
  simp only [CollatzResearch.WordTrace]
  refine ⟨49372619843866778877422155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65830159791822371836562873 49372619843866778877422155)
  ·
    refine ⟨74058929765800168316133233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49372619843866778877422155 74058929765800168316133233)
    ·
      refine ⟨55544197324350126237099925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74058929765800168316133233 55544197324350126237099925)
      ·
        refine ⟨2603634249578912167364059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55544197324350126237099925 2603634249578912167364059)
        ·
          refine ⟨3905451374368368251046089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603634249578912167364059 3905451374368368251046089)
          ·
            refine ⟨2929088530776276188284567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3905451374368368251046089 2929088530776276188284567)
            ·
              refine ⟨4393632796164414282426851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929088530776276188284567 4393632796164414282426851)
              ·
                refine ⟨6590449194246621423640277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393632796164414282426851 6590449194246621423640277)
                ·
                  refine ⟨154463652990155189616569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6590449194246621423640277 154463652990155189616569)
                  ·
                    rfl

theorem cell23_2707352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_2707352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707352 prefixEnd_2707352 := by exact prefixLift 2707352
  have htrace : WordTrace (prefixWord ++ tailWord_2707352) baseStart_2707352 baseEnd_2707352 := by
    simpa [prefixWord, tailWord_2707352, baseEnd_2707352] using wordTrace_append hprefix tailTrace_2707352
  have hstable : (prefixWord ++ tailWord_2707352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707352).length < 2 ^ (prefixWord ++ tailWord_2707352).sum := by decide
  have hdescent : baseEnd_2707352 < baseStart_2707352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707385 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2707385 : Nat := 118140960795 + 2707385 * 2 ^ 59
def prefixEnd_2707385 : Nat := 4983230072969 + 3 ^ 40 * 2707385 * 2
def baseEnd_2707385 : Nat := 1390189821772995077436469

theorem tailTrace_2707385 : CollatzResearch.WordTrace tailWord_2707385 prefixEnd_2707385 1390189821772995077436469 := by
  unfold tailWord_2707385
  simp only [CollatzResearch.WordTrace]
  refine ⟨98746443296614004390795609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65830962197742669593863739 98746443296614004390795609)
  ·
    refine ⟨74059832472460503293096707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98746443296614004390795609 74059832472460503293096707)
    ·
      refine ⟨111089748708690754939645061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74059832472460503293096707 111089748708690754939645061)
      ·
        refine ⟨20829327882879516551183449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111089748708690754939645061 20829327882879516551183449)
        ·
          refine ⟨15621995912159637413387587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20829327882879516551183449 15621995912159637413387587)
          ·
            refine ⟨23432993868239456120081381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15621995912159637413387587 23432993868239456120081381)
            ·
              refine ⟨4393686350294898022515259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23432993868239456120081381 4393686350294898022515259)
              ·
                refine ⟨6590529525442347033772889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393686350294898022515259 6590529525442347033772889)
                ·
                  refine ⟨4942897144081760275329667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6590529525442347033772889 4942897144081760275329667)
                  ·
                    refine ⟨7414345716122640412994501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4942897144081760275329667 7414345716122640412994501)
                    ·
                      refine ⟨1390189821772995077436469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7414345716122640412994501 1390189821772995077436469)
                      ·
                        rfl

theorem cell23_2707385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2707385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707385 prefixEnd_2707385 := by exact prefixLift 2707385
  have htrace : WordTrace (prefixWord ++ tailWord_2707385) baseStart_2707385 baseEnd_2707385 := by
    simpa [prefixWord, tailWord_2707385, baseEnd_2707385] using wordTrace_append hprefix tailTrace_2707385
  have hstable : (prefixWord ++ tailWord_2707385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707385).length < 2 ^ (prefixWord ++ tailWord_2707385).sum := by decide
  have hdescent : baseEnd_2707385 < baseStart_2707385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707408 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 6]
def baseStart_2707408 : Nat := 118140960795 + 2707408 * 2 ^ 59
def prefixEnd_2707408 : Nat := 4983230072969 + 3 ^ 40 * 2707408 * 2
def baseEnd_2707408 : Nat := 154466847980894276383207

theorem tailTrace_2707408 : CollatzResearch.WordTrace tailWord_2707408 prefixEnd_2707408 154466847980894276383207 := by
  unfold tailWord_2707408
  simp only [CollatzResearch.WordTrace]
  refine ⟨49373641087765339659441439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65831521450353786212588585 49373641087765339659441439)
  ·
    refine ⟨74060461631648009489162159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49373641087765339659441439 74060461631648009489162159)
    ·
      refine ⟨111090692447472014233743239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74060461631648009489162159 111090692447472014233743239)
      ·
        refine ⟨166636038671208021350614859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111090692447472014233743239 166636038671208021350614859)
        ·
          refine ⟨249954058006812032025922289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166636038671208021350614859 249954058006812032025922289)
          ·
            refine ⟨187465543505109024019441717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249954058006812032025922289 187465543505109024019441717)
            ·
              refine ⟨17574894703603971001822661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187465543505109024019441717 17574894703603971001822661)
              ·
                refine ⟨3295292756925744562841749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17574894703603971001822661 3295292756925744562841749)
                ·
                  refine ⟨154466847980894276383207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3295292756925744562841749 154466847980894276383207)
                  ·
                    rfl

theorem cell23_2707408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_2707408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707408 prefixEnd_2707408 := by exact prefixLift 2707408
  have htrace : WordTrace (prefixWord ++ tailWord_2707408) baseStart_2707408 baseEnd_2707408 := by
    simpa [prefixWord, tailWord_2707408, baseEnd_2707408] using wordTrace_append hprefix tailTrace_2707408
  have hstable : (prefixWord ++ tailWord_2707408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707408).length < 2 ^ (prefixWord ++ tailWord_2707408).sum := by decide
  have hdescent : baseEnd_2707408 < baseStart_2707408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707446 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_2707446 : Nat := 118140960795 + 2707446 * 2 ^ 59
def prefixEnd_2707446 : Nat := 4983230072969 + 3 ^ 40 * 2707446 * 2
def baseEnd_2707446 : Nat := 463407048030973112924563

theorem tailTrace_2707446 : CollatzResearch.WordTrace tailWord_2707446 prefixEnd_2707446 463407048030973112924563 := by
  unfold tailWord_2707446
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171791759337063238047887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65832445432928674539177461 6171791759337063238047887)
  ·
    refine ⟨9257687639005594857071831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6171791759337063238047887 9257687639005594857071831)
    ·
      refine ⟨13886531458508392285607747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9257687639005594857071831 13886531458508392285607747)
      ·
        refine ⟨20829797187762588428411621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13886531458508392285607747 20829797187762588428411621)
        ·
          refine ⟨3905586972705485330327179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20829797187762588428411621 3905586972705485330327179)
          ·
            refine ⟨5858380459058227995490769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905586972705485330327179 5858380459058227995490769)
            ·
              refine ⟨4393785344293670996618077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858380459058227995490769 4393785344293670996618077)
              ·
                refine ⟨1647669504110126623731779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4393785344293670996618077 1647669504110126623731779)
                ·
                  refine ⟨2471504256165189935597669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647669504110126623731779 2471504256165189935597669)
                  ·
                    refine ⟨463407048030973112924563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471504256165189935597669 463407048030973112924563)
                    ·
                      rfl

theorem cell23_2707446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_2707446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707446 prefixEnd_2707446 := by exact prefixLift 2707446
  have htrace : WordTrace (prefixWord ++ tailWord_2707446) baseStart_2707446 baseEnd_2707446 := by
    simpa [prefixWord, tailWord_2707446, baseEnd_2707446] using wordTrace_append hprefix tailTrace_2707446
  have hstable : (prefixWord ++ tailWord_2707446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707446).length < 2 ^ (prefixWord ++ tailWord_2707446).sum := by decide
  have hdescent : baseEnd_2707446 < baseStart_2707446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707476 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 6]
def baseStart_2707476 : Nat := 118140960795 + 2707476 * 2 ^ 59
def prefixEnd_2707476 : Nat := 4983230072969 + 3 ^ 40 * 2707476 * 2
def baseEnd_2707476 : Nat := 154470727612506024599839

theorem tailTrace_2707476 : CollatzResearch.WordTrace tailWord_2707476 prefixEnd_2707476 154470727612506024599839 := by
  unfold tailWord_2707476
  simp only [CollatzResearch.WordTrace]
  refine ⟨49374881169642163466179141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65833174892856217954905521 49374881169642163466179141)
  ·
    refine ⟨9257790219307905649908589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49374881169642163466179141 9257790219307905649908589)
    ·
      refine ⟨3471671332240464618715721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9257790219307905649908589 3471671332240464618715721)
      ·
        refine ⟨2603753499180348464036791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471671332240464618715721 2603753499180348464036791)
        ·
          refine ⟨3905630248770522696055187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603753499180348464036791 3905630248770522696055187)
          ·
            refine ⟨5858445373155784044082781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905630248770522696055187 5858445373155784044082781)
            ·
              refine ⟨2196917014933419016531043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5858445373155784044082781 2196917014933419016531043)
              ·
                refine ⟨3295375522400128524796565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196917014933419016531043 3295375522400128524796565)
                ·
                  refine ⟨154470727612506024599839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3295375522400128524796565 154470727612506024599839)
                  ·
                    rfl

theorem cell23_2707476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_2707476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707476 prefixEnd_2707476 := by exact prefixLift 2707476
  have htrace : WordTrace (prefixWord ++ tailWord_2707476) baseStart_2707476 baseEnd_2707476 := by
    simpa [prefixWord, tailWord_2707476, baseEnd_2707476] using wordTrace_append hprefix tailTrace_2707476
  have hstable : (prefixWord ++ tailWord_2707476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707476).length < 2 ^ (prefixWord ++ tailWord_2707476).sum := by decide
  have hdescent : baseEnd_2707476 < baseStart_2707476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707502 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_2707502 : Nat := 118140960795 + 2707502 * 2 ^ 59
def prefixEnd_2707502 : Nat := 4983230072969 + 3 ^ 40 * 2707502 * 2
def baseEnd_2707502 : Nat := 463416633003190373224477

theorem tailTrace_2707502 : CollatzResearch.WordTrace tailWord_2707502 prefixEnd_2707502 463416633003190373224477 := by
  unfold tailWord_2707502
  simp only [CollatzResearch.WordTrace]
  refine ⟨12343838829648766671600595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65833807091460088915203173 12343838829648766671600595)
  ·
    refine ⟨18515758244473150007400893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12343838829648766671600595 18515758244473150007400893)
    ·
      refine ⟨6943409341677431252775335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18515758244473150007400893 6943409341677431252775335)
      ·
        refine ⟨10415114012516146879163003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943409341677431252775335 10415114012516146879163003)
        ·
          refine ⟨15622671018774220318744505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10415114012516146879163003 15622671018774220318744505)
          ·
            refine ⟨11717003264080665239058379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15622671018774220318744505 11717003264080665239058379)
            ·
              refine ⟨17575504896120997858587569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11717003264080665239058379 17575504896120997858587569)
              ·
                refine ⟨13181628672090748393940677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17575504896120997858587569 13181628672090748393940677)
                ·
                  refine ⟨2471555376017015323863877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13181628672090748393940677 2471555376017015323863877)
                  ·
                    refine ⟨463416633003190373224477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2471555376017015323863877 463416633003190373224477)
                    ·
                      rfl

theorem cell23_2707502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_2707502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707502 prefixEnd_2707502 := by exact prefixLift 2707502
  have htrace : WordTrace (prefixWord ++ tailWord_2707502) baseStart_2707502 baseEnd_2707502 := by
    simpa [prefixWord, tailWord_2707502, baseEnd_2707502] using wordTrace_append hprefix tailTrace_2707502
  have hstable : (prefixWord ++ tailWord_2707502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707502).length < 2 ^ (prefixWord ++ tailWord_2707502).sum := by decide
  have hdescent : baseEnd_2707502 < baseStart_2707502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707512 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_2707512 : Nat := 118140960795 + 2707512 * 2 ^ 59
def prefixEnd_2707512 : Nat := 4983230072969 + 3 ^ 40 * 2707512 * 2
def baseEnd_2707512 : Nat := 1390255033816116080548385

theorem tailTrace_2707512 : CollatzResearch.WordTrace tailWord_2707512 prefixEnd_2707512 1390255033816116080548385 := by
  unfold tailWord_2707512
  simp only [CollatzResearch.WordTrace]
  refine ⟨49375537683576952540334395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65834050244769270053779193 49375537683576952540334395)
  ·
    refine ⟨74063306525365428810501593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49375537683576952540334395 74063306525365428810501593)
    ·
      refine ⟨55547479894024071607876195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74063306525365428810501593 55547479894024071607876195)
      ·
        refine ⟨83321219841036107411814293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55547479894024071607876195 83321219841036107411814293)
        ·
          refine ⟨3905682180048567534928795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83321219841036107411814293 3905682180048567534928795)
          ·
            refine ⟨5858523270072851302393193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905682180048567534928795 5858523270072851302393193)
            ·
              refine ⟨4393892452554638476794895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858523270072851302393193 4393892452554638476794895)
              ·
                refine ⟨6590838678831957715192343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4393892452554638476794895 6590838678831957715192343)
                ·
                  refine ⟨9886258018247936572788515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590838678831957715192343 9886258018247936572788515)
                  ·
                    refine ⟨14829387027371904859182773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9886258018247936572788515 14829387027371904859182773)
                    ·
                      refine ⟨1390255033816116080548385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14829387027371904859182773 1390255033816116080548385)
                      ·
                        rfl

theorem cell23_2707512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_2707512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707512 prefixEnd_2707512 := by exact prefixLift 2707512
  have htrace : WordTrace (prefixWord ++ tailWord_2707512) baseStart_2707512 baseEnd_2707512 := by
    simpa [prefixWord, tailWord_2707512, baseEnd_2707512] using wordTrace_append hprefix tailTrace_2707512
  have hstable : (prefixWord ++ tailWord_2707512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707512).length < 2 ^ (prefixWord ++ tailWord_2707512).sum := by decide
  have hdescent : baseEnd_2707512 < baseStart_2707512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707592 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2707592 : Nat := 118140960795 + 2707592 * 2 ^ 59
def prefixEnd_2707592 : Nat := 4983230072969 + 3 ^ 40 * 2707592 * 2
def baseEnd_2707592 : Nat := 463432037422825255849339

theorem tailTrace_2707592 : CollatzResearch.WordTrace tailWord_2707592 prefixEnd_2707592 463432037422825255849339 := by
  unfold tailWord_2707592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49376996603432039371790515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65835995471242719162387353 49376996603432039371790515)
  ·
    refine ⟨74065494905148059057685773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49376996603432039371790515 74065494905148059057685773)
    ·
      refine ⟨27774560589430522146632165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74065494905148059057685773 27774560589430522146632165)
      ·
        refine ⟨5207730110518222902493531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27774560589430522146632165 5207730110518222902493531)
        ·
          refine ⟨7811595165777334353740297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5207730110518222902493531 7811595165777334353740297)
          ·
            refine ⟨5858696374333000765305223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7811595165777334353740297 5858696374333000765305223)
            ·
              refine ⟨8788044561499501147957835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858696374333000765305223 8788044561499501147957835)
              ·
                refine ⟨13182066842249251721936753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8788044561499501147957835 13182066842249251721936753)
                ·
                  refine ⟨9886550131686938791452565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13182066842249251721936753 9886550131686938791452565)
                  ·
                    refine ⟨463432037422825255849339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9886550131686938791452565 463432037422825255849339)
                    ·
                      rfl

theorem cell23_2707592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2707592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707592 prefixEnd_2707592 := by exact prefixLift 2707592
  have htrace : WordTrace (prefixWord ++ tailWord_2707592) baseStart_2707592 baseEnd_2707592 := by
    simpa [prefixWord, tailWord_2707592, baseEnd_2707592] using wordTrace_append hprefix tailTrace_2707592
  have hstable : (prefixWord ++ tailWord_2707592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707592).length < 2 ^ (prefixWord ++ tailWord_2707592).sum := by decide
  have hdescent : baseEnd_2707592 < baseStart_2707592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707602 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_2707602 : Nat := 118140960795 + 2707602 * 2 ^ 59
def prefixEnd_2707602 : Nat := 4983230072969 + 3 ^ 40 * 2707602 * 2
def baseEnd_2707602 : Nat := 1390301247075020728422971

theorem tailTrace_2707602 : CollatzResearch.WordTrace tailWord_2707602 prefixEnd_2707602 1390301247075020728422971 := by
  unfold tailWord_2707602
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688589484206962612861265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65836238624551900300963373 24688589484206962612861265)
  ·
    refine ⟨18516442113155221959645949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24688589484206962612861265 18516442113155221959645949)
    ·
      refine ⟨6943665792433208234867231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18516442113155221959645949 6943665792433208234867231)
      ·
        refine ⟨10415498688649812352300847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943665792433208234867231 10415498688649812352300847)
        ·
          refine ⟨15623248032974718528451271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10415498688649812352300847 15623248032974718528451271)
          ·
            refine ⟨23434872049462077792676907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15623248032974718528451271 23434872049462077792676907)
            ·
              refine ⟨35152308074193116689015361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23434872049462077792676907 35152308074193116689015361)
              ·
                refine ⟨26364231055644837516761521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35152308074193116689015361 26364231055644837516761521)
                ·
                  refine ⟨19773173291733628137571141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26364231055644837516761521 19773173291733628137571141)
                  ·
                    refine ⟨3707469992200055275794589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19773173291733628137571141 3707469992200055275794589)
                    ·
                      refine ⟨1390301247075020728422971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3707469992200055275794589 1390301247075020728422971)
                      ·
                        rfl

theorem cell23_2707602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_2707602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707602 prefixEnd_2707602 := by exact prefixLift 2707602
  have htrace : WordTrace (prefixWord ++ tailWord_2707602) baseStart_2707602 baseEnd_2707602 := by
    simpa [prefixWord, tailWord_2707602, baseEnd_2707602] using wordTrace_append hprefix tailTrace_2707602
  have hstable : (prefixWord ++ tailWord_2707602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707602).length < 2 ^ (prefixWord ++ tailWord_2707602).sum := by decide
  have hdescent : baseEnd_2707602 < baseStart_2707602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707605 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 7]
def baseStart_2707605 : Nat := 118140960795 + 2707605 * 2 ^ 59
def prefixEnd_2707605 : Nat := 4983230072969 + 3 ^ 40 * 2707605 * 2
def baseEnd_2707605 : Nat := 154478087501887135187273

theorem tailTrace_2707605 : CollatzResearch.WordTrace tailWord_2707605 prefixEnd_2707605 154478087501887135187273 := by
  unfold tailWord_2707605
  simp only [CollatzResearch.WordTrace]
  refine ⟨98754467355816981963804269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65836311570544654642536179 98754467355816981963804269)
  ·
    refine ⟨37032925258431368236426601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98754467355816981963804269 37032925258431368236426601)
    ·
      refine ⟨27774693943823526177319951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37032925258431368236426601 27774693943823526177319951)
      ·
        refine ⟨41662040915735289265979927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27774693943823526177319951 41662040915735289265979927)
        ·
          refine ⟨62493061373602933898969891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41662040915735289265979927 62493061373602933898969891)
          ·
            refine ⟨93739592060404400848454837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62493061373602933898969891 93739592060404400848454837)
            ·
              refine ⟨8788086755662912579542641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93739592060404400848454837 8788086755662912579542641)
              ·
                refine ⟨6591065066747184434656981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8788086755662912579542641 6591065066747184434656981)
                ·
                  refine ⟨154478087501887135187273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6591065066747184434656981 154478087501887135187273)
                  ·
                    rfl

theorem cell23_2707605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_2707605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707605 prefixEnd_2707605 := by exact prefixLift 2707605
  have htrace : WordTrace (prefixWord ++ tailWord_2707605) baseStart_2707605 baseEnd_2707605 := by
    simpa [prefixWord, tailWord_2707605, baseEnd_2707605] using wordTrace_append hprefix tailTrace_2707605
  have hstable : (prefixWord ++ tailWord_2707605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707605).length < 2 ^ (prefixWord ++ tailWord_2707605).sum := by decide
  have hdescent : baseEnd_2707605 < baseStart_2707605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707620 : List Nat := [2, 3, 1, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_2707620 : Nat := 118140960795 + 2707620 * 2 ^ 59
def prefixEnd_2707620 : Nat := 4983230072969 + 3 ^ 40 * 2707620 * 2
def baseEnd_2707620 : Nat := 1390310489726801657997889

theorem tailTrace_2707620 : CollatzResearch.WordTrace tailWord_2707620 prefixEnd_2707620 1390310489726801657997889 := by
  unfold tailWord_2707620
  simp only [CollatzResearch.WordTrace]
  refine ⟨49377507225381319762800157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65836676300508426350400209 49377507225381319762800157)
  ·
    refine ⟨18516565209517994911050059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49377507225381319762800157 18516565209517994911050059)
    ·
      refine ⟨27774847814276992366575089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18516565209517994911050059 27774847814276992366575089)
      ·
        refine ⟨20831135860707744274931317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27774847814276992366575089 20831135860707744274931317)
        ·
          refine ⟨1952918986941351025774811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20831135860707744274931317 1952918986941351025774811)
          ·
            refine ⟨2929378480412026538662217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952918986941351025774811 2929378480412026538662217)
            ·
              refine ⟨2197033860309019903996663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929378480412026538662217 2197033860309019903996663)
              ·
                refine ⟨3295550790463529855994995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197033860309019903996663 3295550790463529855994995)
                ·
                  refine ⟨4943326185695294783992493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295550790463529855994995 4943326185695294783992493)
                  ·
                    refine ⟨1853747319635735543997185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4943326185695294783992493 1853747319635735543997185)
                    ·
                      refine ⟨1390310489726801657997889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853747319635735543997185 1390310489726801657997889)
                      ·
                        rfl

theorem cell23_2707620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_2707620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707620 prefixEnd_2707620 := by exact prefixLift 2707620
  have htrace : WordTrace (prefixWord ++ tailWord_2707620) baseStart_2707620 baseEnd_2707620 := by
    simpa [prefixWord, tailWord_2707620, baseEnd_2707620] using wordTrace_append hprefix tailTrace_2707620
  have hstable : (prefixWord ++ tailWord_2707620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707620).length < 2 ^ (prefixWord ++ tailWord_2707620).sum := by decide
  have hdescent : baseEnd_2707620 < baseStart_2707620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707635 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 4, 5]
def baseStart_2707635 : Nat := 118140960795 + 2707635 * 2 ^ 59
def prefixEnd_2707635 : Nat := 4983230072969 + 3 ^ 40 * 2707635 * 2
def baseEnd_2707635 : Nat := 463439397312206366436773

theorem tailTrace_2707635 : CollatzResearch.WordTrace tailWord_2707635 prefixEnd_2707635 463439397312206366436773 := by
  unfold tailWord_2707635
  simp only [CollatzResearch.WordTrace]
  refine ⟨98755561545708297087396359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65837041030472198058264239 98755561545708297087396359)
  ·
    refine ⟨148133342318562445631094539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98755561545708297087396359 148133342318562445631094539)
    ·
      refine ⟨222200013477843668446641809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148133342318562445631094539 222200013477843668446641809)
      ·
        refine ⟨166650010108382751334981357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222200013477843668446641809 166650010108382751334981357)
        ·
          refine ⟨62493753790643531750618009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166650010108382751334981357 62493753790643531750618009)
          ·
            refine ⟨46870315342982648812963507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62493753790643531750618009 46870315342982648812963507)
            ·
              refine ⟨70305473014473973219445261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46870315342982648812963507 70305473014473973219445261)
              ·
                refine ⟨26364552380427739957291973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70305473014473973219445261 26364552380427739957291973)
                ·
                  refine ⟨4943353571330201241992245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26364552380427739957291973 4943353571330201241992245)
                  ·
                    refine ⟨463439397312206366436773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4943353571330201241992245 463439397312206366436773)
                    ·
                      rfl

theorem cell23_2707635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 5].length) (baseStart_2707635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707635 prefixEnd_2707635 := by exact prefixLift 2707635
  have htrace : WordTrace (prefixWord ++ tailWord_2707635) baseStart_2707635 baseEnd_2707635 := by
    simpa [prefixWord, tailWord_2707635, baseEnd_2707635] using wordTrace_append hprefix tailTrace_2707635
  have hstable : (prefixWord ++ tailWord_2707635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707635).length < 2 ^ (prefixWord ++ tailWord_2707635).sum := by decide
  have hdescent : baseEnd_2707635 < baseStart_2707635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707642 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_2707642 : Nat := 118140960795 + 2707642 * 2 ^ 59
def prefixEnd_2707642 : Nat := 4983230072969 + 3 ^ 40 * 2707642 * 2
def baseEnd_2707642 : Nat := 1390321786301200571922787

theorem tailTrace_2707642 : CollatzResearch.WordTrace tailWord_2707642 prefixEnd_2707642 1390321786301200571922787 := by
  unfold tailWord_2707642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24688954214170734320725295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65837211237788624855267453 24688954214170734320725295)
  ·
    refine ⟨37033431321256101481087943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24688954214170734320725295 37033431321256101481087943)
    ·
      refine ⟨55550146981884152221631915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37033431321256101481087943 55550146981884152221631915)
      ·
        refine ⟨83325220472826228332447873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55550146981884152221631915 83325220472826228332447873)
        ·
          refine ⟨62493915354619671249335905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83325220472826228332447873 62493915354619671249335905)
          ·
            refine ⟨46870436515964753437001929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62493915354619671249335905 46870436515964753437001929)
            ·
              refine ⟨35152827386973565077751447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46870436515964753437001929 35152827386973565077751447)
              ·
                refine ⟨52729241080460347616627171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35152827386973565077751447 52729241080460347616627171)
                ·
                  refine ⟨79093861620690521424940757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52729241080460347616627171 79093861620690521424940757)
                  ·
                    refine ⟨1853762381734934095897049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 79093861620690521424940757 1853762381734934095897049)
                    ·
                      refine ⟨1390321786301200571922787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853762381734934095897049 1390321786301200571922787)
                      ·
                        rfl

theorem cell23_2707642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_2707642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707642 prefixEnd_2707642 := by exact prefixLift 2707642
  have htrace : WordTrace (prefixWord ++ tailWord_2707642) baseStart_2707642 baseEnd_2707642 := by
    simpa [prefixWord, tailWord_2707642, baseEnd_2707642] using wordTrace_append hprefix tailTrace_2707642
  have hstable : (prefixWord ++ tailWord_2707642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707642).length < 2 ^ (prefixWord ++ tailWord_2707642).sum := by decide
  have hdescent : baseEnd_2707642 < baseStart_2707642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707645 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2707645 : Nat := 118140960795 + 2707645 * 2 ^ 59
def prefixEnd_2707645 : Nat := 4983230072969 + 3 ^ 40 * 2707645 * 2
def baseEnd_2707645 : Nat := 1390323326743164060185273

theorem tailTrace_2707645 : CollatzResearch.WordTrace tailWord_2707645 prefixEnd_2707645 1390323326743164060185273 := by
  unfold tailWord_2707645
  simp only [CollatzResearch.WordTrace]
  refine ⟨98755926275672068795260389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65837284183781379196840259 98755926275672068795260389)
  ·
    refine ⟨18516736176688512899111323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98755926275672068795260389 18516736176688512899111323)
    ·
      refine ⟨27775104265032769348666985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18516736176688512899111323 27775104265032769348666985)
      ·
        refine ⟨20831328198774577011500239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27775104265032769348666985 20831328198774577011500239)
        ·
          refine ⟨31246992298161865517250359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20831328198774577011500239 31246992298161865517250359)
          ·
            refine ⟨46870488447242798275875539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31246992298161865517250359 46870488447242798275875539)
            ·
              refine ⟨70305732670864197413813309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46870488447242798275875539 70305732670864197413813309)
              ·
                refine ⟨26364649751574074030179991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70305732670864197413813309 26364649751574074030179991)
                ·
                  refine ⟨39546974627361111045269987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26364649751574074030179991 39546974627361111045269987)
                  ·
                    refine ⟨59320461941041666567904981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39546974627361111045269987 59320461941041666567904981)
                    ·
                      refine ⟨1390323326743164060185273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59320461941041666567904981 1390323326743164060185273)
                      ·
                        rfl

theorem cell23_2707645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2707645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707645 prefixEnd_2707645 := by exact prefixLift 2707645
  have htrace : WordTrace (prefixWord ++ tailWord_2707645) baseStart_2707645 baseEnd_2707645 := by
    simpa [prefixWord, tailWord_2707645, baseEnd_2707645] using wordTrace_append hprefix tailTrace_2707645
  have hstable : (prefixWord ++ tailWord_2707645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707645).length < 2 ^ (prefixWord ++ tailWord_2707645).sum := by decide
  have hdescent : baseEnd_2707645 < baseStart_2707645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707650 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_2707650 : Nat := 118140960795 + 2707650 * 2 ^ 59
def prefixEnd_2707650 : Nat := 4983230072969 + 3 ^ 40 * 2707650 * 2
def baseEnd_2707650 : Nat := 1390325894146436540622751

theorem tailTrace_2707650 : CollatzResearch.WordTrace tailWord_2707650 prefixEnd_2707650 1390325894146436540622751 := by
  unfold tailWord_2707650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689027160163488662298101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65837405760435969766128269 24689027160163488662298101)
  ·
    refine ⟨2314596296265327062090447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24689027160163488662298101 2314596296265327062090447)
    ·
      refine ⟨3471894444397990593135671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314596296265327062090447 3471894444397990593135671)
      ·
        refine ⟨5207841666596985889703507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471894444397990593135671 5207841666596985889703507)
        ·
          refine ⟨7811762499895478834555261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5207841666596985889703507 7811762499895478834555261)
          ·
            refine ⟨2929410937460804562958223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7811762499895478834555261 2929410937460804562958223)
            ·
              refine ⟨4394116406191206844437335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929410937460804562958223 4394116406191206844437335)
              ·
                refine ⟨6591174609286810266656003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394116406191206844437335 6591174609286810266656003)
                ·
                  refine ⟨9886761913930215399984005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6591174609286810266656003 9886761913930215399984005)
                  ·
                    refine ⟨1853767858861915387497001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9886761913930215399984005 1853767858861915387497001)
                    ·
                      refine ⟨1390325894146436540622751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853767858861915387497001 1390325894146436540622751)
                      ·
                        rfl

theorem cell23_2707650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_2707650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707650 prefixEnd_2707650 := by exact prefixLift 2707650
  have htrace : WordTrace (prefixWord ++ tailWord_2707650) baseStart_2707650 baseEnd_2707650 := by
    simpa [prefixWord, tailWord_2707650, baseEnd_2707650] using wordTrace_append hprefix tailTrace_2707650
  have hstable : (prefixWord ++ tailWord_2707650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707650).length < 2 ^ (prefixWord ++ tailWord_2707650).sum := by decide
  have hdescent : baseEnd_2707650 < baseStart_2707650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707652 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2707652 : Nat := 118140960795 + 2707652 * 2 ^ 59
def prefixEnd_2707652 : Nat := 4983230072969 + 3 ^ 40 * 2707652 * 2
def baseEnd_2707652 : Nat := 463442307035915177599247

theorem tailTrace_2707652 : CollatzResearch.WordTrace tailWord_2707652 prefixEnd_2707652 463442307035915177599247 := by
  unfold tailWord_2707652
  simp only [CollatzResearch.WordTrace]
  refine ⟨49378090793323354495382605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65837454391097805993843473 49378090793323354495382605)
  ·
    refine ⟨18516784047496257935768477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49378090793323354495382605 18516784047496257935768477)
    ·
      refine ⟨6943794017811096725913179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18516784047496257935768477 6943794017811096725913179)
      ·
        refine ⟨10415691026716645088869769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943794017811096725913179 10415691026716645088869769)
        ·
          refine ⟨7811768270037483816652327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10415691026716645088869769 7811768270037483816652327)
          ·
            refine ⟨11717652405056225724978491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811768270037483816652327 11717652405056225724978491)
            ·
              refine ⟨17576478607584338587467737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11717652405056225724978491 17576478607584338587467737)
              ·
                refine ⟨13182358955688253940600803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17576478607584338587467737 13182358955688253940600803)
                ·
                  refine ⟨19773538433532380910901205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13182358955688253940600803 19773538433532380910901205)
                  ·
                    refine ⟨463442307035915177599247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19773538433532380910901205 463442307035915177599247)
                    ·
                      rfl

theorem cell23_2707652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2707652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707652 prefixEnd_2707652 := by exact prefixLift 2707652
  have htrace : WordTrace (prefixWord ++ tailWord_2707652) baseStart_2707652 baseEnd_2707652 := by
    simpa [prefixWord, tailWord_2707652, baseEnd_2707652] using wordTrace_append hprefix tailTrace_2707652
  have hstable : (prefixWord ++ tailWord_2707652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707652).length < 2 ^ (prefixWord ++ tailWord_2707652).sum := by decide
  have hdescent : baseEnd_2707652 < baseStart_2707652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707672 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2707672 : Nat := 118140960795 + 2707672 * 2 ^ 59
def prefixEnd_2707672 : Nat := 4983230072969 + 3 ^ 40 * 2707672 * 2
def baseEnd_2707672 : Nat := 1390337190720835454547649

theorem tailTrace_2707672 : CollatzResearch.WordTrace tailWord_2707672 prefixEnd_2707672 1390337190720835454547649 := by
  unfold tailWord_2707672
  simp only [CollatzResearch.WordTrace]
  refine ⟨49378455523287126203246635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65837940697716168270995513 49378455523287126203246635)
  ·
    refine ⟨74067683284930689304869953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49378455523287126203246635 74067683284930689304869953)
    ·
      refine ⟨55550762463698016978652465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74067683284930689304869953 55550762463698016978652465)
      ·
        refine ⟨41663071847773512733989349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55550762463698016978652465 41663071847773512733989349)
        ·
          refine ⟨7811825971457533637623003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41663071847773512733989349 7811825971457533637623003)
          ·
            refine ⟨11717738957186300456434505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811825971457533637623003 11717738957186300456434505)
            ·
              refine ⟨8788304217889725342325879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11717738957186300456434505 8788304217889725342325879)
              ·
                refine ⟨13182456326834588013488819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8788304217889725342325879 13182456326834588013488819)
                ·
                  refine ⟨19773684490251882020233229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13182456326834588013488819 19773684490251882020233229)
                  ·
                    refine ⟨7415131683844455757587461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19773684490251882020233229 7415131683844455757587461)
                    ·
                      refine ⟨1390337190720835454547649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7415131683844455757587461 1390337190720835454547649)
                      ·
                        rfl

theorem cell23_2707672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2707672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707672 prefixEnd_2707672 := by exact prefixLift 2707672
  have htrace : WordTrace (prefixWord ++ tailWord_2707672) baseStart_2707672 baseEnd_2707672 := by
    simpa [prefixWord, tailWord_2707672, baseEnd_2707672] using wordTrace_append hprefix tailTrace_2707672
  have hstable : (prefixWord ++ tailWord_2707672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707672).length < 2 ^ (prefixWord ++ tailWord_2707672).sum := by decide
  have hdescent : baseEnd_2707672 < baseStart_2707672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707702 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2707702 : Nat := 118140960795 + 2707702 * 2 ^ 59
def prefixEnd_2707702 : Nat := 4983230072969 + 3 ^ 40 * 2707702 * 2
def baseEnd_2707702 : Nat := 1390352595140470337172511

theorem tailTrace_2707702 : CollatzResearch.WordTrace tailWord_2707702 prefixEnd_2707702 1390352595140470337172511 := by
  unfold tailWord_2707702
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172375327279097970630335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65838670157643711686723573 6172375327279097970630335)
  ·
    refine ⟨9258562990918646955945503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6172375327279097970630335 9258562990918646955945503)
    ·
      refine ⟨13887844486377970433918255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9258562990918646955945503 13887844486377970433918255)
      ·
        refine ⟨20831766729566955650877383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13887844486377970433918255 20831766729566955650877383)
        ·
          refine ⟨31247650094350433476316075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20831766729566955650877383 31247650094350433476316075)
          ·
            refine ⟨46871475141525650214474113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31247650094350433476316075 46871475141525650214474113)
            ·
              refine ⟨35153606356144237660855585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46871475141525650214474113 35153606356144237660855585)
              ·
                refine ⟨26365204767108178245641689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35153606356144237660855585 26365204767108178245641689)
                ·
                  refine ⟨19773903575331133684231267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26365204767108178245641689 19773903575331133684231267)
                  ·
                    refine ⟨29660855362996700526346901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19773903575331133684231267 29660855362996700526346901)
                    ·
                      refine ⟨1390352595140470337172511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29660855362996700526346901 1390352595140470337172511)
                      ·
                        rfl

theorem cell23_2707702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2707702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707702 prefixEnd_2707702 := by exact prefixLift 2707702
  have htrace : WordTrace (prefixWord ++ tailWord_2707702) baseStart_2707702 baseEnd_2707702 := by
    simpa [prefixWord, tailWord_2707702, baseEnd_2707702] using wordTrace_append hprefix tailTrace_2707702
  have hstable : (prefixWord ++ tailWord_2707702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707702).length < 2 ^ (prefixWord ++ tailWord_2707702).sum := by decide
  have hdescent : baseEnd_2707702 < baseStart_2707702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707722 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2707722 : Nat := 118140960795 + 2707722 * 2 ^ 59
def prefixEnd_2707722 : Nat := 4983230072969 + 3 ^ 40 * 2707722 * 2
def baseEnd_2707722 : Nat := 1390362864753560258922419

theorem tailTrace_2707722 : CollatzResearch.WordTrace tailWord_2707722 prefixEnd_2707722 1390362864753560258922419 := by
  unfold tailWord_2707722
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689683674098277736453355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65839156464262073963875613 24689683674098277736453355)
  ·
    refine ⟨37034525511147416604680033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24689683674098277736453355 37034525511147416604680033)
    ·
      refine ⟨27775894133360562453510025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37034525511147416604680033 27775894133360562453510025)
      ·
        refine ⟨20831920600020421840132519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27775894133360562453510025 20831920600020421840132519)
        ·
          refine ⟨31247880900030632760198779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20831920600020421840132519 31247880900030632760198779)
          ·
            refine ⟨46871821350045949140298169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31247880900030632760198779 46871821350045949140298169)
            ·
              refine ⟨35153866012534461855223627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46871821350045949140298169 35153866012534461855223627)
              ·
                refine ⟨52730799018801692782835441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35153866012534461855223627 52730799018801692782835441)
                ·
                  refine ⟨39548099264101269587126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52730799018801692782835441 39548099264101269587126581)
                  ·
                    refine ⟨3707634306009494023793117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39548099264101269587126581 3707634306009494023793117)
                    ·
                      refine ⟨1390362864753560258922419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3707634306009494023793117 1390362864753560258922419)
                      ·
                        rfl

theorem cell23_2707722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2707722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707722 prefixEnd_2707722 := by exact prefixLift 2707722
  have htrace : WordTrace (prefixWord ++ tailWord_2707722) baseStart_2707722 baseEnd_2707722 := by
    simpa [prefixWord, tailWord_2707722, baseEnd_2707722] using wordTrace_append hprefix tailTrace_2707722
  have hstable : (prefixWord ++ tailWord_2707722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707722).length < 2 ^ (prefixWord ++ tailWord_2707722).sum := by decide
  have hdescent : baseEnd_2707722 < baseStart_2707722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707755 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 1, 12]
def baseStart_2707755 : Nat := 118140960795 + 2707755 * 2 ^ 59
def prefixEnd_2707755 : Nat := 4983230072969 + 3 ^ 40 * 2707755 * 2
def baseEnd_2707755 : Nat := 463459936538386209936589

theorem tailTrace_2707755 : CollatzResearch.WordTrace tailWord_2707755 prefixEnd_2707755 463459936538386209936589 := by
  unfold tailWord_2707755
  simp only [CollatzResearch.WordTrace]
  refine ⟨98759938305273557581764719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65839958870182371721176479 98759938305273557581764719)
  ·
    refine ⟨148139907457910336372647079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98759938305273557581764719 148139907457910336372647079)
    ·
      refine ⟨222209861186865504558970619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148139907457910336372647079 222209861186865504558970619)
      ·
        refine ⟨333314791780298256838455929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222209861186865504558970619 333314791780298256838455929)
        ·
          refine ⟨249986093835223692628841947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333314791780298256838455929 249986093835223692628841947)
          ·
            refine ⟨374979140752835538943262921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249986093835223692628841947 374979140752835538943262921)
            ·
              refine ⟨281234355564626654207447191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374979140752835538943262921 281234355564626654207447191)
              ·
                refine ⟨421851533346939981311170787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281234355564626654207447191 421851533346939981311170787)
                ·
                  refine ⟨632777300020409971966756181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421851533346939981311170787 632777300020409971966756181)
                  ·
                    refine ⟨463459936538386209936589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 632777300020409971966756181 463459936538386209936589)
                    ·
                      rfl

theorem cell23_2707755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 12].length) (baseStart_2707755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707755 prefixEnd_2707755 := by exact prefixLift 2707755
  have htrace : WordTrace (prefixWord ++ tailWord_2707755) baseStart_2707755 baseEnd_2707755 := by
    simpa [prefixWord, tailWord_2707755, baseEnd_2707755] using wordTrace_append hprefix tailTrace_2707755
  have hstable : (prefixWord ++ tailWord_2707755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707755).length < 2 ^ (prefixWord ++ tailWord_2707755).sum := by decide
  have hdescent : baseEnd_2707755 < baseStart_2707755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707796 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_2707796 : Nat := 118140960795 + 2707796 * 2 ^ 59
def prefixEnd_2707796 : Nat := 4983230072969 + 3 ^ 40 * 2707796 * 2
def baseEnd_2707796 : Nat := 1390400862321992969397079

theorem tailTrace_2707796 : CollatzResearch.WordTrace tailWord_2707796 prefixEnd_2707796 1390400862321992969397079 := by
  unfold tailWord_2707796
  simp only [CollatzResearch.WordTrace]
  refine ⟨49380716849062510792003621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65840955798750014389338161 49380716849062510792003621)
  ·
    refine ⟨9258884409199220773500679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49380716849062510792003621 9258884409199220773500679)
    ·
      refine ⟨13888326613798831160251019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9258884409199220773500679 13888326613798831160251019)
      ·
        refine ⟨20832489920698246740376529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13888326613798831160251019 20832489920698246740376529)
        ·
          refine ⟨15624367440523685055282397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20832489920698246740376529 15624367440523685055282397)
          ·
            refine ⟨5859137790196381895730899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15624367440523685055282397 5859137790196381895730899)
            ·
              refine ⟨8788706685294572843596349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859137790196381895730899 8788706685294572843596349)
              ·
                refine ⟨3295765006985464816348631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8788706685294572843596349 3295765006985464816348631)
                ·
                  refine ⟨4943647510478197224522947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295765006985464816348631 4943647510478197224522947)
                  ·
                    refine ⟨7415471265717295836784421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4943647510478197224522947 7415471265717295836784421)
                    ·
                      refine ⟨1390400862321992969397079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7415471265717295836784421 1390400862321992969397079)
                      ·
                        rfl

theorem cell23_2707796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_2707796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707796 prefixEnd_2707796 := by exact prefixLift 2707796
  have htrace : WordTrace (prefixWord ++ tailWord_2707796) baseStart_2707796 baseEnd_2707796 := by
    simpa [prefixWord, tailWord_2707796, baseEnd_2707796] using wordTrace_append hprefix tailTrace_2707796
  have hstable : (prefixWord ++ tailWord_2707796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707796).length < 2 ^ (prefixWord ++ tailWord_2707796).sum := by decide
  have hdescent : baseEnd_2707796 < baseStart_2707796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707813 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_2707813 : Nat := 118140960795 + 2707813 * 2 ^ 59
def prefixEnd_2707813 : Nat := 4983230072969 + 3 ^ 40 * 2707813 * 2
def baseEnd_2707813 : Nat := 1390409591493119402884501

theorem tailTrace_2707813 : CollatzResearch.WordTrace tailWord_2707813 prefixEnd_2707813 1390409591493119402884501 := by
  unfold tailWord_2707813
  simp only [CollatzResearch.WordTrace]
  refine ⟨98762053739063433487376093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65841369159375622324917395 98762053739063433487376093)
  ·
    refine ⟨37035770152148787557766035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98762053739063433487376093 37035770152148787557766035)
    ·
      refine ⟨55553655228223181336649053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37035770152148787557766035 55553655228223181336649053)
      ·
        refine ⟨20832620710583693001243395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55553655228223181336649053 20832620710583693001243395)
        ·
          refine ⟨31248931065875539501865093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832620710583693001243395 31248931065875539501865093)
          ·
            refine ⟨5859174574851663656599705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31248931065875539501865093 5859174574851663656599705)
            ·
              refine ⟨4394380931138747742449779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859174574851663656599705 4394380931138747742449779)
              ·
                refine ⟨6591571396708121613674669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394380931138747742449779 6591571396708121613674669)
                ·
                  refine ⟨2471839273765545605128001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6591571396708121613674669 2471839273765545605128001)
                  ·
                    refine ⟨1853879455324159203846001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2471839273765545605128001 1853879455324159203846001)
                    ·
                      refine ⟨1390409591493119402884501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1853879455324159203846001 1390409591493119402884501)
                      ·
                        rfl

theorem cell23_2707813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_2707813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707813 prefixEnd_2707813 := by exact prefixLift 2707813
  have htrace : WordTrace (prefixWord ++ tailWord_2707813) baseStart_2707813 baseEnd_2707813 := by
    simpa [prefixWord, tailWord_2707813, baseEnd_2707813] using wordTrace_append hprefix tailTrace_2707813
  have hstable : (prefixWord ++ tailWord_2707813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707813).length < 2 ^ (prefixWord ++ tailWord_2707813).sum := by decide
  have hdescent : baseEnd_2707813 < baseStart_2707813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707826 : List Nat := [3, 2, 1, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2707826 : Nat := 118140960795 + 2707826 * 2 ^ 59
def prefixEnd_2707826 : Nat := 4983230072969 + 3 ^ 40 * 2707826 * 2
def baseEnd_2707826 : Nat := 1390416266741627852021941

theorem tailTrace_2707826 : CollatzResearch.WordTrace tailWord_2707826 prefixEnd_2707826 1390416266741627852021941 := by
  unfold tailWord_2707826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24690631972004084176899833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65841685258677557805066221 24690631972004084176899833)
  ·
    refine ⟨18517973979003063132674875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24690631972004084176899833 18517973979003063132674875)
    ·
      refine ⟨27776960968504594699012313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18517973979003063132674875 27776960968504594699012313)
      ·
        refine ⟨20832720726378446024259235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27776960968504594699012313 20832720726378446024259235)
        ·
          refine ⟨31249081089567669036388853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20832720726378446024259235 31249081089567669036388853)
          ·
            refine ⟨2929601352146968972161455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31249081089567669036388853 2929601352146968972161455)
            ·
              refine ⟨4394402028220453458242183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929601352146968972161455 4394402028220453458242183)
              ·
                refine ⟨6591603042330680187363275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394402028220453458242183 6591603042330680187363275)
                ·
                  refine ⟨9887404563496020281044913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6591603042330680187363275 9887404563496020281044913)
                  ·
                    refine ⟨7415553422622015210783685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9887404563496020281044913 7415553422622015210783685)
                    ·
                      refine ⟨1390416266741627852021941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7415553422622015210783685 1390416266741627852021941)
                      ·
                        rfl

theorem cell23_2707826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2707826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707826 prefixEnd_2707826 := by exact prefixLift 2707826
  have htrace : WordTrace (prefixWord ++ tailWord_2707826) baseStart_2707826 baseEnd_2707826 := by
    simpa [prefixWord, tailWord_2707826, baseEnd_2707826] using wordTrace_append hprefix tailTrace_2707826
  have hstable : (prefixWord ++ tailWord_2707826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707826).length < 2 ^ (prefixWord ++ tailWord_2707826).sum := by decide
  have hdescent : baseEnd_2707826 < baseStart_2707826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707830 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2707830 : Nat := 118140960795 + 2707830 * 2 ^ 59
def prefixEnd_2707830 : Nat := 4983230072969 + 3 ^ 40 * 2707830 * 2
def baseEnd_2707830 : Nat := 1390418320664245836371923

theorem tailTrace_2707830 : CollatzResearch.WordTrace tailWord_2707830 prefixEnd_2707830 1390418320664245836371923 := by
  unfold tailWord_2707830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172667111250115336921559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65841782520001230260496629 6172667111250115336921559)
  ·
    refine ⟨9259000666875173005382339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6172667111250115336921559 9259000666875173005382339)
    ·
      refine ⟨13888501000312759508073509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9259000666875173005382339 13888501000312759508073509)
      ·
        refine ⟨2604093937558642407763783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13888501000312759508073509 2604093937558642407763783)
        ·
          refine ⟨3906140906337963611645675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604093937558642407763783 3906140906337963611645675)
          ·
            refine ⟨5859211359506945417468513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906140906337963611645675 5859211359506945417468513)
            ·
              refine ⟨4394408519630209063101385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859211359506945417468513 4394408519630209063101385)
              ·
                refine ⟨3295806389722656797326039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394408519630209063101385 3295806389722656797326039)
                ·
                  refine ⟨4943709584583985195989059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295806389722656797326039 4943709584583985195989059)
                  ·
                    refine ⟨7415564376875977793983589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4943709584583985195989059 7415564376875977793983589)
                    ·
                      refine ⟨1390418320664245836371923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7415564376875977793983589 1390418320664245836371923)
                      ·
                        rfl

theorem cell23_2707830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2707830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707830 prefixEnd_2707830 := by exact prefixLift 2707830
  have htrace : WordTrace (prefixWord ++ tailWord_2707830) baseStart_2707830 baseEnd_2707830 := by
    simpa [prefixWord, tailWord_2707830, baseEnd_2707830] using wordTrace_append hprefix tailTrace_2707830
  have hstable : (prefixWord ++ tailWord_2707830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707830).length < 2 ^ (prefixWord ++ tailWord_2707830).sum := by decide
  have hdescent : baseEnd_2707830 < baseStart_2707830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707880 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_2707880 : Nat := 118140960795 + 2707880 * 2 ^ 59
def prefixEnd_2707880 : Nat := 4983230072969 + 3 ^ 40 * 2707880 * 2
def baseEnd_2707880 : Nat := 1390443994696970640746693

theorem tailTrace_2707880 : CollatzResearch.WordTrace tailWord_2707880 prefixEnd_2707880 1390443994696970640746693 := by
  unfold tailWord_2707880
  simp only [CollatzResearch.WordTrace]
  refine ⟨49382248714910351965032547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65842998286547135953376729 49382248714910351965032547)
  ·
    refine ⟨74073373072365527947548821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49382248714910351965032547 74073373072365527947548821)
    ·
      refine ⟨3472189362767134122541351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74073373072365527947548821 3472189362767134122541351)
      ·
        refine ⟨5208284044150701183812027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472189362767134122541351 5208284044150701183812027)
        ·
          refine ⟨7812426066226051775718041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208284044150701183812027 7812426066226051775718041)
          ·
            refine ⟨5859319549669538831788531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7812426066226051775718041 5859319549669538831788531)
            ·
              refine ⟨8788979324504308247682797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859319549669538831788531 8788979324504308247682797)
              ·
                refine ⟨3295867246689115592881049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8788979324504308247682797 3295867246689115592881049)
                ·
                  refine ⟨2471900435016836694660787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3295867246689115592881049 2471900435016836694660787)
                  ·
                    refine ⟨3707850652525255041991181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2471900435016836694660787 3707850652525255041991181)
                    ·
                      refine ⟨1390443994696970640746693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3707850652525255041991181 1390443994696970640746693)
                      ·
                        rfl

theorem cell23_2707880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_2707880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707880 prefixEnd_2707880 := by exact prefixLift 2707880
  have htrace : WordTrace (prefixWord ++ tailWord_2707880) baseStart_2707880 baseEnd_2707880 := by
    simpa [prefixWord, tailWord_2707880, baseEnd_2707880] using wordTrace_append hprefix tailTrace_2707880
  have hstable : (prefixWord ++ tailWord_2707880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707880).length < 2 ^ (prefixWord ++ tailWord_2707880).sum := by decide
  have hdescent : baseEnd_2707880 < baseStart_2707880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707889 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2707889 : Nat := 118140960795 + 2707889 * 2 ^ 59
def prefixEnd_2707889 : Nat := 4983230072969 + 3 ^ 40 * 2707889 * 2
def baseEnd_2707889 : Nat := 1390448616022861105534151

theorem tailTrace_2707889 : CollatzResearch.WordTrace tailWord_2707889 prefixEnd_2707889 1390448616022861105534151 := by
  unfold tailWord_2707889
  simp only [CollatzResearch.WordTrace]
  refine ⟨98764825686788098467142721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65843217124525398978095147 98764825686788098467142721)
  ·
    refine ⟨74073619265091073850357041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98764825686788098467142721 74073619265091073850357041)
    ·
      refine ⟨55555214448818305387767781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74073619265091073850357041 55555214448818305387767781)
      ·
        refine ⟨10416602709153432260206459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55555214448818305387767781 10416602709153432260206459)
        ·
          refine ⟨15624904063730148390309689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416602709153432260206459 15624904063730148390309689)
          ·
            refine ⟨11718678047797611292732267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15624904063730148390309689 11718678047797611292732267)
            ·
              refine ⟨17578017071696416939098401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11718678047797611292732267 17578017071696416939098401)
              ·
                refine ⟨13183512803772312704323801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17578017071696416939098401 13183512803772312704323801)
                ·
                  refine ⟨9887634602829234528242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13183512803772312704323801 9887634602829234528242851)
                  ·
                    refine ⟨14831451904243851792364277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9887634602829234528242851 14831451904243851792364277)
                    ·
                      refine ⟨1390448616022861105534151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14831451904243851792364277 1390448616022861105534151)
                      ·
                        rfl

theorem cell23_2707889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2707889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707889 prefixEnd_2707889 := by exact prefixLift 2707889
  have htrace : WordTrace (prefixWord ++ tailWord_2707889) baseStart_2707889 baseEnd_2707889 := by
    simpa [prefixWord, tailWord_2707889, baseEnd_2707889] using wordTrace_append hprefix tailTrace_2707889
  have hstable : (prefixWord ++ tailWord_2707889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707889).length < 2 ^ (prefixWord ++ tailWord_2707889).sum := by decide
  have hdescent : baseEnd_2707889 < baseStart_2707889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707919 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3]
def baseStart_2707919 : Nat := 118140960795 + 2707919 * 2 ^ 59
def prefixEnd_2707919 : Nat := 4983230072969 + 3 ^ 40 * 2707919 * 2
def baseEnd_2707919 : Nat := 1390464020442495988159013

theorem tailTrace_2707919 : CollatzResearch.WordTrace tailWord_2707919 prefixEnd_2707919 1390464020442495988159013 := by
  unfold tailWord_2707919
  simp only [CollatzResearch.WordTrace]
  refine ⟨98765919876679413590734811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65843946584452942393823207 98765919876679413590734811)
  ·
    refine ⟨148148879815019120386102217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98765919876679413590734811 148148879815019120386102217)
    ·
      refine ⟨111111659861264340289576663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148148879815019120386102217 111111659861264340289576663)
      ·
        refine ⟨166667489791896510434364995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111111659861264340289576663 166667489791896510434364995)
        ·
          refine ⟨250001234687844765651547493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166667489791896510434364995 250001234687844765651547493)
          ·
            refine ⟨46875231503970893559665155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250001234687844765651547493 46875231503970893559665155)
            ·
              refine ⟨70312847255956340339497733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46875231503970893559665155 70312847255956340339497733)
              ·
                refine ⟨13183658860491813813655825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70312847255956340339497733 13183658860491813813655825)
                ·
                  refine ⟨9887744145368860360241869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13183658860491813813655825 9887744145368860360241869)
                  ·
                    refine ⟨3707904054513322635090701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9887744145368860360241869 3707904054513322635090701)
                    ·
                      refine ⟨1390464020442495988159013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3707904054513322635090701 1390464020442495988159013)
                      ·
                        rfl

theorem cell23_2707919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 3, 3].length) (baseStart_2707919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707919 prefixEnd_2707919 := by exact prefixLift 2707919
  have htrace : WordTrace (prefixWord ++ tailWord_2707919) baseStart_2707919 baseEnd_2707919 := by
    simpa [prefixWord, tailWord_2707919, baseEnd_2707919] using wordTrace_append hprefix tailTrace_2707919
  have hstable : (prefixWord ++ tailWord_2707919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707919).length < 2 ^ (prefixWord ++ tailWord_2707919).sum := by decide
  have hdescent : baseEnd_2707919 < baseStart_2707919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707926 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_2707926 : Nat := 118140960795 + 2707926 * 2 ^ 59
def prefixEnd_2707926 : Nat := 4983230072969 + 3 ^ 40 * 2707926 * 2
def baseEnd_2707926 : Nat := 154496401645230828974609

theorem tailTrace_2707926 : CollatzResearch.WordTrace tailWord_2707926 prefixEnd_2707926 154496401645230828974609 := by
  unfold tailWord_2707926
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172885949228378361639977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65844116791769369190826421 6172885949228378361639977)
  ·
    refine ⟨4629664461921283771229983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6172885949228378361639977 4629664461921283771229983)
    ·
      refine ⟨6944496692881925656844975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4629664461921283771229983 6944496692881925656844975)
      ·
        refine ⟨10416745039322888485267463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944496692881925656844975 10416745039322888485267463)
        ·
          refine ⟨15625117558984332727901195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416745039322888485267463 15625117558984332727901195)
          ·
            refine ⟨23437676338476499091851793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625117558984332727901195 23437676338476499091851793)
            ·
              refine ⟨17578257253857374318888845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23437676338476499091851793 17578257253857374318888845)
              ·
                refine ⟨6591846470196515369583317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17578257253857374318888845 6591846470196515369583317)
                ·
                  refine ⟨154496401645230828974609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6591846470196515369583317 154496401645230828974609)
                  ·
                    rfl

theorem cell23_2707926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_2707926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707926 prefixEnd_2707926 := by exact prefixLift 2707926
  have htrace : WordTrace (prefixWord ++ tailWord_2707926) baseStart_2707926 baseEnd_2707926 := by
    simpa [prefixWord, tailWord_2707926, baseEnd_2707926] using wordTrace_append hprefix tailTrace_2707926
  have hstable : (prefixWord ++ tailWord_2707926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707926).length < 2 ^ (prefixWord ++ tailWord_2707926).sum := by decide
  have hdescent : baseEnd_2707926 < baseStart_2707926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707989 : List Nat := [1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2707989 : Nat := 118140960795 + 2707989 * 2 ^ 59
def prefixEnd_2707989 : Nat := 4983230072969 + 3 ^ 40 * 2707989 * 2
def baseEnd_2707989 : Nat := 1390499964088310714283691

theorem tailTrace_2707989 : CollatzResearch.WordTrace tailWord_2707989 prefixEnd_2707989 1390499964088310714283691 := by
  unfold tailWord_2707989
  simp only [CollatzResearch.WordTrace]
  refine ⟨98768472986425815545783021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65845648657617210363855347 98768472986425815545783021)
  ·
    refine ⟨37038177369909680829668633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98768472986425815545783021 37038177369909680829668633)
    ·
      refine ⟨27778633027432260622251475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37038177369909680829668633 27778633027432260622251475)
      ·
        refine ⟨41667949541148390933377213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27778633027432260622251475 41667949541148390933377213)
        ·
          refine ⟨15625481077930646600016455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41667949541148390933377213 15625481077930646600016455)
          ·
            refine ⟨23438221616895969900024683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625481077930646600016455 23438221616895969900024683)
            ·
              refine ⟨35157332425343954850037025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23438221616895969900024683 35157332425343954850037025)
              ·
                refine ⟨26367999319007966137527769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35157332425343954850037025 26367999319007966137527769)
                ·
                  refine ⟨19775999489255974603145827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26367999319007966137527769 19775999489255974603145827)
                  ·
                    refine ⟨29663999233883961904718741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19775999489255974603145827 29663999233883961904718741)
                    ·
                      refine ⟨1390499964088310714283691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29663999233883961904718741 1390499964088310714283691)
                      ·
                        rfl

theorem cell23_2707989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2707989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707989 prefixEnd_2707989 := by exact prefixLift 2707989
  have htrace : WordTrace (prefixWord ++ tailWord_2707989) baseStart_2707989 baseEnd_2707989 := by
    simpa [prefixWord, tailWord_2707989, baseEnd_2707989] using wordTrace_append hprefix tailTrace_2707989
  have hstable : (prefixWord ++ tailWord_2707989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707989).length < 2 ^ (prefixWord ++ tailWord_2707989).sum := by decide
  have hdescent : baseEnd_2707989 < baseStart_2707989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2707996 : List Nat := [2, 2, 3, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_2707996 : Nat := 118140960795 + 2707996 * 2 ^ 59
def prefixEnd_2707996 : Nat := 4983230072969 + 3 ^ 40 * 2707996 * 2
def baseEnd_2707996 : Nat := 1390503558452892186896159

theorem tailTrace_2707996 : CollatzResearch.WordTrace tailWord_2707996 prefixEnd_2707996 1390503558452892186896159 := by
  unfold tailWord_2707996
  simp only [CollatzResearch.WordTrace]
  refine ⟨49384364148700227870643921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65845818864933637160858561 49384364148700227870643921)
  ·
    refine ⟨37038273111525170902982941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49384364148700227870643921 37038273111525170902982941)
    ·
      refine ⟨13889352416821939088618603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37038273111525170902982941 13889352416821939088618603)
      ·
        refine ⟨20834028625232908632927905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13889352416821939088618603 20834028625232908632927905)
        ·
          refine ⟨15625521468924681474695929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20834028625232908632927905 15625521468924681474695929)
          ·
            refine ⟨11719141101693511106021947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15625521468924681474695929 11719141101693511106021947)
            ·
              refine ⟨17578711652540266659032921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719141101693511106021947 17578711652540266659032921)
              ·
                refine ⟨13184033739405199994274691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17578711652540266659032921 13184033739405199994274691)
                ·
                  refine ⟨19776050609107799991412037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13184033739405199994274691 19776050609107799991412037)
                  ·
                    refine ⟨3708009489207712498389757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19776050609107799991412037 3708009489207712498389757)
                    ·
                      refine ⟨1390503558452892186896159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708009489207712498389757 1390503558452892186896159)
                      ·
                        rfl

theorem cell23_2707996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_2707996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2707996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2707996 prefixEnd_2707996 := by exact prefixLift 2707996
  have htrace : WordTrace (prefixWord ++ tailWord_2707996) baseStart_2707996 baseEnd_2707996 := by
    simpa [prefixWord, tailWord_2707996, baseEnd_2707996] using wordTrace_append hprefix tailTrace_2707996
  have hstable : (prefixWord ++ tailWord_2707996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2707996).length < 2 ^ (prefixWord ++ tailWord_2707996).sum := by decide
  have hdescent : baseEnd_2707996 < baseStart_2707996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2707996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708043 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 3]
def baseStart_2708043 : Nat := 118140960795 + 2708043 * 2 ^ 59
def prefixEnd_2708043 : Nat := 4983230072969 + 3 ^ 40 * 2708043 * 2
def baseEnd_2708043 : Nat := 1390527692043653503008443

theorem tailTrace_2708043 : CollatzResearch.WordTrace tailWord_2708043 prefixEnd_2708043 1390527692043653503008443 := by
  unfold tailWord_2708043
  simp only [CollatzResearch.WordTrace]
  refine ⟨98770442528230182768248783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65846961685486788512165855 98770442528230182768248783)
  ·
    refine ⟨148155663792345274152373175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98770442528230182768248783 148155663792345274152373175)
    ·
      refine ⟨222233495688517911228559763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148155663792345274152373175 222233495688517911228559763)
      ·
        refine ⟨333350243532776866842839645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222233495688517911228559763 333350243532776866842839645)
        ·
          refine ⟨125006341324791325066064867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333350243532776866842839645 125006341324791325066064867)
          ·
            refine ⟨187509511987186987599097301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125006341324791325066064867 187509511987186987599097301)
            ·
              refine ⟨4394754187199695021853843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 187509511987186987599097301 4394754187199695021853843)
              ·
                refine ⟨6592131280799542532780765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394754187199695021853843 6592131280799542532780765)
                ·
                  refine ⟨2472049230299828449792787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6592131280799542532780765 2472049230299828449792787)
                  ·
                    refine ⟨3708073845449742674689181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472049230299828449792787 3708073845449742674689181)
                    ·
                      refine ⟨1390527692043653503008443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708073845449742674689181 1390527692043653503008443)
                      ·
                        rfl

theorem cell23_2708043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 1, 3].length) (baseStart_2708043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708043 prefixEnd_2708043 := by exact prefixLift 2708043
  have htrace : WordTrace (prefixWord ++ tailWord_2708043) baseStart_2708043 baseEnd_2708043 := by
    simpa [prefixWord, tailWord_2708043, baseEnd_2708043] using wordTrace_append hprefix tailTrace_2708043
  have hstable : (prefixWord ++ tailWord_2708043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708043).length < 2 ^ (prefixWord ++ tailWord_2708043).sum := by decide
  have hdescent : baseEnd_2708043 < baseStart_2708043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708076 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_2708076 : Nat := 118140960795 + 2708076 * 2 ^ 59
def prefixEnd_2708076 : Nat := 4983230072969 + 3 ^ 40 * 2708076 * 2
def baseEnd_2708076 : Nat := 463514878968417291298597

theorem tailTrace_2708076 : CollatzResearch.WordTrace tailWord_2708076 prefixEnd_2708076 463514878968417291298597 := by
  unfold tailWord_2708076
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385823068555314702100041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65847764091407086269466721 49385823068555314702100041)
  ·
    refine ⟨37039367301416486026575031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49385823068555314702100041 37039367301416486026575031)
    ·
      refine ⟨55559050952124729039862547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37039367301416486026575031 55559050952124729039862547)
      ·
        refine ⟨83338576428187093559793821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55559050952124729039862547 83338576428187093559793821)
        ·
          refine ⟨31251966160570160084922683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83338576428187093559793821 31251966160570160084922683)
          ·
            refine ⟨46877949240855240127384025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31251966160570160084922683 46877949240855240127384025)
            ·
              refine ⟨35158461930641430095538019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46877949240855240127384025 35158461930641430095538019)
              ·
                refine ⟨52737692895962145143307029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35158461930641430095538019 52737692895962145143307029)
                ·
                  refine ⟨2472079354498225553592517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52737692895962145143307029 2472079354498225553592517)
                  ·
                    refine ⟨463514878968417291298597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2472079354498225553592517 463514878968417291298597)
                    ·
                      rfl

theorem cell23_2708076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_2708076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708076 prefixEnd_2708076 := by exact prefixLift 2708076
  have htrace : WordTrace (prefixWord ++ tailWord_2708076) baseStart_2708076 baseEnd_2708076 := by
    simpa [prefixWord, tailWord_2708076, baseEnd_2708076] using wordTrace_append hprefix tailTrace_2708076
  have hstable : (prefixWord ++ tailWord_2708076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708076).length < 2 ^ (prefixWord ++ tailWord_2708076).sum := by decide
  have hdescent : baseEnd_2708076 < baseStart_2708076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708080 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 1, 5]
def baseStart_2708080 : Nat := 118140960795 + 2708080 * 2 ^ 59
def prefixEnd_2708080 : Nat := 4983230072969 + 3 ^ 40 * 2708080 * 2
def baseEnd_2708080 : Nat := 463515563609289952748591

theorem tailTrace_2708080 : CollatzResearch.WordTrace tailWord_2708080 prefixEnd_2708080 463515563609289952748591 := by
  unfold tailWord_2708080
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385896014548069043672847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65847861352730758724897129 49385896014548069043672847)
  ·
    refine ⟨74078844021822103565509271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49385896014548069043672847 74078844021822103565509271)
    ·
      refine ⟨111118266032733155348263907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74078844021822103565509271 111118266032733155348263907)
      ·
        refine ⟨166677399049099733022395861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111118266032733155348263907 166677399049099733022395861)
        ·
          refine ⟨3906501540213274992712403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166677399049099733022395861 3906501540213274992712403)
          ·
            refine ⟨5859752310319912489068605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906501540213274992712403 5859752310319912489068605)
            ·
              refine ⟨2197407116369967183400727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5859752310319912489068605 2197407116369967183400727)
              ·
                refine ⟨3296110674554950775101091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197407116369967183400727 3296110674554950775101091)
                ·
                  refine ⟨4944166011832426162651637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296110674554950775101091 4944166011832426162651637)
                  ·
                    refine ⟨463515563609289952748591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4944166011832426162651637 463515563609289952748591)
                    ·
                      rfl

theorem cell23_2708080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_2708080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708080 prefixEnd_2708080 := by exact prefixLift 2708080
  have htrace : WordTrace (prefixWord ++ tailWord_2708080) baseStart_2708080 baseEnd_2708080 := by
    simpa [prefixWord, tailWord_2708080, baseEnd_2708080] using wordTrace_append hprefix tailTrace_2708080
  have hstable : (prefixWord ++ tailWord_2708080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708080).length < 2 ^ (prefixWord ++ tailWord_2708080).sum := by decide
  have hdescent : baseEnd_2708080 < baseStart_2708080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708083 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 7, 2, 2]
def baseStart_2708083 : Nat := 118140960795 + 2708083 * 2 ^ 59
def prefixEnd_2708083 : Nat := 4983230072969 + 3 ^ 40 * 2708083 * 2
def baseEnd_2708083 : Nat := 1390548231269833346508259

theorem tailTrace_2708083 : CollatzResearch.WordTrace tailWord_2708083 prefixEnd_2708083 1390548231269833346508259 := by
  unfold tailWord_2708083
  simp only [CollatzResearch.WordTrace]
  refine ⟨98771901448085269599704903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65847934298723513066469935 98771901448085269599704903)
  ·
    refine ⟨148157852172127904399557355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98771901448085269599704903 148157852172127904399557355)
    ·
      refine ⟨222236778258191856599336033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148157852172127904399557355 222236778258191856599336033)
      ·
        refine ⟨166677583693643892449502025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222236778258191856599336033 166677583693643892449502025)
        ·
          refine ⟨125008187770232919337126519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166677583693643892449502025 125008187770232919337126519)
          ·
            refine ⟨187512281655349379005689779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125008187770232919337126519 187512281655349379005689779)
            ·
              refine ⟨281268422483024068508534669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187512281655349379005689779 281268422483024068508534669)
              ·
                refine ⟨105475658431134025690700501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281268422483024068508534669 105475658431134025690700501)
                ·
                  refine ⟨2472085744479703727125793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 105475658431134025690700501 2472085744479703727125793)
                  ·
                    refine ⟨1854064308359777795344345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2472085744479703727125793 1854064308359777795344345)
                    ·
                      refine ⟨1390548231269833346508259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854064308359777795344345 1390548231269833346508259)
                      ·
                        rfl

theorem cell23_2708083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 2, 2].length) (baseStart_2708083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708083 prefixEnd_2708083 := by exact prefixLift 2708083
  have htrace : WordTrace (prefixWord ++ tailWord_2708083) baseStart_2708083 baseEnd_2708083 := by
    simpa [prefixWord, tailWord_2708083, baseEnd_2708083] using wordTrace_append hprefix tailTrace_2708083
  have hstable : (prefixWord ++ tailWord_2708083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708083).length < 2 ^ (prefixWord ++ tailWord_2708083).sum := by decide
  have hdescent : baseEnd_2708083 < baseStart_2708083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708089 : List Nat := [1, 2, 1, 3, 3, 13]
def baseStart_2708089 : Nat := 118140960795 + 2708089 * 2 ^ 59
def prefixEnd_2708089 : Nat := 4983230072969 + 3 ^ 40 * 2708089 * 2
def baseEnd_2708089 : Nat := 5722433383348807913717

theorem tailTrace_2708089 : CollatzResearch.WordTrace tailWord_2708089 prefixEnd_2708089 5722433383348807913717 := by
  unfold tailWord_2708089
  simp only [CollatzResearch.WordTrace]
  refine ⟨98772120286063532624423321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65848080190709021749615547 98772120286063532624423321)
  ·
    refine ⟨74079090214547649468317491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98772120286063532624423321 74079090214547649468317491)
    ·
      refine ⟨111118635321821474202476237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74079090214547649468317491 111118635321821474202476237)
      ·
        refine ⟨41669488245683052825928589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111118635321821474202476237 41669488245683052825928589)
        ·
          refine ⟨15626058092131144809723221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41669488245683052825928589 15626058092131144809723221)
          ·
            refine ⟨5722433383348807913717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 15626058092131144809723221 5722433383348807913717)
            ·
              rfl

theorem cell23_2708089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 13].length) (baseStart_2708089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708089 prefixEnd_2708089 := by exact prefixLift 2708089
  have htrace : WordTrace (prefixWord ++ tailWord_2708089) baseStart_2708089 baseEnd_2708089 := by
    simpa [prefixWord, tailWord_2708089, baseEnd_2708089] using wordTrace_append hprefix tailTrace_2708089
  have hstable : (prefixWord ++ tailWord_2708089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708089).length < 2 ^ (prefixWord ++ tailWord_2708089).sum := by decide
  have hdescent : baseEnd_2708089 < baseStart_2708089 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708133 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_2708133 : Nat := 118140960795 + 2708133 * 2 ^ 59
def prefixEnd_2708133 : Nat := 4983230072969 + 3 ^ 40 * 2708133 * 2
def baseEnd_2708133 : Nat := 1390573905302558150883029

theorem tailTrace_2708133 : CollatzResearch.WordTrace tailWord_2708133 prefixEnd_2708133 1390573905302558150883029 := by
  unfold tailWord_2708133
  simp only [CollatzResearch.WordTrace]
  refine ⟨98773725097904128139025053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65849150065269418759350035 98773725097904128139025053)
  ·
    refine ⟨37040146911714048052134395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98773725097904128139025053 37040146911714048052134395)
    ·
      refine ⟨55560220367571072078201593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37040146911714048052134395 55560220367571072078201593)
      ·
        refine ⟨41670165275678304058651195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55560220367571072078201593 41670165275678304058651195)
        ·
          refine ⟨62505247913517456087976793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41670165275678304058651195 62505247913517456087976793)
          ·
            refine ⟨46878935935138092065982595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62505247913517456087976793 46878935935138092065982595)
            ·
              refine ⟨70318403902707138098973893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46878935935138092065982595 70318403902707138098973893)
              ·
                refine ⟨13184700731757588393557605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70318403902707138098973893 13184700731757588393557605)
                ·
                  refine ⟨2472131387204547823792051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13184700731757588393557605 2472131387204547823792051)
                  ·
                    refine ⟨3708197080806821735688077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472131387204547823792051 3708197080806821735688077)
                    ·
                      refine ⟨1390573905302558150883029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708197080806821735688077 1390573905302558150883029)
                      ·
                        rfl

theorem cell23_2708133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_2708133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708133 prefixEnd_2708133 := by exact prefixLift 2708133
  have htrace : WordTrace (prefixWord ++ tailWord_2708133) baseStart_2708133 baseEnd_2708133 := by
    simpa [prefixWord, tailWord_2708133, baseEnd_2708133] using wordTrace_append hprefix tailTrace_2708133
  have hstable : (prefixWord ++ tailWord_2708133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708133).length < 2 ^ (prefixWord ++ tailWord_2708133).sum := by decide
  have hdescent : baseEnd_2708133 < baseStart_2708133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708176 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_2708176 : Nat := 118140960795 + 2708176 * 2 ^ 59
def prefixEnd_2708176 : Nat := 4983230072969 + 3 ^ 40 * 2708176 * 2
def baseEnd_2708176 : Nat := 1390595984970701482645331

theorem tailTrace_2708176 : CollatzResearch.WordTrace tailWord_2708176 prefixEnd_2708176 1390595984970701482645331 := by
  unfold tailWord_2708176
  simp only [CollatzResearch.WordTrace]
  refine ⟨49387646718374173241420191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65850195624498897655226921 49387646718374173241420191)
  ·
    refine ⟨74081470077561259862130287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49387646718374173241420191 74081470077561259862130287)
    ·
      refine ⟨111122205116341889793195431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74081470077561259862130287 111122205116341889793195431)
      ·
        refine ⟨166683307674512834689793147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111122205116341889793195431 166683307674512834689793147)
        ·
          refine ⟨250024961511769252034689721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166683307674512834689793147 250024961511769252034689721)
          ·
            refine ⟨187518721133826939026017291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250024961511769252034689721 187518721133826939026017291)
            ·
              refine ⟨281278081700740408539025937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187518721133826939026017291 281278081700740408539025937)
              ·
                refine ⟨210958561275555306404269453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281278081700740408539025937 210958561275555306404269453)
                ·
                  refine ⟨79109460478333239901601045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210958561275555306404269453 79109460478333239901601045)
                  ·
                    refine ⟨3708255959921870620387549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79109460478333239901601045 3708255959921870620387549)
                    ·
                      refine ⟨1390595984970701482645331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708255959921870620387549 1390595984970701482645331)
                      ·
                        rfl

theorem cell23_2708176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_2708176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708176 prefixEnd_2708176 := by exact prefixLift 2708176
  have htrace : WordTrace (prefixWord ++ tailWord_2708176) baseStart_2708176 baseEnd_2708176 := by
    simpa [prefixWord, tailWord_2708176, baseEnd_2708176] using wordTrace_append hprefix tailTrace_2708176
  have hstable : (prefixWord ++ tailWord_2708176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708176).length < 2 ^ (prefixWord ++ tailWord_2708176).sum := by decide
  have hdescent : baseEnd_2708176 < baseStart_2708176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708193 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2708193 : Nat := 118140960795 + 2708193 * 2 ^ 59
def prefixEnd_2708193 : Nat := 4983230072969 + 3 ^ 40 * 2708193 * 2
def baseEnd_2708193 : Nat := 1390604714141827916132753

theorem tailTrace_2708193 : CollatzResearch.WordTrace tailWord_2708193 prefixEnd_2708193 1390604714141827916132753 := by
  unfold tailWord_2708193
  simp only [CollatzResearch.WordTrace]
  refine ⟨98775913477686758386209233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65850608985124505590806155 98775913477686758386209233)
  ·
    refine ⟨74081935108265068789656925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98775913477686758386209233 74081935108265068789656925)
    ·
      refine ⟨27780725665599400796121347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74081935108265068789656925 27780725665599400796121347)
      ·
        refine ⟨41671088498399101194182021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27780725665599400796121347 41671088498399101194182021)
        ·
          refine ⟨7813329093449831473909129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41671088498399101194182021 7813329093449831473909129)
          ·
            refine ⟨5859996820087373605431847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813329093449831473909129 5859996820087373605431847)
            ·
              refine ⟨8789995230131060408147771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859996820087373605431847 8789995230131060408147771)
              ·
                refine ⟨13184992845196590612221657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8789995230131060408147771 13184992845196590612221657)
                ·
                  refine ⟨9888744633897442959166243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13184992845196590612221657 9888744633897442959166243)
                  ·
                    refine ⟨14833116950846164438749365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9888744633897442959166243 14833116950846164438749365)
                    ·
                      refine ⟨1390604714141827916132753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14833116950846164438749365 1390604714141827916132753)
                      ·
                        rfl

theorem cell23_2708193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2708193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708193 prefixEnd_2708193 := by exact prefixLift 2708193
  have htrace : WordTrace (prefixWord ++ tailWord_2708193) baseStart_2708193 baseEnd_2708193 := by
    simpa [prefixWord, tailWord_2708193, baseEnd_2708193] using wordTrace_append hprefix tailTrace_2708193
  have hstable : (prefixWord ++ tailWord_2708193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708193).length < 2 ^ (prefixWord ++ tailWord_2708193).sum := by decide
  have hdescent : baseEnd_2708193 < baseStart_2708193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708236 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2708236 : Nat := 118140960795 + 2708236 * 2 ^ 59
def prefixEnd_2708236 : Nat := 4983230072969 + 3 ^ 40 * 2708236 * 2
def baseEnd_2708236 : Nat := 1390626793809971247895055

theorem tailTrace_2708236 : CollatzResearch.WordTrace tailWord_2708236 prefixEnd_2708236 1390626793809971247895055 := by
  unfold tailWord_2708236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49388740908265488365012281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65851654544353984486683041 49388740908265488365012281)
  ·
    refine ⟨37041555681199116273759211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49388740908265488365012281 37041555681199116273759211)
    ·
      refine ⟨55562333521798674410638817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37041555681199116273759211 55562333521798674410638817)
      ·
        refine ⟨41671750141349005807979113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55562333521798674410638817 41671750141349005807979113)
        ·
          refine ⟨31253812606011754355984335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41671750141349005807979113 31253812606011754355984335)
          ·
            refine ⟨46880718909017631533976503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31253812606011754355984335 46880718909017631533976503)
            ·
              refine ⟨70321078363526447300964755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46880718909017631533976503 70321078363526447300964755)
              ·
                refine ⟨105481617545289670951447133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70321078363526447300964755 105481617545289670951447133)
                ·
                  refine ⟨39555606579483626606792675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105481617545289670951447133 39555606579483626606792675)
                  ·
                    refine ⟨59333409869225439910189013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39555606579483626606792675 59333409869225439910189013)
                    ·
                      refine ⟨1390626793809971247895055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59333409869225439910189013 1390626793809971247895055)
                      ·
                        rfl

theorem cell23_2708236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2708236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708236 prefixEnd_2708236 := by exact prefixLift 2708236
  have htrace : WordTrace (prefixWord ++ tailWord_2708236) baseStart_2708236 baseEnd_2708236 := by
    simpa [prefixWord, tailWord_2708236, baseEnd_2708236] using wordTrace_append hprefix tailTrace_2708236
  have hstable : (prefixWord ++ tailWord_2708236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708236).length < 2 ^ (prefixWord ++ tailWord_2708236).sum := by decide
  have hdescent : baseEnd_2708236 < baseStart_2708236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708243 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 2, 5]
def baseStart_2708243 : Nat := 118140960795 + 2708243 * 2 ^ 59
def prefixEnd_2708243 : Nat := 4983230072969 + 3 ^ 40 * 2708243 * 2
def baseEnd_2708243 : Nat := 463543462724850906835841

theorem tailTrace_2708243 : CollatzResearch.WordTrace tailWord_2708243 prefixEnd_2708243 463543462724850906835841 := by
  unfold tailWord_2708243
  simp only [CollatzResearch.WordTrace]
  refine ⟨98777737127505616925529383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65851824751670411283686255 98777737127505616925529383)
  ·
    refine ⟨148166605691258425388294075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98777737127505616925529383 148166605691258425388294075)
    ·
      refine ⟨222249908536887638082441113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148166605691258425388294075 222249908536887638082441113)
      ·
        refine ⟨166687431402665728561830835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222249908536887638082441113 166687431402665728561830835)
        ·
          refine ⟨250031147103998592842746253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166687431402665728561830835 250031147103998592842746253)
          ·
            refine ⟨93761680163999472316029845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250031147103998592842746253 93761680163999472316029845)
            ·
              refine ⟨4395078757687475264813899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93761680163999472316029845 4395078757687475264813899)
              ·
                refine ⟨6592618136531212897220849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395078757687475264813899 6592618136531212897220849)
                ·
                  refine ⟨4944463602398409672915637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6592618136531212897220849 4944463602398409672915637)
                  ·
                    refine ⟨463543462724850906835841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4944463602398409672915637 463543462724850906835841)
                    ·
                      rfl

theorem cell23_2708243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 5].length) (baseStart_2708243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708243 prefixEnd_2708243 := by exact prefixLift 2708243
  have htrace : WordTrace (prefixWord ++ tailWord_2708243) baseStart_2708243 baseEnd_2708243 := by
    simpa [prefixWord, tailWord_2708243, baseEnd_2708243] using wordTrace_append hprefix tailTrace_2708243
  have hstable : (prefixWord ++ tailWord_2708243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708243).length < 2 ^ (prefixWord ++ tailWord_2708243).sum := by decide
  have hdescent : baseEnd_2708243 < baseStart_2708243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708270 : List Nat := [4, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2708270 : Nat := 118140960795 + 2708270 * 2 ^ 59
def prefixEnd_2708270 : Nat := 4983230072969 + 3 ^ 40 * 2708270 * 2
def baseEnd_2708270 : Nat := 1390644252152224114869899

theorem tailTrace_2708270 : CollatzResearch.WordTrace tailWord_2708270 prefixEnd_2708270 1390644252152224114869899 := by
  unfold tailWord_2708270
  simp only [CollatzResearch.WordTrace]
  refine ⟨12347340237300975067095283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65852481265605200357841509 12347340237300975067095283)
  ·
    refine ⟨18521010355951462600642925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12347340237300975067095283 18521010355951462600642925)
    ·
      refine ⟨6945378883481798475241097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18521010355951462600642925 6945378883481798475241097)
      ·
        refine ⟨5209034162611348856430823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6945378883481798475241097 5209034162611348856430823)
        ·
          refine ⟨7813551243917023284646235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209034162611348856430823 7813551243917023284646235)
          ·
            refine ⟨11720326865875534926969353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813551243917023284646235 11720326865875534926969353)
            ·
              refine ⟨8790245149406651195227015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11720326865875534926969353 8790245149406651195227015)
              ·
                refine ⟨13185367724109976792840523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790245149406651195227015 13185367724109976792840523)
                ·
                  refine ⟨19778051586164965189260785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13185367724109976792840523 19778051586164965189260785)
                  ·
                    refine ⟨14833538689623723891945589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19778051586164965189260785 14833538689623723891945589)
                    ·
                      refine ⟨1390644252152224114869899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14833538689623723891945589 1390644252152224114869899)
                      ·
                        rfl

theorem cell23_2708270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2708270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708270 prefixEnd_2708270 := by exact prefixLift 2708270
  have htrace : WordTrace (prefixWord ++ tailWord_2708270) baseStart_2708270 baseEnd_2708270 := by
    simpa [prefixWord, tailWord_2708270, baseEnd_2708270] using wordTrace_append hprefix tailTrace_2708270
  have hstable : (prefixWord ++ tailWord_2708270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708270).length < 2 ^ (prefixWord ++ tailWord_2708270).sum := by decide
  have hdescent : baseEnd_2708270 < baseStart_2708270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708280 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_2708280 : Nat := 118140960795 + 2708280 * 2 ^ 59
def prefixEnd_2708280 : Nat := 4983230072969 + 3 ^ 40 * 2708280 * 2
def baseEnd_2708280 : Nat := 1390649386958769075744853

theorem tailTrace_2708280 : CollatzResearch.WordTrace tailWord_2708280 prefixEnd_2708280 1390649386958769075744853 := by
  unfold tailWord_2708280
  simp only [CollatzResearch.WordTrace]
  refine ⟨49389543314185786122313147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65852724418914381496417529 49389543314185786122313147)
  ·
    refine ⟨74084314971278679183469721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49389543314185786122313147 74084314971278679183469721)
    ·
      refine ⟨55563236228459009387602291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74084314971278679183469721 55563236228459009387602291)
      ·
        refine ⟨83344854342688514081403437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55563236228459009387602291 83344854342688514081403437)
        ·
          refine ⟨31254320378508192780526289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83344854342688514081403437 31254320378508192780526289)
          ·
            refine ⟨23440740283881144585394717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31254320378508192780526289 23440740283881144585394717)
            ·
              refine ⟨8790277606455429219523019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23440740283881144585394717 8790277606455429219523019)
              ·
                refine ⟨13185416409683143829284529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790277606455429219523019 13185416409683143829284529)
                ·
                  refine ⟨9889062307262357871963397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13185416409683143829284529 9889062307262357871963397)
                  ·
                    refine ⟨1854199182611692100993137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9889062307262357871963397 1854199182611692100993137)
                    ·
                      refine ⟨1390649386958769075744853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854199182611692100993137 1390649386958769075744853)
                      ·
                        rfl

theorem cell23_2708280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_2708280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708280 prefixEnd_2708280 := by exact prefixLift 2708280
  have htrace : WordTrace (prefixWord ++ tailWord_2708280) baseStart_2708280 baseEnd_2708280 := by
    simpa [prefixWord, tailWord_2708280, baseEnd_2708280] using wordTrace_append hprefix tailTrace_2708280
  have hstable : (prefixWord ++ tailWord_2708280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708280).length < 2 ^ (prefixWord ++ tailWord_2708280).sum := by decide
  have hdescent : baseEnd_2708280 < baseStart_2708280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708300 : List Nat := [2, 2, 1, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2708300 : Nat := 118140960795 + 2708300 * 2 ^ 59
def prefixEnd_2708300 : Nat := 4983230072969 + 3 ^ 40 * 2708300 * 2
def baseEnd_2708300 : Nat := 1390659656571858997494761

theorem tailTrace_2708300 : CollatzResearch.WordTrace tailWord_2708300 prefixEnd_2708300 1390659656571858997494761 := by
  unfold tailWord_2708300
  simp only [CollatzResearch.WordTrace]
  refine ⟨49389908044149557830177177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65853210725532743773569569 49389908044149557830177177)
  ·
    refine ⟨37042431033112168372632883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49389908044149557830177177 37042431033112168372632883)
    ·
      refine ⟨55563646549668252558949325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37042431033112168372632883 55563646549668252558949325)
      ·
        refine ⟨20836367456125594709605997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55563646549668252558949325 20836367456125594709605997)
        ·
          refine ⟨7813637796047098016102249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20836367456125594709605997 7813637796047098016102249)
          ·
            refine ⟨5860228347035323512076687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813637796047098016102249 5860228347035323512076687)
            ·
              refine ⟨8790342520552985268115031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860228347035323512076687 8790342520552985268115031)
              ·
                refine ⟨13185513780829477902172547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790342520552985268115031 13185513780829477902172547)
                ·
                  refine ⟨19778270671244216853258821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13185513780829477902172547 19778270671244216853258821)
                  ·
                    refine ⟨3708425750858290659986029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19778270671244216853258821 3708425750858290659986029)
                    ·
                      refine ⟨1390659656571858997494761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708425750858290659986029 1390659656571858997494761)
                      ·
                        rfl

theorem cell23_2708300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2708300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708300 prefixEnd_2708300 := by exact prefixLift 2708300
  have htrace : WordTrace (prefixWord ++ tailWord_2708300) baseStart_2708300 baseEnd_2708300 := by
    simpa [prefixWord, tailWord_2708300, baseEnd_2708300] using wordTrace_append hprefix tailTrace_2708300
  have hstable : (prefixWord ++ tailWord_2708300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708300).length < 2 ^ (prefixWord ++ tailWord_2708300).sum := by decide
  have hdescent : baseEnd_2708300 < baseStart_2708300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708323 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6]
def baseStart_2708323 : Nat := 118140960795 + 2708323 * 2 ^ 59
def prefixEnd_2708323 : Nat := 4983230072969 + 3 ^ 40 * 2708323 * 2
def baseEnd_2708323 : Nat := 1390671466626912407507155

theorem tailTrace_2708323 : CollatzResearch.WordTrace tailWord_2708323 prefixEnd_2708323 1390671466626912407507155 := by
  unfold tailWord_2708323
  simp only [CollatzResearch.WordTrace]
  refine ⟨98780654967215790588441623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65853769978143860392294415 98780654967215790588441623)
  ·
    refine ⟨148170982450823685882662435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98780654967215790588441623 148170982450823685882662435)
    ·
      refine ⟨222256473676235528823993653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148170982450823685882662435 222256473676235528823993653)
      ·
        refine ⟨20836544407147080827249405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222256473676235528823993653 20836544407147080827249405)
        ·
          refine ⟨7813704152680155310218527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20836544407147080827249405 7813704152680155310218527)
          ·
            refine ⟨11720556229020232965327791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813704152680155310218527 11720556229020232965327791)
            ·
              refine ⟨17580834343530349447991687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11720556229020232965327791 17580834343530349447991687)
              ·
                refine ⟨26371251515295524171987531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17580834343530349447991687 26371251515295524171987531)
                ·
                  refine ⟨39556877272943286257981297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26371251515295524171987531 39556877272943286257981297)
                  ·
                    refine ⟨29667657954707464693485973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39556877272943286257981297 29667657954707464693485973)
                    ·
                      refine ⟨1390671466626912407507155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29667657954707464693485973 1390671466626912407507155)
                      ·
                        rfl

theorem cell23_2708323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_2708323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708323 prefixEnd_2708323 := by exact prefixLift 2708323
  have htrace : WordTrace (prefixWord ++ tailWord_2708323) baseStart_2708323 baseEnd_2708323 := by
    simpa [prefixWord, tailWord_2708323, baseEnd_2708323] using wordTrace_append hprefix tailTrace_2708323
  have hstable : (prefixWord ++ tailWord_2708323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708323).length < 2 ^ (prefixWord ++ tailWord_2708323).sum := by decide
  have hdescent : baseEnd_2708323 < baseStart_2708323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708363 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 1, 6]
def baseStart_2708363 : Nat := 118140960795 + 2708363 * 2 ^ 59
def prefixEnd_2708363 : Nat := 4983230072969 + 3 ^ 40 * 2708363 * 2
def baseEnd_2708363 : Nat := 463564001951030750335657

theorem tailTrace_2708363 : CollatzResearch.WordTrace tailWord_2708363 prefixEnd_2708363 463564001951030750335657 := by
  unfold tailWord_2708363
  simp only [CollatzResearch.WordTrace]
  refine ⟨98782113887070877419897743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65854742591380584946598495 98782113887070877419897743)
  ·
    refine ⟨148173170830606316129846615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98782113887070877419897743 148173170830606316129846615)
    ·
      refine ⟨222259756245909474194769923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148173170830606316129846615 222259756245909474194769923)
      ·
        refine ⟨333389634368864211292154885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222259756245909474194769923 333389634368864211292154885)
        ·
          refine ⟨62510556444162039617279041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333389634368864211292154885 62510556444162039617279041)
          ·
            refine ⟨46882917333121529712959281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62510556444162039617279041 46882917333121529712959281)
            ·
              refine ⟨35162187999841147284719461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46882917333121529712959281 35162187999841147284719461)
              ·
                refine ⟨6592910249970215115884899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35162187999841147284719461 6592910249970215115884899)
                ·
                  refine ⟨9889365374955322673827349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6592910249970215115884899 9889365374955322673827349)
                  ·
                    refine ⟨463564001951030750335657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9889365374955322673827349 463564001951030750335657)
                    ·
                      rfl

theorem cell23_2708363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 6].length) (baseStart_2708363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708363 prefixEnd_2708363 := by exact prefixLift 2708363
  have htrace : WordTrace (prefixWord ++ tailWord_2708363) baseStart_2708363 baseEnd_2708363 := by
    simpa [prefixWord, tailWord_2708363, baseEnd_2708363] using wordTrace_append hprefix tailTrace_2708363
  have hstable : (prefixWord ++ tailWord_2708363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708363).length < 2 ^ (prefixWord ++ tailWord_2708363).sum := by decide
  have hdescent : baseEnd_2708363 < baseStart_2708363 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708364 : List Nat := [2, 2, 1, 2, 1, 2, 5, 3, 1, 1, 3]
def baseStart_2708364 : Nat := 118140960795 + 2708364 * 2 ^ 59
def prefixEnd_2708364 : Nat := 4983230072969 + 3 ^ 40 * 2708364 * 2
def baseEnd_2708364 : Nat := 1390692519333746747094467

theorem tailTrace_2708364 : CollatzResearch.WordTrace tailWord_2708364 prefixEnd_2708364 1390692519333746747094467 := by
  unfold tailWord_2708364
  simp only [CollatzResearch.WordTrace]
  refine ⟨49391075180033627295342073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65854766906711503060456097 49391075180033627295342073)
  ·
    refine ⟨37043306385025220471506555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49391075180033627295342073 37043306385025220471506555)
    ·
      refine ⟨55564959577537830707259833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37043306385025220471506555 55564959577537830707259833)
      ·
        refine ⟨41673719683153373030444875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55564959577537830707259833 41673719683153373030444875)
        ·
          refine ⟨62510579524730059545667313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41673719683153373030444875 62510579524730059545667313)
          ·
            refine ⟨46882934643547544659250485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62510579524730059545667313 46882934643547544659250485)
            ·
              refine ⟨4395275122832582311804733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46882934643547544659250485 4395275122832582311804733)
              ·
                refine ⟨1648228171062218366926775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4395275122832582311804733 1648228171062218366926775)
                ·
                  refine ⟨2472342256593327550390163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648228171062218366926775 2472342256593327550390163)
                  ·
                    refine ⟨3708513384889991325585245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472342256593327550390163 3708513384889991325585245)
                    ·
                      refine ⟨1390692519333746747094467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708513384889991325585245 1390692519333746747094467)
                      ·
                        rfl

theorem cell23_2708364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_2708364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708364 prefixEnd_2708364 := by exact prefixLift 2708364
  have htrace : WordTrace (prefixWord ++ tailWord_2708364) baseStart_2708364 baseEnd_2708364 := by
    simpa [prefixWord, tailWord_2708364, baseEnd_2708364] using wordTrace_append hprefix tailTrace_2708364
  have hstable : (prefixWord ++ tailWord_2708364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708364).length < 2 ^ (prefixWord ++ tailWord_2708364).sum := by decide
  have hdescent : baseEnd_2708364 < baseStart_2708364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708381 : List Nat := [1, 4, 2, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_2708381 : Nat := 118140960795 + 2708381 * 2 ^ 59
def prefixEnd_2708381 : Nat := 4983230072969 + 3 ^ 40 * 2708381 * 2
def baseEnd_2708381 : Nat := 1390701248504873180581889

theorem tailTrace_2708381 : CollatzResearch.WordTrace tailWord_2708381 prefixEnd_2708381 1390701248504873180581889 := by
  unfold tailWord_2708381
  simp only [CollatzResearch.WordTrace]
  refine ⟨98782770401005666494052997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65855180267337110996035331 98782770401005666494052997)
  ·
    refine ⟨18521769450188562467634937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98782770401005666494052997 18521769450188562467634937)
    ·
      refine ⟨13891327087641421850726203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18521769450188562467634937 13891327087641421850726203)
      ·
        refine ⟨20836990631462132776089305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13891327087641421850726203 20836990631462132776089305)
        ·
          refine ⟨15627742973596599582066979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20836990631462132776089305 15627742973596599582066979)
          ·
            refine ⟨23441614460394899373100469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15627742973596599582066979 23441614460394899373100469)
            ·
              refine ⟨2197651355662021816228169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23441614460394899373100469 2197651355662021816228169)
              ·
                refine ⟨1648238516746516362171127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197651355662021816228169 1648238516746516362171127)
                ·
                  refine ⟨2472357775119774543256691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648238516746516362171127 2472357775119774543256691)
                  ·
                    refine ⟨3708536662679661814885037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472357775119774543256691 3708536662679661814885037)
                    ·
                      refine ⟨1390701248504873180581889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708536662679661814885037 1390701248504873180581889)
                      ·
                        rfl

theorem cell23_2708381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_2708381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708381 prefixEnd_2708381 := by exact prefixLift 2708381
  have htrace : WordTrace (prefixWord ++ tailWord_2708381) baseStart_2708381 baseEnd_2708381 := by
    simpa [prefixWord, tailWord_2708381, baseEnd_2708381] using wordTrace_append hprefix tailTrace_2708381
  have hstable : (prefixWord ++ tailWord_2708381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708381).length < 2 ^ (prefixWord ++ tailWord_2708381).sum := by decide
  have hdescent : baseEnd_2708381 < baseStart_2708381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708393 : List Nat := [1, 2, 1, 1, 1, 1, 8, 8]
def baseStart_2708393 : Nat := 118140960795 + 2708393 * 2 ^ 59
def prefixEnd_2708393 : Nat := 4983230072969 + 3 ^ 40 * 2708393 * 2
def baseEnd_2708393 : Nat := 51507681861952856801179

theorem tailTrace_2708393 : CollatzResearch.WordTrace tailWord_2708393 prefixEnd_2708393 51507681861952856801179 := by
  unfold tailWord_2708393
  simp only [CollatzResearch.WordTrace]
  refine ⟨98783208076962192543489833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65855472051308128362326555 98783208076962192543489833)
  ·
    refine ⟨74087406057721644407617375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98783208076962192543489833 74087406057721644407617375)
    ·
      refine ⟨111131109086582466611426063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74087406057721644407617375 111131109086582466611426063)
      ·
        refine ⟨166696663629873699917139095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111131109086582466611426063 166696663629873699917139095)
        ·
          refine ⟨250044995444810549875708643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166696663629873699917139095 250044995444810549875708643)
          ·
            refine ⟨375067493167215824813562965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250044995444810549875708643 375067493167215824813562965)
            ·
              refine ⟨4395322185553310447033941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 375067493167215824813562965 4395322185553310447033941)
              ·
                refine ⟨51507681861952856801179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4395322185553310447033941 51507681861952856801179)
                ·
                  rfl

theorem cell23_2708393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 8].length) (baseStart_2708393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708393 prefixEnd_2708393 := by exact prefixLift 2708393
  have htrace : WordTrace (prefixWord ++ tailWord_2708393) baseStart_2708393 baseEnd_2708393 := by
    simpa [prefixWord, tailWord_2708393, baseEnd_2708393] using wordTrace_append hprefix tailTrace_2708393
  have hstable : (prefixWord ++ tailWord_2708393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708393).length < 2 ^ (prefixWord ++ tailWord_2708393).sum := by decide
  have hdescent : baseEnd_2708393 < baseStart_2708393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708404 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2708404 : Nat := 118140960795 + 2708404 * 2 ^ 59
def prefixEnd_2708404 : Nat := 4983230072969 + 3 ^ 40 * 2708404 * 2
def baseEnd_2708404 : Nat := 1390713058559926590594283

theorem tailTrace_2708404 : CollatzResearch.WordTrace tailWord_2708404 prefixEnd_2708404 1390713058559926590594283 := by
  unfold tailWord_2708404
  simp only [CollatzResearch.WordTrace]
  refine ⟨49391804639961170711070133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65855739519948227614760177 49391804639961170711070133)
  ·
    refine ⟨4630481684996359754162825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49391804639961170711070133 4630481684996359754162825)
    ·
      refine ⟨3472861263747269815622119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4630481684996359754162825 3472861263747269815622119)
      ·
        refine ⟨5209291895620904723433179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472861263747269815622119 5209291895620904723433179)
        ·
          refine ⟨7813937843431357085149769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209291895620904723433179 7813937843431357085149769)
          ·
            refine ⟨5860453382573517813862327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813937843431357085149769 5860453382573517813862327)
            ·
              refine ⟨8790680073860276720793491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860453382573517813862327 8790680073860276720793491)
              ·
                refine ⟨13186020110790415081190237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790680073860276720793491 13186020110790415081190237)
                ·
                  refine ⟨4944757541546405655446339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13186020110790415081190237 4944757541546405655446339)
                  ·
                    refine ⟨7417136312319608483169509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4944757541546405655446339 7417136312319608483169509)
                    ·
                      refine ⟨1390713058559926590594283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7417136312319608483169509 1390713058559926590594283)
                      ·
                        rfl

theorem cell23_2708404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2708404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708404 prefixEnd_2708404 := by exact prefixLift 2708404
  have htrace : WordTrace (prefixWord ++ tailWord_2708404) baseStart_2708404 baseEnd_2708404 := by
    simpa [prefixWord, tailWord_2708404, baseEnd_2708404] using wordTrace_append hprefix tailTrace_2708404
  have hstable : (prefixWord ++ tailWord_2708404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708404).length < 2 ^ (prefixWord ++ tailWord_2708404).sum := by decide
  have hdescent : baseEnd_2708404 < baseStart_2708404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708407 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 3]
def baseStart_2708407 : Nat := 118140960795 + 2708407 * 2 ^ 59
def prefixEnd_2708407 : Nat := 4983230072969 + 3 ^ 40 * 2708407 * 2
def baseEnd_2708407 : Nat := 1390714599001890078856769

theorem tailTrace_2708407 : CollatzResearch.WordTrace tailWord_2708407 prefixEnd_2708407 1390714599001890078856769 := by
  unfold tailWord_2708407
  simp only [CollatzResearch.WordTrace]
  refine ⟨98783718698911472934499475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65855812465940981956332983 98783718698911472934499475)
  ·
    refine ⟨148175578048367209401749213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98783718698911472934499475 148175578048367209401749213)
    ·
      refine ⟨55565841768137703525655955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148175578048367209401749213 55565841768137703525655955)
      ·
        refine ⟨83348762652206555288483933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55565841768137703525655955 83348762652206555288483933)
        ·
          refine ⟨31255785994577458233181475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83348762652206555288483933 31255785994577458233181475)
          ·
            refine ⟨46883678991866187349772213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31255785994577458233181475 46883678991866187349772213)
            ·
              refine ⟨4395344905487455064041145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46883678991866187349772213 4395344905487455064041145)
              ·
                refine ⟨3296508679115591298030859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395344905487455064041145 3296508679115591298030859)
                ·
                  refine ⟨4944763018673386947046289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296508679115591298030859 4944763018673386947046289)
                  ·
                    refine ⟨3708572264005040210284717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4944763018673386947046289 3708572264005040210284717)
                    ·
                      refine ⟨1390714599001890078856769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708572264005040210284717 1390714599001890078856769)
                      ·
                        rfl

theorem cell23_2708407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_2708407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708407 prefixEnd_2708407 := by exact prefixLift 2708407
  have htrace : WordTrace (prefixWord ++ tailWord_2708407) baseStart_2708407 baseEnd_2708407 := by
    simpa [prefixWord, tailWord_2708407, baseEnd_2708407] using wordTrace_append hprefix tailTrace_2708407
  have hstable : (prefixWord ++ tailWord_2708407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708407).length < 2 ^ (prefixWord ++ tailWord_2708407).sum := by decide
  have hdescent : baseEnd_2708407 < baseStart_2708407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708424 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_2708424 : Nat := 118140960795 + 2708424 * 2 ^ 59
def prefixEnd_2708424 : Nat := 4983230072969 + 3 ^ 40 * 2708424 * 2
def baseEnd_2708424 : Nat := 1390723328173016512344191

theorem tailTrace_2708424 : CollatzResearch.WordTrace tailWord_2708424 prefixEnd_2708424 1390723328173016512344191 := by
  unfold tailWord_2708424
  simp only [CollatzResearch.WordTrace]
  refine ⟨49392169369924942418934163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65856225826566589891912217 49392169369924942418934163)
  ·
    refine ⟨74088254054887413628401245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49392169369924942418934163 74088254054887413628401245)
    ·
      refine ⟨27783095270582780110650467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74088254054887413628401245 27783095270582780110650467)
      ·
        refine ⟨41674642905874170165975701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27783095270582780110650467 41674642905874170165975701)
        ·
          refine ⟨1953498886212851726530111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41674642905874170165975701 1953498886212851726530111)
          ·
            refine ⟨2930248329319277589795167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953498886212851726530111 2930248329319277589795167)
            ·
              refine ⟨4395372493978916384692751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930248329319277589795167 4395372493978916384692751)
              ·
                refine ⟨6593058740968374577039127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395372493978916384692751 6593058740968374577039127)
                ·
                  refine ⟨9889588111452561865558691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593058740968374577039127 9889588111452561865558691)
                  ·
                    refine ⟨14834382167178842798338037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9889588111452561865558691 14834382167178842798338037)
                    ·
                      refine ⟨1390723328173016512344191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14834382167178842798338037 1390723328173016512344191)
                      ·
                        rfl

theorem cell23_2708424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_2708424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708424 prefixEnd_2708424 := by exact prefixLift 2708424
  have htrace : WordTrace (prefixWord ++ tailWord_2708424) baseStart_2708424 baseEnd_2708424 := by
    simpa [prefixWord, tailWord_2708424, baseEnd_2708424] using wordTrace_append hprefix tailTrace_2708424
  have hstable : (prefixWord ++ tailWord_2708424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708424).length < 2 ^ (prefixWord ++ tailWord_2708424).sum := by decide
  have hdescent : baseEnd_2708424 < baseStart_2708424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708481 : List Nat := [1, 2, 4, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_2708481 : Nat := 118140960795 + 2708481 * 2 ^ 59
def prefixEnd_2708481 : Nat := 4983230072969 + 3 ^ 40 * 2708481 * 2
def baseEnd_2708481 : Nat := 1390752596570322789331429

theorem tailTrace_2708481 : CollatzResearch.WordTrace tailWord_2708481 prefixEnd_2708481 1390752596570322789331429 := by
  unfold tailWord_2708481
  simp only [CollatzResearch.WordTrace]
  refine ⟨98786417700643383572693297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65857611800428922381795531 98786417700643383572693297)
  ·
    refine ⟨74089813275482537679519973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98786417700643383572693297 74089813275482537679519973)
    ·
      refine ⟨13891839989152975814909995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74089813275482537679519973 13891839989152975814909995)
      ·
        refine ⟨20837759983729463722364993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13891839989152975814909995 20837759983729463722364993)
        ·
          refine ⟨15628319987797097791773745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20837759983729463722364993 15628319987797097791773745)
          ·
            refine ⟨11721239990847823343830309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15628319987797097791773745 11721239990847823343830309)
            ·
              refine ⟨2197732498283966876968183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11721239990847823343830309 2197732498283966876968183)
              ·
                refine ⟨3296598747425950315452275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197732498283966876968183 3296598747425950315452275)
                ·
                  refine ⟨4944898121138925473178413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296598747425950315452275 4944898121138925473178413)
                  ·
                    refine ⟨1854336795427097052441905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4944898121138925473178413 1854336795427097052441905)
                    ·
                      refine ⟨1390752596570322789331429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854336795427097052441905 1390752596570322789331429)
                      ·
                        rfl

theorem cell23_2708481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_2708481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708481 prefixEnd_2708481 := by exact prefixLift 2708481
  have htrace : WordTrace (prefixWord ++ tailWord_2708481) baseStart_2708481 baseEnd_2708481 := by
    simpa [prefixWord, tailWord_2708481, baseEnd_2708481] using wordTrace_append hprefix tailTrace_2708481
  have hstable : (prefixWord ++ tailWord_2708481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708481).length < 2 ^ (prefixWord ++ tailWord_2708481).sum := by decide
  have hdescent : baseEnd_2708481 < baseStart_2708481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708530 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_2708530 : Nat := 118140960795 + 2708530 * 2 ^ 59
def prefixEnd_2708530 : Nat := 4983230072969 + 3 ^ 40 * 2708530 * 2
def baseEnd_2708530 : Nat := 463592585707464365872901

theorem tailTrace_2708530 : CollatzResearch.WordTrace tailWord_2708530 prefixEnd_2708530 463592585707464365872901 := by
  unfold tailWord_2708530
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697051219366466235306761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65858803251643909960818029 24697051219366466235306761)
  ·
    refine ⟨18522788414524849676480071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24697051219366466235306761 18522788414524849676480071)
    ·
      refine ⟨27784182621787274514720107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18522788414524849676480071 27784182621787274514720107)
      ·
        refine ⟨41676273932680911772080161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27784182621787274514720107 41676273932680911772080161)
        ·
          refine ⟨31257205449510683829060121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41676273932680911772080161 31257205449510683829060121)
          ·
            refine ⟨23442904087133012871795091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31257205449510683829060121 23442904087133012871795091)
            ·
              refine ⟨35164356130699519307692637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23442904087133012871795091 35164356130699519307692637)
              ·
                refine ⟨13186633549012319740384739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35164356130699519307692637 13186633549012319740384739)
                ·
                  refine ⟨19779950323518479610577109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13186633549012319740384739 19779950323518479610577109)
                  ·
                    refine ⟨463592585707464365872901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19779950323518479610577109 463592585707464365872901)
                    ·
                      rfl

theorem cell23_2708530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_2708530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708530 prefixEnd_2708530 := by exact prefixLift 2708530
  have htrace : WordTrace (prefixWord ++ tailWord_2708530) baseStart_2708530 baseEnd_2708530 := by
    simpa [prefixWord, tailWord_2708530, baseEnd_2708530] using wordTrace_append hprefix tailTrace_2708530
  have hstable : (prefixWord ++ tailWord_2708530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708530).length < 2 ^ (prefixWord ++ tailWord_2708530).sum := by decide
  have hdescent : baseEnd_2708530 < baseStart_2708530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708557 : List Nat := [1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2708557 : Nat := 118140960795 + 2708557 * 2 ^ 59
def prefixEnd_2708557 : Nat := 4983230072969 + 3 ^ 40 * 2708557 * 2
def baseEnd_2708557 : Nat := 1390791621100064491981079

theorem tailTrace_2708557 : CollatzResearch.WordTrace tailWord_2708557 prefixEnd_2708557 1390791621100064491981079 := by
  unfold tailWord_2708557
  simp only [CollatzResearch.WordTrace]
  refine ⟨98789189648368048552459925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65859459765578699034973283 98789189648368048552459925)
  ·
    refine ⟨4630743264767252275896559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 98789189648368048552459925 4630743264767252275896559)
    ·
      refine ⟨6946114897150878413844839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4630743264767252275896559 6946114897150878413844839)
      ·
        refine ⟨10419172345726317620767259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6946114897150878413844839 10419172345726317620767259)
        ·
          refine ⟨15628758518589476431150889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10419172345726317620767259 15628758518589476431150889)
          ·
            refine ⟨11721568888942107323363167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15628758518589476431150889 11721568888942107323363167)
            ·
              refine ⟨17582353333413160985044751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11721568888942107323363167 17582353333413160985044751)
              ·
                refine ⟨26373530000119741477567127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17582353333413160985044751 26373530000119741477567127)
                ·
                  refine ⟨39560295000179612216350691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26373530000119741477567127 39560295000179612216350691)
                  ·
                    refine ⟨59340442500269418324526037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39560295000179612216350691 59340442500269418324526037)
                    ·
                      refine ⟨1390791621100064491981079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 59340442500269418324526037 1390791621100064491981079)
                      ·
                        rfl

theorem cell23_2708557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2708557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708557 prefixEnd_2708557 := by exact prefixLift 2708557
  have htrace : WordTrace (prefixWord ++ tailWord_2708557) baseStart_2708557 baseEnd_2708557 := by
    simpa [prefixWord, tailWord_2708557, baseEnd_2708557] using wordTrace_append hprefix tailTrace_2708557
  have hstable : (prefixWord ++ tailWord_2708557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708557).length < 2 ^ (prefixWord ++ tailWord_2708557).sum := by decide
  have hdescent : baseEnd_2708557 < baseStart_2708557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708567 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 6, 2]
def baseStart_2708567 : Nat := 118140960795 + 2708567 * 2 ^ 59
def prefixEnd_2708567 : Nat := 4983230072969 + 3 ^ 40 * 2708567 * 2
def baseEnd_2708567 : Nat := 1390796755906609452856033

theorem tailTrace_2708567 : CollatzResearch.WordTrace tailWord_2708567 prefixEnd_2708567 1390796755906609452856033 := by
  unfold tailWord_2708567
  simp only [CollatzResearch.WordTrace]
  refine ⟨98789554378331820260323955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65859702918887880173549303 98789554378331820260323955)
  ·
    refine ⟨148184331567497730390485933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98789554378331820260323955 148184331567497730390485933)
    ·
      refine ⟨55569124337811648896432225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148184331567497730390485933 55569124337811648896432225)
      ·
        refine ⟨41676843253358736672324169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55569124337811648896432225 41676843253358736672324169)
        ·
          refine ⟨31257632440019052504243127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41676843253358736672324169 31257632440019052504243127)
          ·
            refine ⟨46886448660028578756364691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31257632440019052504243127 46886448660028578756364691)
            ·
              refine ⟨70329672990042868134547037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46886448660028578756364691 70329672990042868134547037)
              ·
                refine ⟨26373627371266075550455139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70329672990042868134547037 26373627371266075550455139)
                ·
                  refine ⟨39560441056899113325682709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26373627371266075550455139 39560441056899113325682709)
                  ·
                    refine ⟨1854395674542145937141377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 39560441056899113325682709 1854395674542145937141377)
                    ·
                      refine ⟨1390796755906609452856033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854395674542145937141377 1390796755906609452856033)
                      ·
                        rfl

theorem cell23_2708567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_2708567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708567 prefixEnd_2708567 := by exact prefixLift 2708567
  have htrace : WordTrace (prefixWord ++ tailWord_2708567) baseStart_2708567 baseEnd_2708567 := by
    simpa [prefixWord, tailWord_2708567, baseEnd_2708567] using wordTrace_append hprefix tailTrace_2708567
  have hstable : (prefixWord ++ tailWord_2708567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708567).length < 2 ^ (prefixWord ++ tailWord_2708567).sum := by decide
  have hdescent : baseEnd_2708567 < baseStart_2708567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708577 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2708577 : Nat := 118140960795 + 2708577 * 2 ^ 59
def prefixEnd_2708577 : Nat := 4983230072969 + 3 ^ 40 * 2708577 * 2
def baseEnd_2708577 : Nat := 463600630237718137910329

theorem tailTrace_2708577 : CollatzResearch.WordTrace tailWord_2708577 prefixEnd_2708577 463600630237718137910329 := by
  unfold tailWord_2708577
  simp only [CollatzResearch.WordTrace]
  refine ⟨98789919108295591968187985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65859946072197061312125323 98789919108295591968187985)
  ·
    refine ⟨74092439331221693976140989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98789919108295591968187985 74092439331221693976140989)
    ·
      refine ⟨27784664749208135241052871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74092439331221693976140989 27784664749208135241052871)
      ·
        refine ⟨41676997123812202861579307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27784664749208135241052871 41676997123812202861579307)
        ·
          refine ⟨62515495685718304292368961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41676997123812202861579307 62515495685718304292368961)
          ·
            refine ⟨46886621764288728219276721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62515495685718304292368961 46886621764288728219276721)
            ·
              refine ⟨35164966323216546164457541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46886621764288728219276721 35164966323216546164457541)
              ·
                refine ⟨6593431185603102405835789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35164966323216546164457541 6593431185603102405835789)
                ·
                  refine ⟨2472536694601163402188421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6593431185603102405835789 2472536694601163402188421)
                  ·
                    refine ⟨463600630237718137910329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2472536694601163402188421 463600630237718137910329)
                    ·
                      rfl

theorem cell23_2708577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2708577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708577 prefixEnd_2708577 := by exact prefixLift 2708577
  have htrace : WordTrace (prefixWord ++ tailWord_2708577) baseStart_2708577 baseEnd_2708577 := by
    simpa [prefixWord, tailWord_2708577, baseEnd_2708577] using wordTrace_append hprefix tailTrace_2708577
  have hstable : (prefixWord ++ tailWord_2708577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708577).length < 2 ^ (prefixWord ++ tailWord_2708577).sum := by decide
  have hdescent : baseEnd_2708577 < baseStart_2708577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708580 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2708580 : Nat := 118140960795 + 2708580 * 2 ^ 59
def prefixEnd_2708580 : Nat := 4983230072969 + 3 ^ 40 * 2708580 * 2
def baseEnd_2708580 : Nat := 1390803431155117901993473

theorem tailTrace_2708580 : CollatzResearch.WordTrace tailWord_2708580 prefixEnd_2708580 1390803431155117901993473 := by
  unfold tailWord_2708580
  simp only [CollatzResearch.WordTrace]
  refine ⟨49395014263642361740273597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65860019018189815653698129 49395014263642361740273597)
  ·
    refine ⟨18523130348865885652602599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49395014263642361740273597 18523130348865885652602599)
    ·
      refine ⟨27784695523298828478903899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18523130348865885652602599 27784695523298828478903899)
      ·
        refine ⟨41677043284948242718355849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27784695523298828478903899 41677043284948242718355849)
        ·
          refine ⟨31257782463711182038766887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41677043284948242718355849 31257782463711182038766887)
          ·
            refine ⟨46886673695566773058150331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31257782463711182038766887 46886673695566773058150331)
            ·
              refine ⟨70330010543350159587225497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46886673695566773058150331 70330010543350159587225497)
              ·
                refine ⟨52747507907512619690419123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70330010543350159587225497 52747507907512619690419123)
                ·
                  refine ⟨79121261861268929535628685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52747507907512619690419123 79121261861268929535628685)
                  ·
                    refine ⟨29670473197975848575860757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79121261861268929535628685 29670473197975848575860757)
                    ·
                      refine ⟨1390803431155117901993473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29670473197975848575860757 1390803431155117901993473)
                      ·
                        rfl

theorem cell23_2708580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2708580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708580 prefixEnd_2708580 := by exact prefixLift 2708580
  have htrace : WordTrace (prefixWord ++ tailWord_2708580) baseStart_2708580 baseEnd_2708580 := by
    simpa [prefixWord, tailWord_2708580, baseEnd_2708580] using wordTrace_append hprefix tailTrace_2708580
  have hstable : (prefixWord ++ tailWord_2708580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708580).length < 2 ^ (prefixWord ++ tailWord_2708580).sum := by decide
  have hdescent : baseEnd_2708580 < baseStart_2708580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708637 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_2708637 : Nat := 118140960795 + 2708637 * 2 ^ 59
def prefixEnd_2708637 : Nat := 4983230072969 + 3 ^ 40 * 2708637 * 2
def baseEnd_2708637 : Nat := 463610899850808059660237

theorem tailTrace_2708637 : CollatzResearch.WordTrace tailWord_2708637 prefixEnd_2708637 463610899850808059660237 := by
  unfold tailWord_2708637
  simp only [CollatzResearch.WordTrace]
  refine ⟨98792107488078222215372165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65861404992052148143581443 98792107488078222215372165)
  ·
    refine ⟨18523520154014666665382281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98792107488078222215372165 18523520154014666665382281)
    ·
      refine ⟨13892640115510999999036711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18523520154014666665382281 13892640115510999999036711)
      ·
        refine ⟨20838960173266499998555067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892640115510999999036711 20838960173266499998555067)
        ·
          refine ⟨31258440259899749997832601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20838960173266499998555067 31258440259899749997832601)
          ·
            refine ⟨23443830194924812498374451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31258440259899749997832601 23443830194924812498374451)
            ·
              refine ⟨35165745292387218747561677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23443830194924812498374451 35165745292387218747561677)
              ·
                refine ⟨13187154484645207030335629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35165745292387218747561677 13187154484645207030335629)
                ·
                  refine ⟨4945182931741952636375861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13187154484645207030335629 4945182931741952636375861)
                  ·
                    refine ⟨463610899850808059660237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4945182931741952636375861 463610899850808059660237)
                    ·
                      rfl

theorem cell23_2708637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_2708637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708637 prefixEnd_2708637 := by exact prefixLift 2708637
  have htrace : WordTrace (prefixWord ++ tailWord_2708637) baseStart_2708637 baseEnd_2708637 := by
    simpa [prefixWord, tailWord_2708637, baseEnd_2708637] using wordTrace_append hprefix tailTrace_2708637
  have hstable : (prefixWord ++ tailWord_2708637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708637).length < 2 ^ (prefixWord ++ tailWord_2708637).sum := by decide
  have hdescent : baseEnd_2708637 < baseStart_2708637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708638 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_2708638 : Nat := 118140960795 + 2708638 * 2 ^ 59
def prefixEnd_2708638 : Nat := 4983230072969 + 3 ^ 40 * 2708638 * 2
def baseEnd_2708638 : Nat := 1390833213033078675068207

theorem tailTrace_2708638 : CollatzResearch.WordTrace tailWord_2708638 prefixEnd_2708638 1390833213033078675068207 := by
  unfold tailWord_2708638
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349017995134324923269821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65861429307383066257439045 12349017995134324923269821)
  ·
    refine ⟨4630881748175371846226183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12349017995134324923269821 4630881748175371846226183)
    ·
      refine ⟨6946322622263057769339275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4630881748175371846226183 6946322622263057769339275)
      ·
        refine ⟨10419483933394586654008913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6946322622263057769339275 10419483933394586654008913)
        ·
          refine ⟨7814612950045939990506685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10419483933394586654008913 7814612950045939990506685)
          ·
            refine ⟨2930479856267227496440007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7814612950045939990506685 2930479856267227496440007)
            ·
              refine ⟨4395719784400841244660011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930479856267227496440007 4395719784400841244660011)
              ·
                refine ⟨6593579676601261866990017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395719784400841244660011 6593579676601261866990017)
                ·
                  refine ⟨4945184757450946400242513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6593579676601261866990017 4945184757450946400242513)
                  ·
                    refine ⟨3708888568088209800181885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945184757450946400242513 3708888568088209800181885)
                    ·
                      refine ⟨1390833213033078675068207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708888568088209800181885 1390833213033078675068207)
                      ·
                        rfl

theorem cell23_2708638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_2708638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708638 prefixEnd_2708638 := by exact prefixLift 2708638
  have htrace : WordTrace (prefixWord ++ tailWord_2708638) baseStart_2708638 baseEnd_2708638 := by
    simpa [prefixWord, tailWord_2708638, baseEnd_2708638] using wordTrace_append hprefix tailTrace_2708638
  have hstable : (prefixWord ++ tailWord_2708638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708638).length < 2 ^ (prefixWord ++ tailWord_2708638).sum := by decide
  have hdescent : baseEnd_2708638 < baseStart_2708638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708668 : List Nat := [2, 2, 2, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_2708668 : Nat := 118140960795 + 2708668 * 2 ^ 59
def prefixEnd_2708668 : Nat := 4983230072969 + 3 ^ 40 * 2708668 * 2
def baseEnd_2708668 : Nat := 1390848617452713557693069

theorem tailTrace_2708668 : CollatzResearch.WordTrace tailWord_2708668 prefixEnd_2708668 1390848617452713557693069 := by
  unfold tailWord_2708668
  simp only [CollatzResearch.WordTrace]
  refine ⟨49396619075482957254875329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65862158767310609673167105 49396619075482957254875329)
  ·
    refine ⟨37047464306612217941156497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49396619075482957254875329 37047464306612217941156497)
    ·
      refine ⟨27785598229959163455867373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37047464306612217941156497 27785598229959163455867373)
      ·
        refine ⟨10419599336234686295950265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27785598229959163455867373 10419599336234686295950265)
        ·
          refine ⟨7814699502176014721962699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10419599336234686295950265 7814699502176014721962699)
          ·
            refine ⟨11722049253264022082944049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814699502176014721962699 11722049253264022082944049)
            ·
              refine ⟨8791536939948016562208037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11722049253264022082944049 8791536939948016562208037)
              ·
                refine ⟨1648413176240253105414007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8791536939948016562208037 1648413176240253105414007)
                ·
                  refine ⟨2472619764360379658121011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648413176240253105414007 2472619764360379658121011)
                  ·
                    refine ⟨3708929646540569487181517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472619764360379658121011 3708929646540569487181517)
                    ·
                      refine ⟨1390848617452713557693069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3708929646540569487181517 1390848617452713557693069)
                      ·
                        rfl

theorem cell23_2708668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_2708668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708668 prefixEnd_2708668 := by exact prefixLift 2708668
  have htrace : WordTrace (prefixWord ++ tailWord_2708668) baseStart_2708668 baseEnd_2708668 := by
    simpa [prefixWord, tailWord_2708668, baseEnd_2708668] using wordTrace_append hprefix tailTrace_2708668
  have hstable : (prefixWord ++ tailWord_2708668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708668).length < 2 ^ (prefixWord ++ tailWord_2708668).sum := by decide
  have hdescent : baseEnd_2708668 < baseStart_2708668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708687 : List Nat := [1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4]
def baseStart_2708687 : Nat := 118140960795 + 2708687 * 2 ^ 59
def prefixEnd_2708687 : Nat := 4983230072969 + 3 ^ 40 * 2708687 * 2
def baseEnd_2708687 : Nat := 1390858373585148983355481

theorem tailTrace_2708687 : CollatzResearch.WordTrace tailWord_2708687 prefixEnd_2708687 1390858373585148983355481 := by
  unfold tailWord_2708687
  simp only [CollatzResearch.WordTrace]
  refine ⟨98793931137897080754692315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65862620758598053836461543 98793931137897080754692315)
  ·
    refine ⟨148190896706845621132038473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98793931137897080754692315 148190896706845621132038473)
    ·
      refine ⟨111143172530134215849028855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148190896706845621132038473 111143172530134215849028855)
      ·
        refine ⟨166714758795201323773543283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111143172530134215849028855 166714758795201323773543283)
        ·
          refine ⟨250072138192801985660314925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166714758795201323773543283 250072138192801985660314925)
          ·
            refine ⟨93777051822300744622618097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250072138192801985660314925 93777051822300744622618097)
            ·
              refine ⟨70332788866725558466963573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93777051822300744622618097 70332788866725558466963573)
              ·
                refine ⟨6593698956255521106277835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70332788866725558466963573 6593698956255521106277835)
                ·
                  refine ⟨9890548434383281659416753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593698956255521106277835 9890548434383281659416753)
                  ·
                    refine ⟨7417911325787461244562565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9890548434383281659416753 7417911325787461244562565)
                    ·
                      refine ⟨1390858373585148983355481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7417911325787461244562565 1390858373585148983355481)
                      ·
                        rfl

theorem cell23_2708687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_2708687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708687 prefixEnd_2708687 := by exact prefixLift 2708687
  have htrace : WordTrace (prefixWord ++ tailWord_2708687) baseStart_2708687 baseEnd_2708687 := by
    simpa [prefixWord, tailWord_2708687, baseEnd_2708687] using wordTrace_append hprefix tailTrace_2708687
  have hstable : (prefixWord ++ tailWord_2708687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708687).length < 2 ^ (prefixWord ++ tailWord_2708687).sum := by decide
  have hdescent : baseEnd_2708687 < baseStart_2708687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708711 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_2708711 : Nat := 118140960795 + 2708711 * 2 ^ 59
def prefixEnd_2708711 : Nat := 4983230072969 + 3 ^ 40 * 2708711 * 2
def baseEnd_2708711 : Nat := 1390870697120856889455371

theorem tailTrace_2708711 : CollatzResearch.WordTrace tailWord_2708711 prefixEnd_2708711 1390870697120856889455371 := by
  unfold tailWord_2708711
  simp only [CollatzResearch.WordTrace]
  refine ⟨98794806489810132853565987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65863204326540088569043991 98794806489810132853565987)
  ·
    refine ⟨148192209734715199280348981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98794806489810132853565987 148192209734715199280348981)
    ·
      refine ⟨13893019662629549932532717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148192209734715199280348981 13893019662629549932532717)
      ·
        refine ⟨5209882373486081224699769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13893019662629549932532717 5209882373486081224699769)
        ·
          refine ⟨3907411780114560918524827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5209882373486081224699769 3907411780114560918524827)
          ·
            refine ⟨5861117670171841377787241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907411780114560918524827 5861117670171841377787241)
            ·
              refine ⟨4395838252628881033340431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861117670171841377787241 4395838252628881033340431)
              ·
                refine ⟨6593757378943321550010647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395838252628881033340431 6593757378943321550010647)
                ·
                  refine ⟨9890636068414982325015971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593757378943321550010647 9890636068414982325015971)
                  ·
                    refine ⟨14835954102622473487523957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9890636068414982325015971 14835954102622473487523957)
                    ·
                      refine ⟨1390870697120856889455371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14835954102622473487523957 1390870697120856889455371)
                      ·
                        rfl

theorem cell23_2708711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_2708711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708711 prefixEnd_2708711 := by exact prefixLift 2708711
  have htrace : WordTrace (prefixWord ++ tailWord_2708711) baseStart_2708711 baseEnd_2708711 := by
    simpa [prefixWord, tailWord_2708711, baseEnd_2708711] using wordTrace_append hprefix tailTrace_2708711
  have hstable : (prefixWord ++ tailWord_2708711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708711).length < 2 ^ (prefixWord ++ tailWord_2708711).sum := by decide
  have hdescent : baseEnd_2708711 < baseStart_2708711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708741 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_2708741 : Nat := 118140960795 + 2708741 * 2 ^ 59
def prefixEnd_2708741 : Nat := 4983230072969 + 3 ^ 40 * 2708741 * 2
def baseEnd_2708741 : Nat := 1390886101540491772080233

theorem tailTrace_2708741 : CollatzResearch.WordTrace tailWord_2708741 prefixEnd_2708741 1390886101540491772080233 := by
  unfold tailWord_2708741
  simp only [CollatzResearch.WordTrace]
  refine ⟨98795900679701447977158077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65863933786467631984772051 98795900679701447977158077)
  ·
    refine ⟨37048462754888042991434279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98795900679701447977158077 37048462754888042991434279)
    ·
      refine ⟨55572694132332064487151419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37048462754888042991434279 55572694132332064487151419)
      ·
        refine ⟨83359041198498096730727129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55572694132332064487151419 83359041198498096730727129)
        ·
          refine ⟨62519280898873572548045347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83359041198498096730727129 62519280898873572548045347)
          ·
            refine ⟨93778921348310358822068021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62519280898873572548045347 93778921348310358822068021)
            ·
              refine ⟨8791773876404096139568877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93778921348310358822068021 8791773876404096139568877)
              ·
                refine ⟨3296915203651536052338329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8791773876404096139568877 3296915203651536052338329)
                ·
                  refine ⟨2472686402738652039253747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3296915203651536052338329 2472686402738652039253747)
                  ·
                    refine ⟨3709029604107978058880621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472686402738652039253747 3709029604107978058880621)
                    ·
                      refine ⟨1390886101540491772080233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709029604107978058880621 1390886101540491772080233)
                      ·
                        rfl

theorem cell23_2708741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_2708741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708741 prefixEnd_2708741 := by exact prefixLift 2708741
  have htrace : WordTrace (prefixWord ++ tailWord_2708741) baseStart_2708741 baseEnd_2708741 := by
    simpa [prefixWord, tailWord_2708741, baseEnd_2708741] using wordTrace_append hprefix tailTrace_2708741
  have hstable : (prefixWord ++ tailWord_2708741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708741).length < 2 ^ (prefixWord ++ tailWord_2708741).sum := by decide
  have hdescent : baseEnd_2708741 < baseStart_2708741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708757 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2708757 : Nat := 118140960795 + 2708757 * 2 ^ 59
def prefixEnd_2708757 : Nat := 4983230072969 + 3 ^ 40 * 2708757 * 2
def baseEnd_2708757 : Nat := 463631439076987903160053

theorem tailTrace_2708757 : CollatzResearch.WordTrace tailWord_2708757 prefixEnd_2708757 463631439076987903160053 := by
  unfold tailWord_2708757
  simp only [CollatzResearch.WordTrace]
  refine ⟨98796484247643482709740525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65864322831762321806493683 98796484247643482709740525)
  ·
    refine ⟨37048681592866306016152697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98796484247643482709740525 37048681592866306016152697)
    ·
      refine ⟨27786511194649729512114523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37048681592866306016152697 27786511194649729512114523)
      ·
        refine ⟨41679766791974594268171785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27786511194649729512114523 41679766791974594268171785)
        ·
          refine ⟨31259825093980945701128839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41679766791974594268171785 31259825093980945701128839)
          ·
            refine ⟨46889737640971418551693259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31259825093980945701128839 46889737640971418551693259)
            ·
              refine ⟨70334606461457127827539889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46889737640971418551693259 70334606461457127827539889)
              ·
                refine ⟨52750954846092845870654917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70334606461457127827539889 52750954846092845870654917)
                ·
                  refine ⟨9890804033642408600747797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52750954846092845870654917 9890804033642408600747797)
                  ·
                    refine ⟨463631439076987903160053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9890804033642408600747797 463631439076987903160053)
                    ·
                      rfl

theorem cell23_2708757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2708757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708757 prefixEnd_2708757 := by exact prefixLift 2708757
  have htrace : WordTrace (prefixWord ++ tailWord_2708757) baseStart_2708757 baseEnd_2708757 := by
    simpa [prefixWord, tailWord_2708757, baseEnd_2708757] using wordTrace_append hprefix tailTrace_2708757
  have hstable : (prefixWord ++ tailWord_2708757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708757).length < 2 ^ (prefixWord ++ tailWord_2708757).sum := by decide
  have hdescent : baseEnd_2708757 < baseStart_2708757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708781 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_2708781 : Nat := 118140960795 + 2708781 * 2 ^ 59
def prefixEnd_2708781 : Nat := 4983230072969 + 3 ^ 40 * 2708781 * 2
def baseEnd_2708781 : Nat := 1390906640766671615580049

theorem tailTrace_2708781 : CollatzResearch.WordTrace tailWord_2708781 prefixEnd_2708781 1390906640766671615580049 := by
  unfold tailWord_2708781
  simp only [CollatzResearch.WordTrace]
  refine ⟨98797359599556534808614197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65864906399704356539076131 98797359599556534808614197)
  ·
    refine ⟨9262252462458425138307581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 98797359599556534808614197 9262252462458425138307581)
    ·
      refine ⟨3473344673421909426865343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9262252462458425138307581 3473344673421909426865343)
      ·
        refine ⟨5210017010132864140298015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473344673421909426865343 5210017010132864140298015)
        ·
          refine ⟨7815025515199296210447023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210017010132864140298015 7815025515199296210447023)
          ·
            refine ⟨11722538272798944315670535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815025515199296210447023 11722538272798944315670535)
            ·
              refine ⟨17583807409198416473505803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11722538272798944315670535 17583807409198416473505803)
              ·
                refine ⟨26375711113797624710258705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17583807409198416473505803 26375711113797624710258705)
                ·
                  refine ⟨19781783335348218532694029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26375711113797624710258705 19781783335348218532694029)
                  ·
                    refine ⟨7418168750755581949760261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19781783335348218532694029 7418168750755581949760261)
                    ·
                      refine ⟨1390906640766671615580049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7418168750755581949760261 1390906640766671615580049)
                      ·
                        rfl

theorem cell23_2708781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_2708781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708781 prefixEnd_2708781 := by exact prefixLift 2708781
  have htrace : WordTrace (prefixWord ++ tailWord_2708781) baseStart_2708781 baseEnd_2708781 := by
    simpa [prefixWord, tailWord_2708781, baseEnd_2708781] using wordTrace_append hprefix tailTrace_2708781
  have hstable : (prefixWord ++ tailWord_2708781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708781).length < 2 ^ (prefixWord ++ tailWord_2708781).sum := by decide
  have hdescent : baseEnd_2708781 < baseStart_2708781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708794 : List Nat := [3, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_2708794 : Nat := 118140960795 + 2708794 * 2 ^ 59
def prefixEnd_2708794 : Nat := 4983230072969 + 3 ^ 40 * 2708794 * 2
def baseEnd_2708794 : Nat := 1390913316015180064717489

theorem tailTrace_2708794 : CollatzResearch.WordTrace tailWord_2708794 prefixEnd_2708794 1390913316015180064717489 := by
  unfold tailWord_2708794
  simp only [CollatzResearch.WordTrace]
  refine ⟨24699458437127359507209359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65865222499006292019224957 24699458437127359507209359)
  ·
    refine ⟨37049187655691039260814039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24699458437127359507209359 37049187655691039260814039)
    ·
      refine ⟨55573781483536558891221059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37049187655691039260814039 55573781483536558891221059)
      ·
        refine ⟨83360672225304838336831589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55573781483536558891221059 83360672225304838336831589)
        ·
          refine ⟨15630126042244657188155923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83360672225304838336831589 15630126042244657188155923)
          ·
            refine ⟨23445189063366985782233885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15630126042244657188155923 23445189063366985782233885)
            ·
              refine ⟨8791945898762619668337707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23445189063366985782233885 8791945898762619668337707)
              ·
                refine ⟨13187918848143929502506561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8791945898762619668337707 13187918848143929502506561)
                ·
                  refine ⟨9890939136107947126879921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13187918848143929502506561 9890939136107947126879921)
                  ·
                    refine ⟨7418204352080960345159941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9890939136107947126879921 7418204352080960345159941)
                    ·
                      refine ⟨1390913316015180064717489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7418204352080960345159941 1390913316015180064717489)
                      ·
                        rfl

theorem cell23_2708794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_2708794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708794 prefixEnd_2708794 := by exact prefixLift 2708794
  have htrace : WordTrace (prefixWord ++ tailWord_2708794) baseStart_2708794 baseEnd_2708794 := by
    simpa [prefixWord, tailWord_2708794, baseEnd_2708794] using wordTrace_append hprefix tailTrace_2708794
  have hstable : (prefixWord ++ tailWord_2708794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708794).length < 2 ^ (prefixWord ++ tailWord_2708794).sum := by decide
  have hdescent : baseEnd_2708794 < baseStart_2708794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708798 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_2708798 : Nat := 118140960795 + 2708798 * 2 ^ 59
def prefixEnd_2708798 : Nat := 4983230072969 + 3 ^ 40 * 2708798 * 2
def baseEnd_2708798 : Nat := 1390915369937798049067471

theorem tailTrace_2708798 : CollatzResearch.WordTrace tailWord_2708798 prefixEnd_2708798 1390915369937798049067471 := by
  unfold tailWord_2708798
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349747455061868338997881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65865319760329964474655365 12349747455061868338997881)
  ·
    refine ⟨9262310591296401254248411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12349747455061868338997881 9262310591296401254248411)
    ·
      refine ⟨13893465886944601881372617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262310591296401254248411 13893465886944601881372617)
      ·
        refine ⟨10420099415208451411029463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13893465886944601881372617 10420099415208451411029463)
        ·
          refine ⟨15630149122812677116544195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10420099415208451411029463 15630149122812677116544195)
          ·
            refine ⟨23445223684219015674816293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15630149122812677116544195 23445223684219015674816293)
            ·
              refine ⟨4395979440791065439028055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23445223684219015674816293 4395979440791065439028055)
              ·
                refine ⟨6593969161186598158542083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4395979440791065439028055 6593969161186598158542083)
                ·
                  refine ⟨9890953741779897237813125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6593969161186598158542083 9890953741779897237813125)
                  ·
                    refine ⟨1854553826583730732089961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9890953741779897237813125 1854553826583730732089961)
                    ·
                      refine ⟨1390915369937798049067471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854553826583730732089961 1390915369937798049067471)
                      ·
                        rfl

theorem cell23_2708798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_2708798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708798 prefixEnd_2708798 := by exact prefixLift 2708798
  have htrace : WordTrace (prefixWord ++ tailWord_2708798) baseStart_2708798 baseEnd_2708798 := by
    simpa [prefixWord, tailWord_2708798, baseEnd_2708798] using wordTrace_append hprefix tailTrace_2708798
  have hstable : (prefixWord ++ tailWord_2708798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708798).length < 2 ^ (prefixWord ++ tailWord_2708798).sum := by decide
  have hdescent : baseEnd_2708798 < baseStart_2708798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708814 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3]
def baseStart_2708814 : Nat := 118140960795 + 2708814 * 2 ^ 59
def prefixEnd_2708814 : Nat := 4983230072969 + 3 ^ 40 * 2708814 * 2
def baseEnd_2708814 : Nat := 1390923585628269986467397

theorem tailTrace_2708814 : CollatzResearch.WordTrace tailWord_2708814 prefixEnd_2708814 1390923585628269986467397 := by
  unfold tailWord_2708814
  simp only [CollatzResearch.WordTrace]
  refine ⟨12349820401054622680570687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65865708805624654296376997 12349820401054622680570687)
  ·
    refine ⟨18524730601581934020856031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12349820401054622680570687 18524730601581934020856031)
    ·
      refine ⟨27787095902372901031284047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18524730601581934020856031 27787095902372901031284047)
      ·
        refine ⟨41680643853559351546926071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27787095902372901031284047 41680643853559351546926071)
        ·
          refine ⟨62520965780339027320389107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41680643853559351546926071 62520965780339027320389107)
          ·
            refine ⟨93781448670508540980583661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62520965780339027320389107 93781448670508540980583661)
            ·
              refine ⟨35168043251440702867718873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93781448670508540980583661 35168043251440702867718873)
              ·
                refine ⟨26376032438580527150789155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35168043251440702867718873 26376032438580527150789155)
                ·
                  refine ⟨39564048657870790726183733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26376032438580527150789155 39564048657870790726183733)
                  ·
                    refine ⟨3709129561675386630579725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39564048657870790726183733 3709129561675386630579725)
                    ·
                      refine ⟨1390923585628269986467397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709129561675386630579725 1390923585628269986467397)
                      ·
                        rfl

theorem cell23_2708814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_2708814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708814 prefixEnd_2708814 := by exact prefixLift 2708814
  have htrace : WordTrace (prefixWord ++ tailWord_2708814) baseStart_2708814 baseEnd_2708814 := by
    simpa [prefixWord, tailWord_2708814, baseEnd_2708814] using wordTrace_append hprefix tailTrace_2708814
  have hstable : (prefixWord ++ tailWord_2708814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708814).length < 2 ^ (prefixWord ++ tailWord_2708814).sum := by decide
  have hdescent : baseEnd_2708814 < baseStart_2708814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708821 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 5]
def baseStart_2708821 : Nat := 118140960795 + 2708821 * 2 ^ 59
def prefixEnd_2708821 : Nat := 4983230072969 + 3 ^ 40 * 2708821 * 2
def baseEnd_2708821 : Nat := 154547464443650162119985

theorem tailTrace_2708821 : CollatzResearch.WordTrace tailWord_2708821 prefixEnd_2708821 154547464443650162119985 := by
  unfold tailWord_2708821
  simp only [CollatzResearch.WordTrace]
  refine ⟨98798818519411621640070317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65865879012941081093380211 98798818519411621640070317)
  ·
    refine ⟨37049556944779358115026369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98798818519411621640070317 37049556944779358115026369)
    ·
      refine ⟨27787167708584518586269777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37049556944779358115026369 27787167708584518586269777)
      ·
        refine ⟨20840375781438388939702333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27787167708584518586269777 20840375781438388939702333)
        ·
          refine ⟨7815140918039395852388375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20840375781438388939702333 7815140918039395852388375)
          ·
            refine ⟨11722711377059093778582563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815140918039395852388375 11722711377059093778582563)
            ·
              refine ⟨17584067065588640667873845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11722711377059093778582563 17584067065588640667873845)
              ·
                refine ⟨1648506287398935062613173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17584067065588640667873845 1648506287398935062613173)
                ·
                  refine ⟨154547464443650162119985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1648506287398935062613173 154547464443650162119985)
                  ·
                    rfl

theorem cell23_2708821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_2708821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708821 prefixEnd_2708821 := by exact prefixLift 2708821
  have htrace : WordTrace (prefixWord ++ tailWord_2708821) baseStart_2708821 baseEnd_2708821 := by
    simpa [prefixWord, tailWord_2708821, baseEnd_2708821] using wordTrace_append hprefix tailTrace_2708821
  have hstable : (prefixWord ++ tailWord_2708821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708821).length < 2 ^ (prefixWord ++ tailWord_2708821).sum := by decide
  have hdescent : baseEnd_2708821 < baseStart_2708821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708888 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_2708888 : Nat := 118140960795 + 2708888 * 2 ^ 59
def prefixEnd_2708888 : Nat := 4983230072969 + 3 ^ 40 * 2708888 * 2
def baseEnd_2708888 : Nat := 1390961583196702696942057

theorem tailTrace_2708888 : CollatzResearch.WordTrace tailWord_2708888 prefixEnd_2708888 1390961583196702696942057 := by
  unfold tailWord_2708888
  simp only [CollatzResearch.WordTrace]
  refine ⟨49400631105084446041379659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65867508140112594721839545 49400631105084446041379659)
  ·
    refine ⟨74100946657626669062069489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49400631105084446041379659 74100946657626669062069489)
    ·
      refine ⟨55575709993220001796552117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74100946657626669062069489 55575709993220001796552117)
      ·
        refine ⟨5210222811864375168426761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55575709993220001796552117 5210222811864375168426761)
        ·
          refine ⟨3907667108898281376320071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5210222811864375168426761 3907667108898281376320071)
          ·
            refine ⟨5861500663347422064480107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907667108898281376320071 5861500663347422064480107)
            ·
              refine ⟨8792250995021133096720161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861500663347422064480107 8792250995021133096720161)
              ·
                refine ⟨6594188246265849822540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792250995021133096720161 6594188246265849822540121)
                ·
                  refine ⟨4945641184699387366905091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6594188246265849822540121 4945641184699387366905091)
                  ·
                    refine ⟨7418461777049081050357637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945641184699387366905091 7418461777049081050357637)
                    ·
                      refine ⟨1390961583196702696942057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7418461777049081050357637 1390961583196702696942057)
                      ·
                        rfl

theorem cell23_2708888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_2708888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708888 prefixEnd_2708888 := by exact prefixLift 2708888
  have htrace : WordTrace (prefixWord ++ tailWord_2708888) baseStart_2708888 baseEnd_2708888 := by
    simpa [prefixWord, tailWord_2708888, baseEnd_2708888] using wordTrace_append hprefix tailTrace_2708888
  have hstable : (prefixWord ++ tailWord_2708888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708888).length < 2 ^ (prefixWord ++ tailWord_2708888).sum := by decide
  have hdescent : baseEnd_2708888 < baseStart_2708888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708898 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2708898 : Nat := 118140960795 + 2708898 * 2 ^ 59
def prefixEnd_2708898 : Nat := 4983230072969 + 3 ^ 40 * 2708898 * 2
def baseEnd_2708898 : Nat := 463655572667749219272337

theorem tailTrace_2708898 : CollatzResearch.WordTrace tailWord_2708898 prefixEnd_2708898 463655572667749219272337 := by
  unfold tailWord_2708898
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700406735033165947655837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65867751293421775860415565 24700406735033165947655837)
  ·
    refine ⟨9262652525637437230370939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24700406735033165947655837 9262652525637437230370939)
    ·
      refine ⟨13893978788456155845556409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262652525637437230370939 13893978788456155845556409)
      ·
        refine ⟨10420484091342116884167307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13893978788456155845556409 10420484091342116884167307)
        ·
          refine ⟨15630726137013175326250961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10420484091342116884167307 15630726137013175326250961)
          ·
            refine ⟨11723044602759881494688221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15630726137013175326250961 11723044602759881494688221)
            ·
              refine ⟨4396141726034955560508083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11723044602759881494688221 4396141726034955560508083)
              ·
                refine ⟨6594212589052433340762125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396141726034955560508083 6594212589052433340762125)
                ·
                  refine ⟨2472829720894662502785797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6594212589052433340762125 2472829720894662502785797)
                  ·
                    refine ⟨463655572667749219272337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2472829720894662502785797 463655572667749219272337)
                    ·
                      rfl

theorem cell23_2708898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2708898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708898 prefixEnd_2708898 := by exact prefixLift 2708898
  have htrace : WordTrace (prefixWord ++ tailWord_2708898) baseStart_2708898 baseEnd_2708898 := by
    simpa [prefixWord, tailWord_2708898, baseEnd_2708898] using wordTrace_append hprefix tailTrace_2708898
  have hstable : (prefixWord ++ tailWord_2708898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708898).length < 2 ^ (prefixWord ++ tailWord_2708898).sum := by decide
  have hdescent : baseEnd_2708898 < baseStart_2708898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708931 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 5, 2]
def baseStart_2708931 : Nat := 118140960795 + 2708931 * 2 ^ 59
def prefixEnd_2708931 : Nat := 4983230072969 + 3 ^ 40 * 2708931 * 2
def baseEnd_2708931 : Nat := 1390983662864846028704359

theorem tailTrace_2708931 : CollatzResearch.WordTrace tailWord_2708931 prefixEnd_2708931 1390983662864846028704359 := by
  unfold tailWord_2708931
  simp only [CollatzResearch.WordTrace]
  refine ⟨98802830549013110426574647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65868553699342073617716431 98802830549013110426574647)
  ·
    refine ⟨148204245823519665639861971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98802830549013110426574647 148204245823519665639861971)
    ·
      refine ⟨222306368735279498459792957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148204245823519665639861971 222306368735279498459792957)
      ·
        refine ⟨83364888275729811922422359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222306368735279498459792957 83364888275729811922422359)
        ·
          refine ⟨125047332413594717883633539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83364888275729811922422359 125047332413594717883633539)
          ·
            refine ⟨187570998620392076825450309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125047332413594717883633539 187570998620392076825450309)
            ·
              refine ⟨35169562241323514404771933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187570998620392076825450309 35169562241323514404771933)
              ·
                refine ⟨13188585840496317901789475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35169562241323514404771933 13188585840496317901789475)
                ·
                  refine ⟨19782878760744476852684213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13188585840496317901789475 19782878760744476852684213)
                  ·
                    refine ⟨1854644883819794704939145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19782878760744476852684213 1854644883819794704939145)
                    ·
                      refine ⟨1390983662864846028704359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854644883819794704939145 1390983662864846028704359)
                      ·
                        rfl

theorem cell23_2708931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_2708931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708931 prefixEnd_2708931 := by exact prefixLift 2708931
  have htrace : WordTrace (prefixWord ++ tailWord_2708931) baseStart_2708931 baseEnd_2708931 := by
    simpa [prefixWord, tailWord_2708931, baseEnd_2708931] using wordTrace_append hprefix tailTrace_2708931
  have hstable : (prefixWord ++ tailWord_2708931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708931).length < 2 ^ (prefixWord ++ tailWord_2708931).sum := by decide
  have hdescent : baseEnd_2708931 < baseStart_2708931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708961 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2708961 : Nat := 118140960795 + 2708961 * 2 ^ 59
def prefixEnd_2708961 : Nat := 4983230072969 + 3 ^ 40 * 2708961 * 2
def baseEnd_2708961 : Nat := 1390999067284480911329221

theorem tailTrace_2708961 : CollatzResearch.WordTrace tailWord_2708961 prefixEnd_2708961 1390999067284480911329221 := by
  unfold tailWord_2708961
  simp only [CollatzResearch.WordTrace]
  refine ⟨98803924738904425550166737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65869283159269617033444491 98803924738904425550166737)
  ·
    refine ⟨74102943554178319162625053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98803924738904425550166737 74102943554178319162625053)
    ·
      refine ⟨27788603832816869685984395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74102943554178319162625053 27788603832816869685984395)
      ·
        refine ⟨41682905749225304528976593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27788603832816869685984395 41682905749225304528976593)
        ·
          refine ⟨31262179311918978396732445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41682905749225304528976593 31262179311918978396732445)
          ·
            refine ⟨11723317241969616898774667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31262179311918978396732445 11723317241969616898774667)
            ·
              refine ⟨17584975862954425348162001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11723317241969616898774667 17584975862954425348162001)
              ·
                refine ⟨13188731897215819011121501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17584975862954425348162001 13188731897215819011121501)
                ·
                  refine ⟨4945774461455932129170563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13188731897215819011121501 4945774461455932129170563)
                  ·
                    refine ⟨7418661692183898193755845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945774461455932129170563 7418661692183898193755845)
                    ·
                      refine ⟨1390999067284480911329221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7418661692183898193755845 1390999067284480911329221)
                      ·
                        rfl

theorem cell23_2708961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2708961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708961 prefixEnd_2708961 := by exact prefixLift 2708961
  have htrace : WordTrace (prefixWord ++ tailWord_2708961) baseStart_2708961 baseEnd_2708961 := by
    simpa [prefixWord, tailWord_2708961, baseEnd_2708961] using wordTrace_append hprefix tailTrace_2708961
  have hstable : (prefixWord ++ tailWord_2708961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708961).length < 2 ^ (prefixWord ++ tailWord_2708961).sum := by decide
  have hdescent : baseEnd_2708961 < baseStart_2708961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708978 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2708978 : Nat := 118140960795 + 2708978 * 2 ^ 59
def prefixEnd_2708978 : Nat := 4983230072969 + 3 ^ 40 * 2708978 * 2
def baseEnd_2708978 : Nat := 1391007796455607344816643

theorem tailTrace_2708978 : CollatzResearch.WordTrace tailWord_2708978 prefixEnd_2708978 1391007796455607344816643 := by
  unfold tailWord_2708978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24701136194960709363383897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65869696519895224969023725 24701136194960709363383897)
  ·
    refine ⟨18525852146220532022537923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24701136194960709363383897 18525852146220532022537923)
    ·
      refine ⟨27788778219330798033806885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18525852146220532022537923 27788778219330798033806885)
      ·
        refine ⟨5210395916124524631338791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27788778219330798033806885 5210395916124524631338791)
        ·
          refine ⟨7815593874186786947008187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210395916124524631338791 7815593874186786947008187)
          ·
            refine ⟨11723390811280180420512281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815593874186786947008187 11723390811280180420512281)
            ·
              refine ⟨8792543108460135315384211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11723390811280180420512281 8792543108460135315384211)
              ·
                refine ⟨13188814662690202973076317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8792543108460135315384211 13188814662690202973076317)
                ·
                  refine ⟨4945805498508826114903619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13188814662690202973076317 4945805498508826114903619)
                  ·
                    refine ⟨7418708247763239172355429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4945805498508826114903619 7418708247763239172355429)
                    ·
                      refine ⟨1391007796455607344816643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7418708247763239172355429 1391007796455607344816643)
                      ·
                        rfl

theorem cell23_2708978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2708978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708978 prefixEnd_2708978 := by exact prefixLift 2708978
  have htrace : WordTrace (prefixWord ++ tailWord_2708978) baseStart_2708978 baseEnd_2708978 := by
    simpa [prefixWord, tailWord_2708978, baseEnd_2708978] using wordTrace_append hprefix tailTrace_2708978
  have hstable : (prefixWord ++ tailWord_2708978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708978).length < 2 ^ (prefixWord ++ tailWord_2708978).sum := by decide
  have hdescent : baseEnd_2708978 < baseStart_2708978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2708982 : List Nat := [5, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2708982 : Nat := 118140960795 + 2708982 * 2 ^ 59
def prefixEnd_2708982 : Nat := 4983230072969 + 3 ^ 40 * 2708982 * 2
def baseEnd_2708982 : Nat := 1391009850378225329166625

theorem tailTrace_2708982 : CollatzResearch.WordTrace tailWord_2708982 prefixEnd_2708982 1391009850378225329166625 := by
  unfold tailWord_2708982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175293166989271633542575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65869793781218897424454133 6175293166989271633542575)
  ·
    refine ⟨9262939750483907450313863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6175293166989271633542575 9262939750483907450313863)
    ·
      refine ⟨13894409625725861175470795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262939750483907450313863 13894409625725861175470795)
      ·
        refine ⟨20841614438588791763206193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13894409625725861175470795 20841614438588791763206193)
        ·
          refine ⟨15631210828941593822404645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20841614438588791763206193 15631210828941593822404645)
          ·
            refine ⟨2930852030426548841700871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15631210828941593822404645 2930852030426548841700871)
            ·
              refine ⟨4396278045639823262551307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2930852030426548841700871 4396278045639823262551307)
              ·
                refine ⟨6594417068459734893826961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396278045639823262551307 6594417068459734893826961)
                ·
                  refine ⟨4945812801344801170370221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6594417068459734893826961 4945812801344801170370221)
                  ·
                    refine ⟨1854679800504300438888833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4945812801344801170370221 1854679800504300438888833)
                    ·
                      refine ⟨1391009850378225329166625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854679800504300438888833 1391009850378225329166625)
                      ·
                        rfl

theorem cell23_2708982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2708982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2708982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2708982 prefixEnd_2708982 := by exact prefixLift 2708982
  have htrace : WordTrace (prefixWord ++ tailWord_2708982) baseStart_2708982 baseEnd_2708982 := by
    simpa [prefixWord, tailWord_2708982, baseEnd_2708982] using wordTrace_append hprefix tailTrace_2708982
  have hstable : (prefixWord ++ tailWord_2708982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2708982).length < 2 ^ (prefixWord ++ tailWord_2708982).sum := by decide
  have hdescent : baseEnd_2708982 < baseStart_2708982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2708982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709032 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2709032 : Nat := 118140960795 + 2709032 * 2 ^ 59
def prefixEnd_2709032 : Nat := 4983230072969 + 3 ^ 40 * 2709032 * 2
def baseEnd_2709032 : Nat := 1391035524410950133541395

theorem tailTrace_2709032 : CollatzResearch.WordTrace tailWord_2709032 prefixEnd_2709032 1391035524410950133541395 := by
  unfold tailWord_2709032
  simp only [CollatzResearch.WordTrace]
  refine ⟨49403257160823602338000675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65871009547764803117334233 49403257160823602338000675)
  ·
    refine ⟨74104885741235403507001013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49403257160823602338000675 74104885741235403507001013)
    ·
      refine ⟨6947333038240819078781345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74104885741235403507001013 6947333038240819078781345)
      ·
        refine ⟨5210499778680614309086009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6947333038240819078781345 5210499778680614309086009)
        ·
          refine ⟨3907874834010460731814507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5210499778680614309086009 3907874834010460731814507)
          ·
            refine ⟨5861812251015691097721761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907874834010460731814507 5861812251015691097721761)
            ·
              refine ⟨4396359188261768323291321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5861812251015691097721761 4396359188261768323291321)
              ·
                refine ⟨3297269391196326242468491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396359188261768323291321 3297269391196326242468491)
                ·
                  refine ⟨4945904086794489363702737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297269391196326242468491 4945904086794489363702737)
                  ·
                    refine ⟨3709428065095867022777053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4945904086794489363702737 3709428065095867022777053)
                    ·
                      refine ⟨1391035524410950133541395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709428065095867022777053 1391035524410950133541395)
                      ·
                        rfl

theorem cell23_2709032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2709032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709032 prefixEnd_2709032 := by exact prefixLift 2709032
  have htrace : WordTrace (prefixWord ++ tailWord_2709032) baseStart_2709032 baseEnd_2709032 := by
    simpa [prefixWord, tailWord_2709032, baseEnd_2709032] using wordTrace_append hprefix tailTrace_2709032
  have hstable : (prefixWord ++ tailWord_2709032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709032).length < 2 ^ (prefixWord ++ tailWord_2709032).sum := by decide
  have hdescent : baseEnd_2709032 < baseStart_2709032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709055 : List Nat := [1, 1, 2, 2, 3, 3, 2, 3, 1, 3, 2]
def baseStart_2709055 : Nat := 118140960795 + 2709055 * 2 ^ 59
def prefixEnd_2709055 : Nat := 4983230072969 + 3 ^ 40 * 2709055 * 2
def baseEnd_2709055 : Nat := 1391047334466003543553789

theorem tailTrace_2709055 : CollatzResearch.WordTrace tailWord_2709055 prefixEnd_2709055 1391047334466003543553789 := by
  unfold tailWord_2709055
  simp only [CollatzResearch.WordTrace]
  refine ⟨98807353200563879604088619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65871568800375919736059079 98807353200563879604088619)
  ·
    refine ⟨148211029800845819406132929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98807353200563879604088619 148211029800845819406132929)
    ·
      refine ⟨111158272350634364554599697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148211029800845819406132929 111158272350634364554599697)
      ·
        refine ⟨83368704262975773415949773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111158272350634364554599697 83368704262975773415949773)
        ·
          refine ⟨31263264098615915030981165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83368704262975773415949773 31263264098615915030981165)
          ·
            refine ⟨11723724036980968136617937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31263264098615915030981165 11723724036980968136617937)
            ·
              refine ⟨8792793027735726102463453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11723724036980968136617937 8792793027735726102463453)
              ·
                refine ⟨3297297385400897288423795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8792793027735726102463453 3297297385400897288423795)
                ·
                  refine ⟨4945946078101345932635693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3297297385400897288423795 4945946078101345932635693)
                  ·
                    refine ⟨1854729779288004724738385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4945946078101345932635693 1854729779288004724738385)
                    ·
                      refine ⟨1391047334466003543553789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854729779288004724738385 1391047334466003543553789)
                      ·
                        rfl

theorem cell23_2709055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_2709055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709055 prefixEnd_2709055 := by exact prefixLift 2709055
  have htrace : WordTrace (prefixWord ++ tailWord_2709055) baseStart_2709055 baseEnd_2709055 := by
    simpa [prefixWord, tailWord_2709055, baseEnd_2709055] using wordTrace_append hprefix tailTrace_2709055
  have hstable : (prefixWord ++ tailWord_2709055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709055).length < 2 ^ (prefixWord ++ tailWord_2709055).sum := by decide
  have hdescent : baseEnd_2709055 < baseStart_2709055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709071 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3]
def baseStart_2709071 : Nat := 118140960795 + 2709071 * 2 ^ 59
def prefixEnd_2709071 : Nat := 4983230072969 + 3 ^ 40 * 2709071 * 2
def baseEnd_2709071 : Nat := 1391055550156475480953715

theorem tailTrace_2709071 : CollatzResearch.WordTrace tailWord_2709071 prefixEnd_2709071 1391055550156475480953715 := by
  unfold tailWord_2709071
  simp only [CollatzResearch.WordTrace]
  refine ⟨98807936768505914336671067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65871957845670609557780711 98807936768505914336671067)
  ·
    refine ⟨148211905152758871505006601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98807936768505914336671067 148211905152758871505006601)
    ·
      refine ⟨111158928864569153628754951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148211905152758871505006601 111158928864569153628754951)
      ·
        refine ⟨166738393296853730443132427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111158928864569153628754951 166738393296853730443132427)
        ·
          refine ⟨250107589945280595664698641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166738393296853730443132427 250107589945280595664698641)
          ·
            refine ⟨187580692458960446748523981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250107589945280595664698641 187580692458960446748523981)
            ·
              refine ⟨70342759672110167530696493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187580692458960446748523981 70342759672110167530696493)
              ·
                refine ⟨26378534877041312824011185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70342759672110167530696493 26378534877041312824011185)
                ·
                  refine ⟨19783901157780984618008389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26378534877041312824011185 19783901157780984618008389)
                  ·
                    refine ⟨3709481467083934615876573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19783901157780984618008389 3709481467083934615876573)
                    ·
                      refine ⟨1391055550156475480953715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709481467083934615876573 1391055550156475480953715)
                      ·
                        rfl

theorem cell23_2709071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_2709071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709071 prefixEnd_2709071 := by exact prefixLift 2709071
  have htrace : WordTrace (prefixWord ++ tailWord_2709071) baseStart_2709071 baseEnd_2709071 := by
    simpa [prefixWord, tailWord_2709071, baseEnd_2709071] using wordTrace_append hprefix tailTrace_2709071
  have hstable : (prefixWord ++ tailWord_2709071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709071).length < 2 ^ (prefixWord ++ tailWord_2709071).sum := by decide
  have hdescent : baseEnd_2709071 < baseStart_2709071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709081 : List Nat := [1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_2709081 : Nat := 118140960795 + 2709081 * 2 ^ 59
def prefixEnd_2709081 : Nat := 4983230072969 + 3 ^ 40 * 2709081 * 2
def baseEnd_2709081 : Nat := 1391060684963020441828669

theorem tailTrace_2709081 : CollatzResearch.WordTrace tailWord_2709081 prefixEnd_2709081 1391060684963020441828669 := by
  unfold tailWord_2709081
  simp only [CollatzResearch.WordTrace]
  refine ⟨98808301498469686044535097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65872200998979790696356731 98808301498469686044535097)
  ·
    refine ⟨74106226123852264533401323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98808301498469686044535097 74106226123852264533401323)
    ·
      refine ⟨111159339185778396800101985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74106226123852264533401323 111159339185778396800101985)
      ·
        refine ⟨83369504389333797600076489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111159339185778396800101985 83369504389333797600076489)
        ·
          refine ⟨62527128292000348200057367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83369504389333797600076489 62527128292000348200057367)
          ·
            refine ⟨93790692438000522300086051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62527128292000348200057367 93790692438000522300086051)
            ·
              refine ⟨140686038657000783450129077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93790692438000522300086051 140686038657000783450129077)
              ·
                refine ⟨13189316124093823448449601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140686038657000783450129077 13189316124093823448449601)
                ·
                  refine ⟨9891987093070367586337201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13189316124093823448449601 9891987093070367586337201)
                  ·
                    refine ⟨7418990319802775689752901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9891987093070367586337201 7418990319802775689752901)
                    ·
                      refine ⟨1391060684963020441828669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7418990319802775689752901 1391060684963020441828669)
                      ·
                        rfl

theorem cell23_2709081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_2709081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709081 prefixEnd_2709081 := by exact prefixLift 2709081
  have htrace : WordTrace (prefixWord ++ tailWord_2709081) baseStart_2709081 baseEnd_2709081 := by
    simpa [prefixWord, tailWord_2709081, baseEnd_2709081] using wordTrace_append hprefix tailTrace_2709081
  have hstable : (prefixWord ++ tailWord_2709081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709081).length < 2 ^ (prefixWord ++ tailWord_2709081).sum := by decide
  have hdescent : baseEnd_2709081 < baseStart_2709081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709102 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2709102 : Nat := 118140960795 + 2709102 * 2 ^ 59
def prefixEnd_2709102 : Nat := 4983230072969 + 3 ^ 40 * 2709102 * 2
def baseEnd_2709102 : Nat := 1391071468056764859666073

theorem tailTrace_2709102 : CollatzResearch.WordTrace tailWord_2709102 prefixEnd_2709102 1391071468056764859666073 := by
  unfold tailWord_2709102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12351133428924200828881195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65872711620929071087366373 12351133428924200828881195)
  ·
    refine ⟨18526700143386301243321793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12351133428924200828881195 18526700143386301243321793)
    ·
      refine ⟨13895025107539725932491345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18526700143386301243321793 13895025107539725932491345)
      ·
        refine ⟨10421268830654794449368509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13895025107539725932491345 10421268830654794449368509)
        ·
          refine ⟨3907975811495547918513191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10421268830654794449368509 3907975811495547918513191)
          ·
            refine ⟨5861963717243321877769787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907975811495547918513191 5861963717243321877769787)
            ·
              refine ⟨8792945575864982816654681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861963717243321877769787 8792945575864982816654681)
              ·
                refine ⟨6594709181898737112491011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8792945575864982816654681 6594709181898737112491011)
                ·
                  refine ⟨9892063772848105668736517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6594709181898737112491011 9892063772848105668736517)
                  ·
                    refine ⟨1854761957409019812888097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9892063772848105668736517 1854761957409019812888097)
                    ·
                      refine ⟨1391071468056764859666073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854761957409019812888097 1391071468056764859666073)
                      ·
                        rfl

theorem cell23_2709102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2709102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709102 prefixEnd_2709102 := by exact prefixLift 2709102
  have htrace : WordTrace (prefixWord ++ tailWord_2709102) baseStart_2709102 baseEnd_2709102 := by
    simpa [prefixWord, tailWord_2709102, baseEnd_2709102] using wordTrace_append hprefix tailTrace_2709102
  have hstable : (prefixWord ++ tailWord_2709102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709102).length < 2 ^ (prefixWord ++ tailWord_2709102).sum := by decide
  have hdescent : baseEnd_2709102 < baseStart_2709102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709131 : List Nat := [1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5]
def baseStart_2709131 : Nat := 118140960795 + 2709131 * 2 ^ 59
def prefixEnd_2709131 : Nat := 4983230072969 + 3 ^ 40 * 2709131 * 2
def baseEnd_2709131 : Nat := 1391086358995745246203439

theorem tailTrace_2709131 : CollatzResearch.WordTrace tailWord_2709131 prefixEnd_2709131 1391086358995745246203439 := by
  unfold tailWord_2709131
  simp only [CollatzResearch.WordTrace]
  refine ⟨98810125148288544583855247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65873416765525696389236831 98810125148288544583855247)
  ·
    refine ⟨148215187722432816875782871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98810125148288544583855247 148215187722432816875782871)
    ·
      refine ⟨222322781583649225313674307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148215187722432816875782871 222322781583649225313674307)
      ·
        refine ⟨333484172375473837970511461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222322781583649225313674307 333484172375473837970511461)
        ·
          refine ⟨62528282320401344619470899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 333484172375473837970511461 62528282320401344619470899)
          ·
            refine ⟨93792423480602016929206349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62528282320401344619470899 93792423480602016929206349)
            ·
              refine ⟨35172158805225756348452381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93792423480602016929206349 35172158805225756348452381)
              ·
                refine ⟨13189559551959658630669643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35172158805225756348452381 13189559551959658630669643)
                ·
                  refine ⟨19784339327939487946004465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13189559551959658630669643 19784339327939487946004465)
                  ·
                    refine ⟨14838254495954615959503349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19784339327939487946004465 14838254495954615959503349)
                    ·
                      refine ⟨1391086358995745246203439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14838254495954615959503349 1391086358995745246203439)
                      ·
                        rfl

theorem cell23_2709131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 2, 5].length) (baseStart_2709131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709131 prefixEnd_2709131 := by exact prefixLift 2709131
  have htrace : WordTrace (prefixWord ++ tailWord_2709131) baseStart_2709131 baseEnd_2709131 := by
    simpa [prefixWord, tailWord_2709131, baseEnd_2709131] using wordTrace_append hprefix tailTrace_2709131
  have hstable : (prefixWord ++ tailWord_2709131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709131).length < 2 ^ (prefixWord ++ tailWord_2709131).sum := by decide
  have hdescent : baseEnd_2709131 < baseStart_2709131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709171 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_2709171 : Nat := 118140960795 + 2709171 * 2 ^ 59
def prefixEnd_2709171 : Nat := 4983230072969 + 3 ^ 40 * 2709171 * 2
def baseEnd_2709171 : Nat := 1391106898221925089703255

theorem tailTrace_2709171 : CollatzResearch.WordTrace tailWord_2709171 prefixEnd_2709171 1391106898221925089703255 := by
  unfold tailWord_2709171
  simp only [CollatzResearch.WordTrace]
  refine ⟨98811584068143631415311367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65874389378762420943540911 98811584068143631415311367)
  ·
    refine ⟨148217376102215447122967051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98811584068143631415311367 148217376102215447122967051)
    ·
      refine ⟨222326064153323170684450577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148217376102215447122967051 222326064153323170684450577)
      ·
        refine ⟨166744548114992378013337933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222326064153323170684450577 166744548114992378013337933)
        ·
          refine ⟨62529205543122141755001725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166744548114992378013337933 62529205543122141755001725)
          ·
            refine ⟨23448452078670803158125647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62529205543122141755001725 23448452078670803158125647)
            ·
              refine ⟨35172678118006204737188471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448452078670803158125647 35172678118006204737188471)
              ·
                refine ⟨52759017177009307105782707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35172678118006204737188471 52759017177009307105782707)
                ·
                  refine ⟨79138525765513960658674061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52759017177009307105782707 79138525765513960658674061)
                  ·
                    refine ⟨29676947162067735247002773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79138525765513960658674061 29676947162067735247002773)
                    ·
                      refine ⟨1391106898221925089703255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29676947162067735247002773 1391106898221925089703255)
                      ·
                        rfl

theorem cell23_2709171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_2709171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709171 prefixEnd_2709171 := by exact prefixLift 2709171
  have htrace : WordTrace (prefixWord ++ tailWord_2709171) baseStart_2709171 baseEnd_2709171 := by
    simpa [prefixWord, tailWord_2709171, baseEnd_2709171] using wordTrace_append hprefix tailTrace_2709171
  have hstable : (prefixWord ++ tailWord_2709171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709171).length < 2 ^ (prefixWord ++ tailWord_2709171).sum := by decide
  have hdescent : baseEnd_2709171 < baseStart_2709171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709175 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_2709175 : Nat := 118140960795 + 2709175 * 2 ^ 59
def prefixEnd_2709175 : Nat := 4983230072969 + 3 ^ 40 * 2709175 * 2
def baseEnd_2709175 : Nat := 1391108952144543074053237

theorem tailTrace_2709175 : CollatzResearch.WordTrace tailWord_2709175 prefixEnd_2709175 1391108952144543074053237 := by
  unfold tailWord_2709175
  simp only [CollatzResearch.WordTrace]
  refine ⟨98811729960129140098456979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65874486640086093398971319 98811729960129140098456979)
  ·
    refine ⟨148217594940193710147685469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98811729960129140098456979 148217594940193710147685469)
    ·
      refine ⟨55581598102572641305382051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148217594940193710147685469 55581598102572641305382051)
      ·
        refine ⟨83372397153858961958073077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55581598102572641305382051 83372397153858961958073077)
        ·
          refine ⟨7816162233174277683569351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83372397153858961958073077 7816162233174277683569351)
          ·
            refine ⟨11724243349761416525354027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816162233174277683569351 11724243349761416525354027)
            ·
              refine ⟨17586365024642124788031041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724243349761416525354027 17586365024642124788031041)
              ·
                refine ⟨13189773768481593591023281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17586365024642124788031041 13189773768481593591023281)
                ·
                  refine ⟨9892330326361195193267461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13189773768481593591023281 9892330326361195193267461)
                  ·
                    refine ⟨1854811936192724098737649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9892330326361195193267461 1854811936192724098737649)
                    ·
                      refine ⟨1391108952144543074053237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854811936192724098737649 1391108952144543074053237)
                      ·
                        rfl

theorem cell23_2709175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_2709175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709175 prefixEnd_2709175 := by exact prefixLift 2709175
  have htrace : WordTrace (prefixWord ++ tailWord_2709175) baseStart_2709175 baseEnd_2709175 := by
    simpa [prefixWord, tailWord_2709175, baseEnd_2709175] using wordTrace_append hprefix tailTrace_2709175
  have hstable : (prefixWord ++ tailWord_2709175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709175).length < 2 ^ (prefixWord ++ tailWord_2709175).sum := by decide
  have hdescent : baseEnd_2709175 < baseStart_2709175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709188 : List Nat := [2, 3, 3, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2709188 : Nat := 118140960795 + 2709188 * 2 ^ 59
def prefixEnd_2709188 : Nat := 4983230072969 + 3 ^ 40 * 2709188 * 2
def baseEnd_2709188 : Nat := 1391115627393051523190677

theorem tailTrace_2709188 : CollatzResearch.WordTrace tailWord_2709188 prefixEnd_2709188 1391115627393051523190677 := by
  unfold tailWord_2709188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406102054541021659340109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65874802739388028879120145 49406102054541021659340109)
  ·
    refine ⟨18527288270452883122252541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49406102054541021659340109 18527288270452883122252541)
    ·
      refine ⟨6947733101419831170844703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18527288270452883122252541 6947733101419831170844703)
      ·
        refine ⟨10421599652129746756267055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947733101419831170844703 10421599652129746756267055)
        ·
          refine ⟨15632399478194620134400583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10421599652129746756267055 15632399478194620134400583)
          ·
            refine ⟨23448599217291930201600875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15632399478194620134400583 23448599217291930201600875)
            ·
              refine ⟨35172898825937895302401313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448599217291930201600875 35172898825937895302401313)
              ·
                refine ⟨26379674119453421476800985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35172898825937895302401313 26379674119453421476800985)
                ·
                  refine ⟨19784755589590066107600739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26379674119453421476800985 19784755589590066107600739)
                  ·
                    refine ⟨29677133384385099161401109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19784755589590066107600739 29677133384385099161401109)
                    ·
                      refine ⟨1391115627393051523190677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29677133384385099161401109 1391115627393051523190677)
                      ·
                        rfl

theorem cell23_2709188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2709188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709188 prefixEnd_2709188 := by exact prefixLift 2709188
  have htrace : WordTrace (prefixWord ++ tailWord_2709188) baseStart_2709188 baseEnd_2709188 := by
    simpa [prefixWord, tailWord_2709188, baseEnd_2709188] using wordTrace_append hprefix tailTrace_2709188
  have hstable : (prefixWord ++ tailWord_2709188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709188).length < 2 ^ (prefixWord ++ tailWord_2709188).sum := by decide
  have hdescent : baseEnd_2709188 < baseStart_2709188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709208 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_2709208 : Nat := 118140960795 + 2709208 * 2 ^ 59
def prefixEnd_2709208 : Nat := 4983230072969 + 3 ^ 40 * 2709208 * 2
def baseEnd_2709208 : Nat := 1391125897006141444940585

theorem tailTrace_2709208 : CollatzResearch.WordTrace tailWord_2709208 prefixEnd_2709208 1391125897006141444940585 := by
  unfold tailWord_2709208
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406466784504793367204139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65875289046006391156272185 49406466784504793367204139)
  ·
    refine ⟨74109700176757190050806209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49406466784504793367204139 74109700176757190050806209)
    ·
      refine ⟨55582275132567892538104657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74109700176757190050806209 55582275132567892538104657)
      ·
        refine ⟨41686706349425919403578493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55582275132567892538104657 41686706349425919403578493)
        ·
          refine ⟨15632514881034719776341935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41686706349425919403578493 15632514881034719776341935)
          ·
            refine ⟨23448772321552079664512903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15632514881034719776341935 23448772321552079664512903)
            ·
              refine ⟨35173158482328119496769355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23448772321552079664512903 35173158482328119496769355)
              ·
                refine ⟨52759737723492179245154033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35173158482328119496769355 52759737723492179245154033)
                ·
                  refine ⟨39569803292619134433865525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52759737723492179245154033 39569803292619134433865525)
                  ·
                    refine ⟨3709669058683043853174893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39569803292619134433865525 3709669058683043853174893)
                    ·
                      refine ⟨1391125897006141444940585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709669058683043853174893 1391125897006141444940585)
                      ·
                        rfl

theorem cell23_2709208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_2709208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709208 prefixEnd_2709208 := by exact prefixLift 2709208
  have htrace : WordTrace (prefixWord ++ tailWord_2709208) baseStart_2709208 baseEnd_2709208 := by
    simpa [prefixWord, tailWord_2709208, baseEnd_2709208] using wordTrace_append hprefix tailTrace_2709208
  have hstable : (prefixWord ++ tailWord_2709208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709208).length < 2 ^ (prefixWord ++ tailWord_2709208).sum := by decide
  have hdescent : baseEnd_2709208 < baseStart_2709208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709235 : List Nat := [1, 1, 1, 2, 2, 3, 3, 1, 4, 3, 2]
def baseStart_2709235 : Nat := 118140960795 + 2709235 * 2 ^ 59
def prefixEnd_2709235 : Nat := 4983230072969 + 3 ^ 40 * 2709235 * 2
def baseEnd_2709235 : Nat := 1391139760983812839302961

theorem tailTrace_2709235 : CollatzResearch.WordTrace tailWord_2709235 prefixEnd_2709235 1391139760983812839302961 := by
  unfold tailWord_2709235
  simp only [CollatzResearch.WordTrace]
  refine ⟨98813918339911770345641159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65875945559941180230427439 98813918339911770345641159)
  ·
    refine ⟨148220877509867655518461739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98813918339911770345641159 148220877509867655518461739)
    ·
      refine ⟨222331316264801483277692609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148220877509867655518461739 222331316264801483277692609)
      ·
        refine ⟨166748487198601112458269457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222331316264801483277692609 166748487198601112458269457)
        ·
          refine ⟨125061365398950834343702093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166748487198601112458269457 125061365398950834343702093)
          ·
            refine ⟨46898012024606562878888285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125061365398950834343702093 46898012024606562878888285)
            ·
              refine ⟨17586754509227461079583107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46898012024606562878888285 17586754509227461079583107)
              ·
                refine ⟨26380131763841191619374661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17586754509227461079583107 26380131763841191619374661)
                ·
                  refine ⟨4946274705720223428632749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26380131763841191619374661 4946274705720223428632749)
                  ·
                    refine ⟨1854853014645083785737281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4946274705720223428632749 1854853014645083785737281)
                    ·
                      refine ⟨1391139760983812839302961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1854853014645083785737281 1391139760983812839302961)
                      ·
                        rfl

theorem cell23_2709235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 1, 4, 3, 2].length) (baseStart_2709235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709235 prefixEnd_2709235 := by exact prefixLift 2709235
  have htrace : WordTrace (prefixWord ++ tailWord_2709235) baseStart_2709235 baseEnd_2709235 := by
    simpa [prefixWord, tailWord_2709235, baseEnd_2709235] using wordTrace_append hprefix tailTrace_2709235
  have hstable : (prefixWord ++ tailWord_2709235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709235).length < 2 ^ (prefixWord ++ tailWord_2709235).sum := by decide
  have hdescent : baseEnd_2709235 < baseStart_2709235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709236 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2709236 : Nat := 118140960795 + 2709236 * 2 ^ 59
def prefixEnd_2709236 : Nat := 4983230072969 + 3 ^ 40 * 2709236 * 2
def baseEnd_2709236 : Nat := 463713424821489111796819

theorem tailTrace_2709236 : CollatzResearch.WordTrace tailWord_2709236 prefixEnd_2709236 463713424821489111796819 := by
  unfold tailWord_2709236
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406977406454073758213781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65875969875272098344285041 49406977406454073758213781)
  ·
    refine ⟨2315952065927534707416271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49406977406454073758213781 2315952065927534707416271)
    ·
      refine ⟨3473928098891302061124407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2315952065927534707416271 3473928098891302061124407)
      ·
        refine ⟨5210892148336953091686611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3473928098891302061124407 5210892148336953091686611)
        ·
          refine ⟨7816338222505429637529917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210892148336953091686611 7816338222505429637529917)
          ·
            refine ⟨2931126833439536114073719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7816338222505429637529917 2931126833439536114073719)
            ·
              refine ⟨4396690250159304171110579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931126833439536114073719 4396690250159304171110579)
              ·
                refine ⟨6595035375238956256665869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396690250159304171110579 6595035375238956256665869)
                ·
                  refine ⟨2473138265714608596249701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6595035375238956256665869 2473138265714608596249701)
                  ·
                    refine ⟨463713424821489111796819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473138265714608596249701 463713424821489111796819)
                    ·
                      rfl

theorem cell23_2709236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2709236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709236 prefixEnd_2709236 := by exact prefixLift 2709236
  have htrace : WordTrace (prefixWord ++ tailWord_2709236) baseStart_2709236 baseEnd_2709236 := by
    simpa [prefixWord, tailWord_2709236, baseEnd_2709236] using wordTrace_append hprefix tailTrace_2709236
  have hstable : (prefixWord ++ tailWord_2709236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709236).length < 2 ^ (prefixWord ++ tailWord_2709236).sum := by decide
  have hdescent : baseEnd_2709236 < baseStart_2709236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709248 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_2709248 : Nat := 118140960795 + 2709248 * 2 ^ 59
def prefixEnd_2709248 : Nat := 4983230072969 + 3 ^ 40 * 2709248 * 2
def baseEnd_2709248 : Nat := 1391146436232321288440401

theorem tailTrace_2709248 : CollatzResearch.WordTrace tailWord_2709248 prefixEnd_2709248 1391146436232321288440401 := by
  unfold tailWord_2709248
  simp only [CollatzResearch.WordTrace]
  refine ⟨49407196244432336782932199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65876261659243115710576265 49407196244432336782932199)
  ·
    refine ⟨74110794366648505174398299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49407196244432336782932199 74110794366648505174398299)
    ·
      refine ⟨111166191549972757761597449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74110794366648505174398299 111166191549972757761597449)
      ·
        refine ⟨83374643662479568321198087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111166191549972757761597449 83374643662479568321198087)
        ·
          refine ⟨125061965493719352481797131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83374643662479568321198087 125061965493719352481797131)
          ·
            refine ⟨187592948240579028722695697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125061965493719352481797131 187592948240579028722695697)
            ·
              refine ⟨140694711180434271542021773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187592948240579028722695697 140694711180434271542021773)
              ·
                refine ⟨52760516692662851828258165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140694711180434271542021773 52760516692662851828258165)
                ·
                  refine ⟨4946298439937142358899203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52760516692662851828258165 4946298439937142358899203)
                  ·
                    refine ⟨7419447659905713538348805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4946298439937142358899203 7419447659905713538348805)
                    ·
                      refine ⟨1391146436232321288440401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7419447659905713538348805 1391146436232321288440401)
                      ·
                        rfl

theorem cell23_2709248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_2709248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709248 prefixEnd_2709248 := by exact prefixLift 2709248
  have htrace : WordTrace (prefixWord ++ tailWord_2709248) baseStart_2709248 baseEnd_2709248 := by
    simpa [prefixWord, tailWord_2709248, baseEnd_2709248] using wordTrace_append hprefix tailTrace_2709248
  have hstable : (prefixWord ++ tailWord_2709248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709248).length < 2 ^ (prefixWord ++ tailWord_2709248).sum := by decide
  have hdescent : baseEnd_2709248 < baseStart_2709248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709285 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_2709285 : Nat := 118140960795 + 2709285 * 2 ^ 59
def prefixEnd_2709285 : Nat := 4983230072969 + 3 ^ 40 * 2709285 * 2
def baseEnd_2709285 : Nat := 1391165435016537643677731

theorem tailTrace_2709285 : CollatzResearch.WordTrace tailWord_2709285 prefixEnd_2709285 1391165435016537643677731 := by
  unfold tailWord_2709285
  simp only [CollatzResearch.WordTrace]
  refine ⟨98815741989730628884961309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65877161326487085923307539 98815741989730628884961309)
  ·
    refine ⟨37055903246148985831860491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98815741989730628884961309 37055903246148985831860491)
    ·
      refine ⟨55583854869223478747790737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37055903246148985831860491 55583854869223478747790737)
      ·
        refine ⟨41687891151917609060843053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55583854869223478747790737 41687891151917609060843053)
        ·
          refine ⟨15632959181969103397816145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41687891151917609060843053 15632959181969103397816145)
          ·
            refine ⟨11724719386476827548362109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15632959181969103397816145 11724719386476827548362109)
            ·
              refine ⟨4396769769928810330635791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11724719386476827548362109 4396769769928810330635791)
              ·
                refine ⟨6595154654893215495953687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396769769928810330635791 6595154654893215495953687)
                ·
                  refine ⟨9892731982339823243930531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595154654893215495953687 9892731982339823243930531)
                  ·
                    refine ⟨14839097973509734865895797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9892731982339823243930531 14839097973509734865895797)
                    ·
                      refine ⟨1391165435016537643677731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14839097973509734865895797 1391165435016537643677731)
                      ·
                        rfl

theorem cell23_2709285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_2709285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709285 prefixEnd_2709285 := by exact prefixLift 2709285
  have htrace : WordTrace (prefixWord ++ tailWord_2709285) baseStart_2709285 baseEnd_2709285 := by
    simpa [prefixWord, tailWord_2709285, baseEnd_2709285] using wordTrace_append hprefix tailTrace_2709285
  have hstable : (prefixWord ++ tailWord_2709285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709285).length < 2 ^ (prefixWord ++ tailWord_2709285).sum := by decide
  have hdescent : baseEnd_2709285 < baseStart_2709285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709288 : List Nat := [2, 1, 5, 1, 1, 13]
def baseStart_2709288 : Nat := 118140960795 + 2709288 * 2 ^ 59
def prefixEnd_2709288 : Nat := 4983230072969 + 3 ^ 40 * 2709288 * 2
def baseEnd_2709288 : Nat := 5724966977195477909219

theorem tailTrace_2709288 : CollatzResearch.WordTrace tailWord_2709288 prefixEnd_2709288 5724966977195477909219 := by
  unfold tailWord_2709288
  simp only [CollatzResearch.WordTrace]
  refine ⟨49407925704359880198660259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65877234272479840264880345 49407925704359880198660259)
  ·
    refine ⟨74111888556539820297990389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49407925704359880198660259 74111888556539820297990389)
    ·
      refine ⟨6947989552175608152936599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74111888556539820297990389 6947989552175608152936599)
      ·
        refine ⟨10421984328263412229404899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6947989552175608152936599 10421984328263412229404899)
        ·
          refine ⟨15632976492395118344107349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10421984328263412229404899 15632976492395118344107349)
          ·
            refine ⟨5724966977195477909219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 15632976492395118344107349 5724966977195477909219)
            ·
              rfl

theorem cell23_2709288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 13].length) (baseStart_2709288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709288 prefixEnd_2709288 := by exact prefixLift 2709288
  have htrace : WordTrace (prefixWord ++ tailWord_2709288) baseStart_2709288 baseEnd_2709288 := by
    simpa [prefixWord, tailWord_2709288, baseEnd_2709288] using wordTrace_append hprefix tailTrace_2709288
  have hstable : (prefixWord ++ tailWord_2709288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709288).length < 2 ^ (prefixWord ++ tailWord_2709288).sum := by decide
  have hdescent : baseEnd_2709288 < baseStart_2709288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709292 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_2709292 : Nat := 118140960795 + 2709292 * 2 ^ 59
def prefixEnd_2709292 : Nat := 4983230072969 + 3 ^ 40 * 2709292 * 2
def baseEnd_2709292 : Nat := 463723009793706372096733

theorem tailTrace_2709292 : CollatzResearch.WordTrace tailWord_2709292 prefixEnd_2709292 463723009793706372096733 := by
  unfold tailWord_2709292
  simp only [CollatzResearch.WordTrace]
  refine ⟨49407998650352634540233065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65877331533803512720310753 49407998650352634540233065)
  ·
    refine ⟨37055998987764475905174799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49407998650352634540233065 37055998987764475905174799)
    ·
      refine ⟨55583998481646713857762199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37055998987764475905174799 55583998481646713857762199)
      ·
        refine ⟨83375997722470070786643299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55583998481646713857762199 83375997722470070786643299)
        ·
          refine ⟨125063996583705106179964949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83375997722470070786643299 125063996583705106179964949)
          ·
            refine ⟨5862374839861176852185857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125063996583705106179964949 5862374839861176852185857)
            ·
              refine ⟨4396781129895882639139393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5862374839861176852185857 4396781129895882639139393)
              ·
                refine ⟨3297585847421911979354545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4396781129895882639139393 3297585847421911979354545)
                ·
                  refine ⟨2473189385566433984515909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297585847421911979354545 2473189385566433984515909)
                  ·
                    refine ⟨463723009793706372096733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473189385566433984515909 463723009793706372096733)
                    ·
                      rfl

theorem cell23_2709292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_2709292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709292 prefixEnd_2709292 := by exact prefixLift 2709292
  have htrace : WordTrace (prefixWord ++ tailWord_2709292) baseStart_2709292 baseEnd_2709292 := by
    simpa [prefixWord, tailWord_2709292, baseEnd_2709292] using wordTrace_append hprefix tailTrace_2709292
  have hstable : (prefixWord ++ tailWord_2709292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709292).length < 2 ^ (prefixWord ++ tailWord_2709292).sum := by decide
  have hdescent : baseEnd_2709292 < baseStart_2709292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709308 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_2709308 : Nat := 118140960795 + 2709308 * 2 ^ 59
def prefixEnd_2709308 : Nat := 4983230072969 + 3 ^ 40 * 2709308 * 2
def baseEnd_2709308 : Nat := 1391177245071591053690125

theorem tailTrace_2709308 : CollatzResearch.WordTrace tailWord_2709308 prefixEnd_2709308 1391177245071591053690125 := by
  unfold tailWord_2709308
  simp only [CollatzResearch.WordTrace]
  refine ⟨49408290434323651906524289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65877720579098202542032385 49408290434323651906524289)
  ·
    refine ⟨37056217825742738929893217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49408290434323651906524289 37056217825742738929893217)
    ·
      refine ⟨27792163369307054197419913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37056217825742738929893217 27792163369307054197419913)
      ·
        refine ⟨20844122526980290648064935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27792163369307054197419913 20844122526980290648064935)
        ·
          refine ⟨31266183790470435972097403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20844122526980290648064935 31266183790470435972097403)
          ·
            refine ⟨46899275685705653958146105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31266183790470435972097403 46899275685705653958146105)
            ·
              refine ⟨35174456764279240468609579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46899275685705653958146105 35174456764279240468609579)
              ·
                refine ⟨52761685146418860702914369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35174456764279240468609579 52761685146418860702914369)
                ·
                  refine ⟨39571263859814145527185777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52761685146418860702914369 39571263859814145527185777)
                  ·
                    refine ⟨29678447894860609145389333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39571263859814145527185777 29678447894860609145389333)
                    ·
                      refine ⟨1391177245071591053690125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29678447894860609145389333 1391177245071591053690125)
                      ·
                        rfl

theorem cell23_2709308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_2709308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709308 prefixEnd_2709308 := by exact prefixLift 2709308
  have htrace : WordTrace (prefixWord ++ tailWord_2709308) baseStart_2709308 baseEnd_2709308 := by
    simpa [prefixWord, tailWord_2709308, baseEnd_2709308] using wordTrace_append hprefix tailTrace_2709308
  have hstable : (prefixWord ++ tailWord_2709308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709308).length < 2 ^ (prefixWord ++ tailWord_2709308).sum := by decide
  have hdescent : baseEnd_2709308 < baseStart_2709308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709315 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3]
def baseStart_2709315 : Nat := 118140960795 + 2709315 * 2 ^ 59
def prefixEnd_2709315 : Nat := 4983230072969 + 3 ^ 40 * 2709315 * 2
def baseEnd_2709315 : Nat := 1391180839436172526302593

theorem tailTrace_2709315 : CollatzResearch.WordTrace tailWord_2709315 prefixEnd_2709315 1391180839436172526302593 := by
  unfold tailWord_2709315
  simp only [CollatzResearch.WordTrace]
  refine ⟨98816836179621944008553399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65877890786414629339035599 98816836179621944008553399)
  ·
    refine ⟨148225254269432916012830099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98816836179621944008553399 148225254269432916012830099)
    ·
      refine ⟨222337881404149374019245149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148225254269432916012830099 222337881404149374019245149)
      ·
        refine ⟨83376705526556015257216931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222337881404149374019245149 83376705526556015257216931)
        ·
          refine ⟨125065058289834022885825397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83376705526556015257216931 125065058289834022885825397)
          ·
            refine ⟨11724849214671939645546131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125065058289834022885825397 11724849214671939645546131)
            ·
              refine ⟨17587273822007909468319197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11724849214671939645546131 17587273822007909468319197)
              ·
                refine ⟨6595227683252966050619699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17587273822007909468319197 6595227683252966050619699)
                ·
                  refine ⟨9892841524879449075929549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595227683252966050619699 9892841524879449075929549)
                  ·
                    refine ⟨3709815571829793403473581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9892841524879449075929549 3709815571829793403473581)
                    ·
                      refine ⟨1391180839436172526302593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709815571829793403473581 1391180839436172526302593)
                      ·
                        rfl

theorem cell23_2709315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_2709315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709315 prefixEnd_2709315 := by exact prefixLift 2709315
  have htrace : WordTrace (prefixWord ++ tailWord_2709315) baseStart_2709315 baseEnd_2709315 := by
    simpa [prefixWord, tailWord_2709315, baseEnd_2709315] using wordTrace_append hprefix tailTrace_2709315
  have hstable : (prefixWord ++ tailWord_2709315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709315).length < 2 ^ (prefixWord ++ tailWord_2709315).sum := by decide
  have hdescent : baseEnd_2709315 < baseStart_2709315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709328 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_2709328 : Nat := 118140960795 + 2709328 * 2 ^ 59
def prefixEnd_2709328 : Nat := 4983230072969 + 3 ^ 40 * 2709328 * 2
def baseEnd_2709328 : Nat := 1391187514684680975440033

theorem tailTrace_2709328 : CollatzResearch.WordTrace tailWord_2709328 prefixEnd_2709328 1391187514684680975440033 := by
  unfold tailWord_2709328
  simp only [CollatzResearch.WordTrace]
  refine ⟨49408655164287423614388319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65878206885716564819184425 49408655164287423614388319)
  ·
    refine ⟨74112982746431135421582479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49408655164287423614388319 74112982746431135421582479)
    ·
      refine ⟨111169474119646703132373719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74112982746431135421582479 111169474119646703132373719)
      ·
        refine ⟨166754211179470054698560579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111169474119646703132373719 166754211179470054698560579)
        ·
          refine ⟨250131316769205082047840869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166754211179470054698560579 250131316769205082047840869)
          ·
            refine ⟨46899621894225952883970163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250131316769205082047840869 46899621894225952883970163)
            ·
              refine ⟨70349432841338929325955245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46899621894225952883970163 70349432841338929325955245)
              ·
                refine ⟨26381037315502098497233217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70349432841338929325955245 26381037315502098497233217)
                ·
                  refine ⟨19785777986626573872924913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26381037315502098497233217 19785777986626573872924913)
                  ·
                    refine ⟨14839333489969930404693685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19785777986626573872924913 14839333489969930404693685)
                    ·
                      refine ⟨1391187514684680975440033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14839333489969930404693685 1391187514684680975440033)
                      ·
                        rfl

theorem cell23_2709328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_2709328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709328 prefixEnd_2709328 := by exact prefixLift 2709328
  have htrace : WordTrace (prefixWord ++ tailWord_2709328) baseStart_2709328 baseEnd_2709328 := by
    simpa [prefixWord, tailWord_2709328, baseEnd_2709328] using wordTrace_append hprefix tailTrace_2709328
  have hstable : (prefixWord ++ tailWord_2709328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709328).length < 2 ^ (prefixWord ++ tailWord_2709328).sum := by decide
  have hdescent : baseEnd_2709328 < baseStart_2709328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709332 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2709332 : Nat := 118140960795 + 2709332 * 2 ^ 59
def prefixEnd_2709332 : Nat := 4983230072969 + 3 ^ 40 * 2709332 * 2
def baseEnd_2709332 : Nat := 1391189568607298959790015

theorem tailTrace_2709332 : CollatzResearch.WordTrace tailWord_2709332 prefixEnd_2709332 1391189568607298959790015 := by
  unfold tailWord_2709332
  simp only [CollatzResearch.WordTrace]
  refine ⟨49408728110280177955961125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65878304147040237274614833 49408728110280177955961125)
  ·
    refine ⟨9264136520677533366742711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49408728110280177955961125 9264136520677533366742711)
    ·
      refine ⟨13896204781016300050114067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9264136520677533366742711 13896204781016300050114067)
      ·
        refine ⟨20844307171524450075171101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896204781016300050114067 20844307171524450075171101)
        ·
          refine ⟨7816615189321668778189163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20844307171524450075171101 7816615189321668778189163)
          ·
            refine ⟨11724922783982503167283745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7816615189321668778189163 11724922783982503167283745)
            ·
              refine ⟨8793692087986877375462809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11724922783982503167283745 8793692087986877375462809)
              ·
                refine ⟨6595269065990158031597107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8793692087986877375462809 6595269065990158031597107)
                ·
                  refine ⟨9892903598985237047395661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595269065990158031597107 9892903598985237047395661)
                  ·
                    refine ⟨3709838849619463892773373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9892903598985237047395661 3709838849619463892773373)
                    ·
                      refine ⟨1391189568607298959790015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709838849619463892773373 1391189568607298959790015)
                      ·
                        rfl

theorem cell23_2709332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2709332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709332 prefixEnd_2709332 := by exact prefixLift 2709332
  have htrace : WordTrace (prefixWord ++ tailWord_2709332) baseStart_2709332 baseEnd_2709332 := by
    simpa [prefixWord, tailWord_2709332, baseEnd_2709332] using wordTrace_append hprefix tailTrace_2709332
  have hstable : (prefixWord ++ tailWord_2709332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709332).length < 2 ^ (prefixWord ++ tailWord_2709332).sum := by decide
  have hdescent : baseEnd_2709332 < baseStart_2709332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709365 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2709365 : Nat := 118140960795 + 2709365 * 2 ^ 59
def prefixEnd_2709365 : Nat := 4983230072969 + 3 ^ 40 * 2709365 * 2
def baseEnd_2709365 : Nat := 463735504489632443559121

theorem tailTrace_2709365 : CollatzResearch.WordTrace tailWord_2709365 prefixEnd_2709365 463735504489632443559121 := by
  unfold tailWord_2709365
  simp only [CollatzResearch.WordTrace]
  refine ⟨98818659829440802547873549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65879106552960535031915699 98818659829440802547873549)
  ·
    refine ⟨37056997436040300955452581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98818659829440802547873549 37056997436040300955452581)
    ·
      refine ⟨6948187019257556429147359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37056997436040300955452581 6948187019257556429147359)
      ·
        refine ⟨10422280528886334643721039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948187019257556429147359 10422280528886334643721039)
        ·
          refine ⟨15633420793329501965581559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10422280528886334643721039 15633420793329501965581559)
          ·
            refine ⟨23450131189994252948372339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15633420793329501965581559 23450131189994252948372339)
            ·
              refine ⟨35175196784991379422558509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23450131189994252948372339 35175196784991379422558509)
              ·
                refine ⟨13190698794371767283459441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35175196784991379422558509 13190698794371767283459441)
                ·
                  refine ⟨9893024095778825462594581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13190698794371767283459441 9893024095778825462594581)
                  ·
                    refine ⟨463735504489632443559121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9893024095778825462594581 463735504489632443559121)
                    ·
                      rfl

theorem cell23_2709365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2709365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709365 prefixEnd_2709365 := by exact prefixLift 2709365
  have htrace : WordTrace (prefixWord ++ tailWord_2709365) baseStart_2709365 baseEnd_2709365 := by
    simpa [prefixWord, tailWord_2709365, baseEnd_2709365] using wordTrace_append hprefix tailTrace_2709365
  have hstable : (prefixWord ++ tailWord_2709365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709365).length < 2 ^ (prefixWord ++ tailWord_2709365).sum := by decide
  have hdescent : baseEnd_2709365 < baseStart_2709365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709366 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2709366 : Nat := 118140960795 + 2709366 * 2 ^ 59
def prefixEnd_2709366 : Nat := 4983230072969 + 3 ^ 40 * 2709366 * 2
def baseEnd_2709366 : Nat := 1391207026949551826764859

theorem tailTrace_2709366 : CollatzResearch.WordTrace tailWord_2709366 prefixEnd_2709366 1391207026949551826764859 := by
  unfold tailWord_2709366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6176168518902323732416247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65879130868291453145773301 6176168518902323732416247)
  ·
    refine ⟨9264252778353485598624371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6176168518902323732416247 9264252778353485598624371)
    ·
      refine ⟨13896379167530228397936557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9264252778353485598624371 13896379167530228397936557)
      ·
        refine ⟨5211142187823835649226209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13896379167530228397936557 5211142187823835649226209)
        ·
          refine ⟨3908356640867876736919657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5211142187823835649226209 3908356640867876736919657)
          ·
            refine ⟨2931267480650907552689743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3908356640867876736919657 2931267480650907552689743)
            ·
              refine ⟨4396901220976361329034615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931267480650907552689743 4396901220976361329034615)
              ·
                refine ⟨6595351831464541993551923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396901220976361329034615 6595351831464541993551923)
                ·
                  refine ⟨9893027747196812990327885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6595351831464541993551923 9893027747196812990327885)
                  ·
                    refine ⟨3709885405198804871372957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9893027747196812990327885 3709885405198804871372957)
                    ·
                      refine ⟨1391207026949551826764859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3709885405198804871372957 1391207026949551826764859)
                      ·
                        rfl

theorem cell23_2709366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2709366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709366 prefixEnd_2709366 := by exact prefixLift 2709366
  have htrace : WordTrace (prefixWord ++ tailWord_2709366) baseStart_2709366 baseEnd_2709366 := by
    simpa [prefixWord, tailWord_2709366, baseEnd_2709366] using wordTrace_append hprefix tailTrace_2709366
  have hstable : (prefixWord ++ tailWord_2709366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709366).length < 2 ^ (prefixWord ++ tailWord_2709366).sum := by decide
  have hdescent : baseEnd_2709366 < baseStart_2709366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709412 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 7]
def baseStart_2709412 : Nat := 118140960795 + 2709412 * 2 ^ 59
def prefixEnd_2709412 : Nat := 4983230072969 + 3 ^ 40 * 2709412 * 2
def baseEnd_2709412 : Nat := 154581183006628738532183

theorem tailTrace_2709412 : CollatzResearch.WordTrace tailWord_2709412 prefixEnd_2709412 154581183006628738532183 := by
  unfold tailWord_2709412
  simp only [CollatzResearch.WordTrace]
  refine ⟨49410187030135264787417245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65880249373513686383222993 49410187030135264787417245)
  ·
    refine ⟨18528820136300724295281467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49410187030135264787417245 18528820136300724295281467)
    ·
      refine ⟨27793230204451086442922201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18528820136300724295281467 27793230204451086442922201)
      ·
        refine ⟨20844922653338314832191651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27793230204451086442922201 20844922653338314832191651)
        ·
          refine ⟨31267383980007472248287477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20844922653338314832191651 31267383980007472248287477)
          ·
            refine ⟨2931317248125700523276951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31267383980007472248287477 2931317248125700523276951)
            ·
              refine ⟨4396975872188550784915427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931317248125700523276951 4396975872188550784915427)
              ·
                refine ⟨6595463808282826177373141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396975872188550784915427 6595463808282826177373141)
                ·
                  refine ⟨154581183006628738532183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6595463808282826177373141 154581183006628738532183)
                  ·
                    rfl

theorem cell23_2709412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_2709412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709412 prefixEnd_2709412 := by exact prefixLift 2709412
  have htrace : WordTrace (prefixWord ++ tailWord_2709412) baseStart_2709412 baseEnd_2709412 := by
    simpa [prefixWord, tailWord_2709412, baseEnd_2709412] using wordTrace_append hprefix tailTrace_2709412
  have hstable : (prefixWord ++ tailWord_2709412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709412).length < 2 ^ (prefixWord ++ tailWord_2709412).sum := by decide
  have hdescent : baseEnd_2709412 < baseStart_2709412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709482 : List Nat := [3, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_2709482 : Nat := 118140960795 + 2709482 * 2 ^ 59
def prefixEnd_2709482 : Nat := 4983230072969 + 3 ^ 40 * 2709482 * 2
def baseEnd_2709482 : Nat := 1391266590705473372914325

theorem tailTrace_2709482 : CollatzResearch.WordTrace tailWord_2709482 prefixEnd_2709482 1391266590705473372914325 := by
  unfold tailWord_2709482
  simp only [CollatzResearch.WordTrace]
  refine ⟨24705731792504232882470675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65881951446677954353255133 24705731792504232882470675)
  ·
    refine ⟨37058597688756349323706013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24705731792504232882470675 37058597688756349323706013)
    ·
      refine ⟨13896974133283630996389755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37058597688756349323706013 13896974133283630996389755)
      ·
        refine ⟨20845461199925446494584633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13896974133283630996389755 20845461199925446494584633)
        ·
          refine ⟨15634095899944084870938475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20845461199925446494584633 15634095899944084870938475)
          ·
            refine ⟨23451143849916127306407713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15634095899944084870938475 23451143849916127306407713)
            ·
              refine ⟨17588357887437095479805785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23451143849916127306407713 17588357887437095479805785)
              ·
                refine ⟨13191268415577821609854339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17588357887437095479805785 13191268415577821609854339)
                ·
                  refine ⟨19786902623366732414781509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13191268415577821609854339 19786902623366732414781509)
                  ·
                    refine ⟨3710044241881262327771533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19786902623366732414781509 3710044241881262327771533)
                    ·
                      refine ⟨1391266590705473372914325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3710044241881262327771533 1391266590705473372914325)
                      ·
                        rfl

theorem cell23_2709482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_2709482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709482 prefixEnd_2709482 := by exact prefixLift 2709482
  have htrace : WordTrace (prefixWord ++ tailWord_2709482) baseStart_2709482 baseEnd_2709482 := by
    simpa [prefixWord, tailWord_2709482, baseEnd_2709482] using wordTrace_append hprefix tailTrace_2709482
  have hstable : (prefixWord ++ tailWord_2709482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709482).length < 2 ^ (prefixWord ++ tailWord_2709482).sum := by decide
  have hdescent : baseEnd_2709482 < baseStart_2709482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709489 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_2709489 : Nat := 118140960795 + 2709489 * 2 ^ 59
def prefixEnd_2709489 : Nat := 4983230072969 + 3 ^ 40 * 2709489 * 2
def baseEnd_2709489 : Nat := 463756728356684948508931

theorem tailTrace_2709489 : CollatzResearch.WordTrace tailWord_2709489 prefixEnd_2709489 463756728356684948508931 := by
  unfold tailWord_2709489
  simp only [CollatzResearch.WordTrace]
  refine ⟨98823182480991571725387521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65882121653994381150258347 98823182480991571725387521)
  ·
    refine ⟨74117386860743678794040641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98823182480991571725387521 74117386860743678794040641)
    ·
      refine ⟨55588040145557759095530481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74117386860743678794040641 55588040145557759095530481)
      ·
        refine ⟨41691030109168319321647861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55588040145557759095530481 41691030109168319321647861)
        ·
          refine ⟨3908534072734529936404487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41691030109168319321647861 3908534072734529936404487)
          ·
            refine ⟨5862801109101794904606731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908534072734529936404487 5862801109101794904606731)
            ·
              refine ⟨8794201663652692356910097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5862801109101794904606731 8794201663652692356910097)
              ·
                refine ⟨6595651247739519267682573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8794201663652692356910097 6595651247739519267682573)
                ·
                  refine ⟨2473369217902319725380965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6595651247739519267682573 2473369217902319725380965)
                  ·
                    refine ⟨463756728356684948508931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473369217902319725380965 463756728356684948508931)
                    ·
                      rfl

theorem cell23_2709489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_2709489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709489 prefixEnd_2709489 := by exact prefixLift 2709489
  have htrace : WordTrace (prefixWord ++ tailWord_2709489) baseStart_2709489 baseEnd_2709489 := by
    simpa [prefixWord, tailWord_2709489, baseEnd_2709489] using wordTrace_append hprefix tailTrace_2709489
  have hstable : (prefixWord ++ tailWord_2709489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709489).length < 2 ^ (prefixWord ++ tailWord_2709489).sum := by decide
  have hdescent : baseEnd_2709489 < baseStart_2709489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709546 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2709546 : Nat := 118140960795 + 2709546 * 2 ^ 59
def prefixEnd_2709546 : Nat := 4983230072969 + 3 ^ 40 * 2709546 * 2
def baseEnd_2709546 : Nat := 1391299453467361122514031

theorem tailTrace_2709546 : CollatzResearch.WordTrace tailWord_2709546 prefixEnd_2709546 1391299453467361122514031 := by
  unfold tailWord_2709546
  simp only [CollatzResearch.WordTrace]
  refine ⟨24706315360446267615053123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65883507627856713640141661 24706315360446267615053123)
  ·
    refine ⟨37059473040669401422579685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24706315360446267615053123 37059473040669401422579685)
    ·
      refine ⟨6948651195125512766733691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37059473040669401422579685 6948651195125512766733691)
      ·
        refine ⟨10422976792688269150100537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948651195125512766733691 10422976792688269150100537)
        ·
          refine ⟨7817232594516201862575403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10422976792688269150100537 7817232594516201862575403)
          ·
            refine ⟨11725848891774302793863105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7817232594516201862575403 11725848891774302793863105)
            ·
              refine ⟨8794386668830727095397329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11725848891774302793863105 8794386668830727095397329)
              ·
                refine ⟨6595790001623045321547997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8794386668830727095397329 6595790001623045321547997)
                ·
                  refine ⟨2473421250608641995580499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6595790001623045321547997 2473421250608641995580499)
                  ·
                    refine ⟨3710131875912962993370749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2473421250608641995580499 3710131875912962993370749)
                    ·
                      refine ⟨1391299453467361122514031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3710131875912962993370749 1391299453467361122514031)
                      ·
                        rfl

theorem cell23_2709546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2709546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709546 prefixEnd_2709546 := by exact prefixLift 2709546
  have htrace : WordTrace (prefixWord ++ tailWord_2709546) baseStart_2709546 baseEnd_2709546 := by
    simpa [prefixWord, tailWord_2709546, baseEnd_2709546] using wordTrace_append hprefix tailTrace_2709546
  have hstable : (prefixWord ++ tailWord_2709546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709546).length < 2 ^ (prefixWord ++ tailWord_2709546).sum := by decide
  have hdescent : baseEnd_2709546 < baseStart_2709546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709582 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6]
def baseStart_2709582 : Nat := 118140960795 + 2709582 * 2 ^ 59
def prefixEnd_2709582 : Nat := 4983230072969 + 3 ^ 40 * 2709582 * 2
def baseEnd_2709582 : Nat := 1391317938770922981663865

theorem tailTrace_2709582 : CollatzResearch.WordTrace tailWord_2709582 prefixEnd_2709582 1391317938770922981663865 := by
  unfold tailWord_2709582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12353321808706831076065375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65884382979769765739015333 12353321808706831076065375)
  ·
    refine ⟨18529982713060246614098063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12353321808706831076065375 18529982713060246614098063)
    ·
      refine ⟨27794974069590369921147095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18529982713060246614098063 27794974069590369921147095)
      ·
        refine ⟨41692461104385554881720643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27794974069590369921147095 41692461104385554881720643)
        ·
          refine ⟨62538691656578332322580965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41692461104385554881720643 62538691656578332322580965)
          ·
            refine ⟨11726004685608437310483931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62538691656578332322580965 11726004685608437310483931)
            ·
              refine ⟨17589007028412655965725897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11726004685608437310483931 17589007028412655965725897)
              ·
                refine ⟨13191755271309491974294423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17589007028412655965725897 13191755271309491974294423)
                ·
                  refine ⟨19787632906964237961441635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13191755271309491974294423 19787632906964237961441635)
                  ·
                    refine ⟨29681449360446356942162453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19787632906964237961441635 29681449360446356942162453)
                    ·
                      refine ⟨1391317938770922981663865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 29681449360446356942162453 1391317938770922981663865)
                      ·
                        rfl

theorem cell23_2709582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_2709582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709582 prefixEnd_2709582 := by exact prefixLift 2709582
  have htrace : WordTrace (prefixWord ++ tailWord_2709582) baseStart_2709582 baseEnd_2709582 := by
    simpa [prefixWord, tailWord_2709582, baseEnd_2709582] using wordTrace_append hprefix tailTrace_2709582
  have hstable : (prefixWord ++ tailWord_2709582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709582).length < 2 ^ (prefixWord ++ tailWord_2709582).sum := by decide
  have hdescent : baseEnd_2709582 < baseStart_2709582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709592 : List Nat := [2, 1, 2, 2, 1, 5, 2, 8]
def baseStart_2709592 : Nat := 118140960795 + 2709592 * 2 ^ 59
def prefixEnd_2709592 : Nat := 4983230072969 + 3 ^ 40 * 2709592 * 2
def baseEnd_2709592 : Nat := 51530484206572886760697

theorem tailTrace_2709592 : CollatzResearch.WordTrace tailWord_2709592 prefixEnd_2709592 51530484206572886760697 := by
  unfold tailWord_2709592
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413469599809210158193515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65884626133078946877591353 49413469599809210158193515)
  ·
    refine ⟨74120204399713815237290273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49413469599809210158193515 74120204399713815237290273)
    ·
      refine ⟨55590153299785361427967705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74120204399713815237290273 55590153299785361427967705)
      ·
        refine ⟨41692614974839021070975779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55590153299785361427967705 41692614974839021070975779)
        ·
          refine ⟨62538922462258531606463669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41692614974839021070975779 62538922462258531606463669)
          ·
            refine ⟨5863023980836737338105969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62538922462258531606463669 5863023980836737338105969)
            ·
              refine ⟨4397267985627553003579477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5863023980836737338105969 4397267985627553003579477)
              ·
                refine ⟨51530484206572886760697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4397267985627553003579477 51530484206572886760697)
                ·
                  rfl

theorem cell23_2709592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 8].length) (baseStart_2709592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709592 prefixEnd_2709592 := by exact prefixLift 2709592
  have htrace : WordTrace (prefixWord ++ tailWord_2709592) baseStart_2709592 baseEnd_2709592 := by
    simpa [prefixWord, tailWord_2709592, baseEnd_2709592] using wordTrace_append hprefix tailTrace_2709592
  have hstable : (prefixWord ++ tailWord_2709592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709592).length < 2 ^ (prefixWord ++ tailWord_2709592).sum := by decide
  have hdescent : baseEnd_2709592 < baseStart_2709592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709596 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2709596 : Nat := 118140960795 + 2709596 * 2 ^ 59
def prefixEnd_2709596 : Nat := 4983230072969 + 3 ^ 40 * 2709596 * 2
def baseEnd_2709596 : Nat := 463775042500028642296267

theorem tailTrace_2709596 : CollatzResearch.WordTrace tailWord_2709596 prefixEnd_2709596 463775042500028642296267 := by
  unfold tailWord_2709596
  simp only [CollatzResearch.WordTrace]
  refine ⟨49413542545801964499766321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65884723394402619333021761 49413542545801964499766321)
  ·
    refine ⟨37060156909351473374824741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49413542545801964499766321 37060156909351473374824741)
    ·
      refine ⟨6948779420503401257779639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37060156909351473374824741 6948779420503401257779639)
      ·
        refine ⟨10423169130755101886669459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6948779420503401257779639 10423169130755101886669459)
        ·
          refine ⟨15634753696132652830004189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10423169130755101886669459 15634753696132652830004189)
          ·
            refine ⟨5863032636049744811251571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15634753696132652830004189 5863032636049744811251571)
            ·
              refine ⟨8794548954074617216877357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863032636049744811251571 8794548954074617216877357)
              ·
                refine ⟨3297955857777981456329009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8794548954074617216877357 3297955857777981456329009)
                ·
                  refine ⟨2473466893333486092246757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3297955857777981456329009 2473466893333486092246757)
                  ·
                    refine ⟨463775042500028642296267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2473466893333486092246757 463775042500028642296267)
                    ·
                      rfl

theorem cell23_2709596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2709596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709596 prefixEnd_2709596 := by exact prefixLift 2709596
  have htrace : WordTrace (prefixWord ++ tailWord_2709596) baseStart_2709596 baseEnd_2709596 := by
    simpa [prefixWord, tailWord_2709596, baseEnd_2709596] using wordTrace_append hprefix tailTrace_2709596
  have hstable : (prefixWord ++ tailWord_2709596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709596).length < 2 ^ (prefixWord ++ tailWord_2709596).sum := by decide
  have hdescent : baseEnd_2709596 < baseStart_2709596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709637 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 1, 2, 2]
def baseStart_2709637 : Nat := 118140960795 + 2709637 * 2 ^ 59
def prefixEnd_2709637 : Nat := 4983230072969 + 3 ^ 40 * 2709637 * 2
def baseEnd_2709637 : Nat := 1391346180206920266476113

theorem tailTrace_2709637 : CollatzResearch.WordTrace tailWord_2709637 prefixEnd_2709637 1391346180206920266476113 := by
  unfold tailWord_2709637
  simp only [CollatzResearch.WordTrace]
  refine ⟨98828580484455393001775165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65885720322970262001183443 98828580484455393001775165)
  ·
    refine ⟨37060717681670772375665687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98828580484455393001775165 37060717681670772375665687)
    ·
      refine ⟨55591076522506158563498531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37060717681670772375665687 55591076522506158563498531)
      ·
        refine ⟨83386614783759237845247797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55591076522506158563498531 83386614783759237845247797)
        ·
          refine ⟨7817495135977428547991981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83386614783759237845247797 7817495135977428547991981)
          ·
            refine ⟨2931560675991535705496993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7817495135977428547991981 2931560675991535705496993)
            ·
              refine ⟨2198670506993651779122745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2931560675991535705496993 2198670506993651779122745)
              ·
                refine ⟨1649002880245238834342059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198670506993651779122745 1649002880245238834342059)
                ·
                  refine ⟨2473504320367858251513089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649002880245238834342059 2473504320367858251513089)
                  ·
                    refine ⟨1855128240275893688634817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2473504320367858251513089 1855128240275893688634817)
                    ·
                      refine ⟨1391346180206920266476113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1855128240275893688634817 1391346180206920266476113)
                      ·
                        rfl

theorem cell23_2709637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_2709637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709637 prefixEnd_2709637 := by exact prefixLift 2709637
  have htrace : WordTrace (prefixWord ++ tailWord_2709637) baseStart_2709637 baseEnd_2709637 := by
    simpa [prefixWord, tailWord_2709637, baseEnd_2709637] using wordTrace_append hprefix tailTrace_2709637
  have hstable : (prefixWord ++ tailWord_2709637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709637).length < 2 ^ (prefixWord ++ tailWord_2709637).sum := by decide
  have hdescent : baseEnd_2709637 < baseStart_2709637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709682 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_2709682 : Nat := 118140960795 + 2709682 * 2 ^ 59
def prefixEnd_2709682 : Nat := 4983230072969 + 3 ^ 40 * 2709682 * 2
def baseEnd_2709682 : Nat := 154596587426263621157045

theorem tailTrace_2709682 : CollatzResearch.WordTrace tailWord_2709682 prefixEnd_2709682 154596587426263621157045 := by
  unfold tailWord_2709682
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707555442323091421790825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65886814512861577124775533 24707555442323091421790825)
  ·
    refine ⟨18530666581742318566343119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24707555442323091421790825 18530666581742318566343119)
    ·
      refine ⟨27795999872613477849514679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18530666581742318566343119 27795999872613477849514679)
      ·
        refine ⟨41693999808920216774272019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27795999872613477849514679 41693999808920216774272019)
        ·
          refine ⟨62540999713380325161408029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41693999808920216774272019 62540999713380325161408029)
          ·
            refine ⟨23452874892517621935528011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62540999713380325161408029 23452874892517621935528011)
            ·
              refine ⟨35179312338776432903292017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23452874892517621935528011 35179312338776432903292017)
              ·
                refine ⟨26384484254082324677469013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35179312338776432903292017 26384484254082324677469013)
                ·
                  refine ⟨154596587426263621157045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 26384484254082324677469013 154596587426263621157045)
                  ·
                    rfl

theorem cell23_2709682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_2709682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709682 prefixEnd_2709682 := by exact prefixLift 2709682
  have htrace : WordTrace (prefixWord ++ tailWord_2709682) baseStart_2709682 baseEnd_2709682 := by
    simpa [prefixWord, tailWord_2709682, baseEnd_2709682] using wordTrace_append hprefix tailTrace_2709682
  have hstable : (prefixWord ++ tailWord_2709682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709682).length < 2 ^ (prefixWord ++ tailWord_2709682).sum := by decide
  have hdescent : baseEnd_2709682 < baseStart_2709682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709729 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2709729 : Nat := 118140960795 + 2709729 * 2 ^ 59
def prefixEnd_2709729 : Nat := 4983230072969 + 3 ^ 40 * 2709729 * 2
def baseEnd_2709729 : Nat := 463797806809044635508563

theorem tailTrace_2709729 : CollatzResearch.WordTrace tailWord_2709729 prefixEnd_2709729 463797806809044635508563 := by
  unfold tailWord_2709729
  simp only [CollatzResearch.WordTrace]
  refine ⟨98831936000122092714124241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65887957333414728476082827 98831936000122092714124241)
  ·
    refine ⟨74123952000091569535593181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98831936000122092714124241 74123952000091569535593181)
    ·
      refine ⟨27796482000034338575847443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74123952000091569535593181 27796482000034338575847443)
      ·
        refine ⟨41694723000051507863771165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27796482000034338575847443 41694723000051507863771165)
        ·
          refine ⟨15635521125019315448914187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41694723000051507863771165 15635521125019315448914187)
          ·
            refine ⟨23453281687528973173371281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15635521125019315448914187 23453281687528973173371281)
            ·
              refine ⟨17589961265646729880028461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23453281687528973173371281 17589961265646729880028461)
              ·
                refine ⟨6596235474617523705010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17589961265646729880028461 6596235474617523705010673)
                ·
                  refine ⟨4947176605963142778758005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6596235474617523705010673 4947176605963142778758005)
                  ·
                    refine ⟨463797806809044635508563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4947176605963142778758005 463797806809044635508563)
                    ·
                      rfl

theorem cell23_2709729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2709729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709729 prefixEnd_2709729 := by exact prefixLift 2709729
  have htrace : WordTrace (prefixWord ++ tailWord_2709729) baseStart_2709729 baseEnd_2709729 := by
    simpa [prefixWord, tailWord_2709729, baseEnd_2709729] using wordTrace_append hprefix tailTrace_2709729
  have hstable : (prefixWord ++ tailWord_2709729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709729).length < 2 ^ (prefixWord ++ tailWord_2709729).sum := by decide
  have hdescent : baseEnd_2709729 < baseStart_2709729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709730 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2709730 : Nat := 118140960795 + 2709730 * 2 ^ 59
def prefixEnd_2709730 : Nat := 4983230072969 + 3 ^ 40 * 2709730 * 2
def baseEnd_2709730 : Nat := 1391393933907788402613185

theorem tailTrace_2709730 : CollatzResearch.WordTrace tailWord_2709730 prefixEnd_2709730 1391393933907788402613185 := by
  unfold tailWord_2709730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24707993118279617471227661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65887981648745646589940429 24707993118279617471227661)
  ·
    refine ⟨9265497419354856551710373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24707993118279617471227661 9265497419354856551710373)
    ·
      refine ⟨1737280766129035603445695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9265497419354856551710373 1737280766129035603445695)
      ·
        refine ⟨2605921149193553405168543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737280766129035603445695 2605921149193553405168543)
        ·
          refine ⟨3908881723790330107752815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2605921149193553405168543 3908881723790330107752815)
          ·
            refine ⟨5863322585685495161629223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3908881723790330107752815 5863322585685495161629223)
            ·
              refine ⟨8794983878528242742443835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5863322585685495161629223 8794983878528242742443835)
              ·
                refine ⟨13192475817792364113665753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8794983878528242742443835 13192475817792364113665753)
                ·
                  refine ⟨9894356863344273085249315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13192475817792364113665753 9894356863344273085249315)
                  ·
                    refine ⟨14841535295016409627873973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9894356863344273085249315 14841535295016409627873973)
                    ·
                      refine ⟨1391393933907788402613185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 14841535295016409627873973 1391393933907788402613185)
                      ·
                        rfl

theorem cell23_2709730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2709730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709730 prefixEnd_2709730 := by exact prefixLift 2709730
  have htrace : WordTrace (prefixWord ++ tailWord_2709730) baseStart_2709730 baseEnd_2709730 := by
    simpa [prefixWord, tailWord_2709730, baseEnd_2709730] using wordTrace_append hprefix tailTrace_2709730
  have hstable : (prefixWord ++ tailWord_2709730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709730).length < 2 ^ (prefixWord ++ tailWord_2709730).sum := by decide
  have hdescent : baseEnd_2709730 < baseStart_2709730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2709733 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 5]
def baseStart_2709733 : Nat := 118140960795 + 2709733 * 2 ^ 59
def prefixEnd_2709733 : Nat := 4983230072969 + 3 ^ 40 * 2709733 * 2
def baseEnd_2709733 : Nat := 154599497149972432319519

theorem tailTrace_2709733 : CollatzResearch.WordTrace tailWord_2709733 prefixEnd_2709733 154599497149972432319519 := by
  unfold tailWord_2709733
  simp only [CollatzResearch.WordTrace]
  refine ⟨98832081892107601397269853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65888054594738400931513235 98832081892107601397269853)
  ·
    refine ⟨37062030709540350523976195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98832081892107601397269853 37062030709540350523976195)
    ·
      refine ⟨55593046064310525785964293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37062030709540350523976195 55593046064310525785964293)
      ·
        refine ⟨10423696137058223584868305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55593046064310525785964293 10423696137058223584868305)
        ·
          refine ⟨7817772102793667688651229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10423696137058223584868305 7817772102793667688651229)
          ·
            refine ⟨2931664538547625383244211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7817772102793667688651229 2931664538547625383244211)
            ·
              refine ⟨4397496807821438074866317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931664538547625383244211 4397496807821438074866317)
              ·
                refine ⟨1649061302933039278074869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4397496807821438074866317 1649061302933039278074869)
                ·
                  refine ⟨154599497149972432319519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1649061302933039278074869 154599497149972432319519)
                  ·
                    rfl

theorem cell23_2709733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_2709733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2709733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2709733 prefixEnd_2709733 := by exact prefixLift 2709733
  have htrace : WordTrace (prefixWord ++ tailWord_2709733) baseStart_2709733 baseEnd_2709733 := by
    simpa [prefixWord, tailWord_2709733, baseEnd_2709733] using wordTrace_append hprefix tailTrace_2709733
  have hstable : (prefixWord ++ tailWord_2709733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2709733).length < 2 ^ (prefixWord ++ tailWord_2709733).sum := by decide
  have hdescent : baseEnd_2709733 < baseStart_2709733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2709733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
