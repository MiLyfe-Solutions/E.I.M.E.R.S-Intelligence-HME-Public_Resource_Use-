import V185TrunkScan23Chunk0344

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2041178 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_2041178 : Nat := 118140960795 + 2041178 * 2 ^ 59
def prefixEnd_2041178 : Nat := 4983230072969 + 3 ^ 40 * 2041178 * 2
def baseEnd_2041178 : Nat := 349368471794373371795933

theorem tailTrace_2041178 : CollatzResearch.WordTrace tailWord_2041178 prefixEnd_2041178 349368471794373371795933 := by
  unfold tailWord_2041178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18611969449792046573403047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49631918532778790862408125 18611969449792046573403047)
  ·
    refine ⟨27917954174688069860104571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18611969449792046573403047 27917954174688069860104571)
    ·
      refine ⟨41876931262032104790156857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27917954174688069860104571 41876931262032104790156857)
      ·
        refine ⟨31407698446524078592617643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41876931262032104790156857 31407698446524078592617643)
        ·
          refine ⟨47111547669786117888926465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31407698446524078592617643 47111547669786117888926465)
          ·
            refine ⟨35333660752339588416694849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47111547669786117888926465 35333660752339588416694849)
            ·
              refine ⟨26500245564254691312521137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35333660752339588416694849 26500245564254691312521137)
              ·
                refine ⟨19875184173191018484390853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26500245564254691312521137 19875184173191018484390853)
                ·
                  refine ⟨3726597032473315965823285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19875184173191018484390853 3726597032473315965823285)
                  ·
                    refine ⟨349368471794373371795933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3726597032473315965823285 349368471794373371795933)
                    ·
                      rfl

theorem cell23_2041178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_2041178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041178 prefixEnd_2041178 := by exact prefixLift 2041178
  have htrace : WordTrace (prefixWord ++ tailWord_2041178) baseStart_2041178 baseEnd_2041178 := by
    simpa [prefixWord, tailWord_2041178, baseEnd_2041178] using wordTrace_append hprefix tailTrace_2041178
  have hstable : (prefixWord ++ tailWord_2041178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041178).length < 2 ^ (prefixWord ++ tailWord_2041178).sum := by decide
  have hdescent : baseEnd_2041178 < baseStart_2041178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041228 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_2041228 : Nat := 118140960795 + 2041228 * 2 ^ 59
def prefixEnd_2041228 : Nat := 4983230072969 + 3 ^ 40 * 2041228 * 2
def baseEnd_2041228 : Nat := 1048131089415844919762569

theorem tailTrace_2041228 : CollatzResearch.WordTrace tailWord_2041228 prefixEnd_2041228 1048131089415844919762569 := by
  unfold tailWord_2041228
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224850724493522416466169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49633134299324696555288225 37224850724493522416466169)
  ·
    refine ⟨27918638043370141812349627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37224850724493522416466169 27918638043370141812349627)
    ·
      refine ⟨41877957065055212718524441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27918638043370141812349627 41877957065055212718524441)
      ·
        refine ⟨31408467798791409538893331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41877957065055212718524441 31408467798791409538893331)
        ·
          refine ⟨47112701698187114308339997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31408467798791409538893331 47112701698187114308339997)
          ·
            refine ⟨17667263136820167865627499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47112701698187114308339997 17667263136820167865627499)
            ·
              refine ⟨26500894705230251798441249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17667263136820167865627499 26500894705230251798441249)
              ·
                refine ⟨19875671028922688848830937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26500894705230251798441249 19875671028922688848830937)
                ·
                  refine ⟨14906753271692016636623203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19875671028922688848830937 14906753271692016636623203)
                  ·
                    refine ⟨22360129907538024954934805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14906753271692016636623203 22360129907538024954934805)
                    ·
                      refine ⟨1048131089415844919762569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22360129907538024954934805 1048131089415844919762569)
                      ·
                        rfl

theorem cell23_2041228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_2041228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041228 prefixEnd_2041228 := by exact prefixLift 2041228
  have htrace : WordTrace (prefixWord ++ tailWord_2041228) baseStart_2041228 baseEnd_2041228 := by
    simpa [prefixWord, tailWord_2041228, baseEnd_2041228] using wordTrace_append hprefix tailTrace_2041228
  have hstable : (prefixWord ++ tailWord_2041228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041228).length < 2 ^ (prefixWord ++ tailWord_2041228).sum := by decide
  have hdescent : baseEnd_2041228 < baseStart_2041228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041276 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_2041276 : Nat := 118140960795 + 2041276 * 2 ^ 59
def prefixEnd_2041276 : Nat := 4983230072969 + 3 ^ 40 * 2041276 * 2
def baseEnd_2041276 : Nat := 349385245495753577320783

theorem tailTrace_2041276 : CollatzResearch.WordTrace tailWord_2041276 prefixEnd_2041276 349385245495753577320783 := by
  unfold tailWord_2041276
  simp only [CollatzResearch.WordTrace]
  refine ⟨37225726076406574515339841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49634301435208766020453121 37225726076406574515339841)
  ·
    refine ⟨27919294557304930886504881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37225726076406574515339841 27919294557304930886504881)
    ·
      refine ⟨20939470917978698164878661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27919294557304930886504881 20939470917978698164878661)
      ·
        refine ⟨3926150797121005905914749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20939470917978698164878661 3926150797121005905914749)
        ·
          refine ⟨1472306548920377214718031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3926150797121005905914749 1472306548920377214718031)
          ·
            refine ⟨2208459823380565822077047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472306548920377214718031 2208459823380565822077047)
            ·
              refine ⟨3312689735070848733115571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208459823380565822077047 3312689735070848733115571)
              ·
                refine ⟨4969034602606273099673357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312689735070848733115571 4969034602606273099673357)
                ·
                  refine ⟨1863387975977352412377509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4969034602606273099673357 1863387975977352412377509)
                  ·
                    refine ⟨349385245495753577320783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863387975977352412377509 349385245495753577320783)
                    ·
                      rfl

theorem cell23_2041276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_2041276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041276 prefixEnd_2041276 := by exact prefixLift 2041276
  have htrace : WordTrace (prefixWord ++ tailWord_2041276) baseStart_2041276 baseEnd_2041276 := by
    simpa [prefixWord, tailWord_2041276, baseEnd_2041276] using wordTrace_append hprefix tailTrace_2041276
  have hstable : (prefixWord ++ tailWord_2041276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041276).length < 2 ^ (prefixWord ++ tailWord_2041276).sum := by decide
  have hdescent : baseEnd_2041276 < baseStart_2041276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041309 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_2041309 : Nat := 118140960795 + 2041309 * 2 ^ 59
def prefixEnd_2041309 : Nat := 4983230072969 + 3 ^ 40 * 2041309 * 2
def baseEnd_2041309 : Nat := 1048172681348859102849697

theorem tailTrace_2041309 : CollatzResearch.WordTrace tailWord_2041309 prefixEnd_2041309 1048172681348859102849697 := by
  unfold tailWord_2041309
  simp only [CollatzResearch.WordTrace]
  refine ⟨74452655761693595666630981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49635103841129063777753987 74452655761693595666630981)
  ·
    refine ⟨13959872955317549187493309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74452655761693595666630981 13959872955317549187493309)
    ·
      refine ⟨5234952358244080945309991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13959872955317549187493309 5234952358244080945309991)
      ·
        refine ⟨7852428537366121417964987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234952358244080945309991 7852428537366121417964987)
        ·
          refine ⟨11778642806049182126947481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852428537366121417964987 11778642806049182126947481)
          ·
            refine ⟨8833982104536886595210611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778642806049182126947481 8833982104536886595210611)
            ·
              refine ⟨13250973156805329892815917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833982104536886595210611 13250973156805329892815917)
              ·
                refine ⟨4969114933801998709805969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13250973156805329892815917 4969114933801998709805969)
                ·
                  refine ⟨3726836200351499032354477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969114933801998709805969 3726836200351499032354477)
                  ·
                    refine ⟨1397563575131812137132929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726836200351499032354477 1397563575131812137132929)
                    ·
                      refine ⟨1048172681348859102849697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397563575131812137132929 1048172681348859102849697)
                      ·
                        rfl

theorem cell23_2041309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_2041309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041309 prefixEnd_2041309 := by exact prefixLift 2041309
  have htrace : WordTrace (prefixWord ++ tailWord_2041309) baseStart_2041309 baseEnd_2041309 := by
    simpa [prefixWord, tailWord_2041309, baseEnd_2041309] using wordTrace_append hprefix tailTrace_2041309
  have hstable : (prefixWord ++ tailWord_2041309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041309).length < 2 ^ (prefixWord ++ tailWord_2041309).sum := by decide
  have hdescent : baseEnd_2041309 < baseStart_2041309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041315 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 3, 6]
def baseStart_2041315 : Nat := 118140960795 + 2041315 * 2 ^ 59
def prefixEnd_2041315 : Nat := 4983230072969 + 3 ^ 40 * 2041315 * 2
def baseEnd_2041315 : Nat := 349391920744262026458223

theorem tailTrace_2041315 : CollatzResearch.WordTrace tailWord_2041315 prefixEnd_2041315 349391920744262026458223 := by
  unfold tailWord_2041315
  simp only [CollatzResearch.WordTrace]
  refine ⟨74452874599671858691349399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49635249733114572460899599 74452874599671858691349399)
  ·
    refine ⟨111679311899507788037024099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74452874599671858691349399 111679311899507788037024099)
    ·
      refine ⟨167518967849261682055536149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111679311899507788037024099 167518967849261682055536149)
      ·
        refine ⟨7852451617934141346353257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167518967849261682055536149 7852451617934141346353257)
        ·
          refine ⟨5889338713450606009764943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7852451617934141346353257 5889338713450606009764943)
          ·
            refine ⟨8834008070175909014647415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889338713450606009764943 8834008070175909014647415)
            ·
              refine ⟨13251012105263863521971123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834008070175909014647415 13251012105263863521971123)
              ·
                refine ⟨19876518157895795282956685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251012105263863521971123 19876518157895795282956685)
                ·
                  refine ⟨7453694309210923231108757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19876518157895795282956685 7453694309210923231108757)
                  ·
                    refine ⟨349391920744262026458223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7453694309210923231108757 349391920744262026458223)
                    ·
                      rfl

theorem cell23_2041315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 6].length) (baseStart_2041315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041315 prefixEnd_2041315 := by exact prefixLift 2041315
  have htrace : WordTrace (prefixWord ++ tailWord_2041315) baseStart_2041315 baseEnd_2041315 := by
    simpa [prefixWord, tailWord_2041315, baseEnd_2041315] using wordTrace_append hprefix tailTrace_2041315
  have hstable : (prefixWord ++ tailWord_2041315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041315).length < 2 ^ (prefixWord ++ tailWord_2041315).sum := by decide
  have hdescent : baseEnd_2041315 < baseStart_2041315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041319 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 1, 5]
def baseStart_2041319 : Nat := 118140960795 + 2041319 * 2 ^ 59
def prefixEnd_2041319 : Nat := 4983230072969 + 3 ^ 40 * 2041319 * 2
def baseEnd_2041319 : Nat := 349392605385134687908217

theorem tailTrace_2041319 : CollatzResearch.WordTrace tailWord_2041319 prefixEnd_2041319 349392605385134687908217 := by
  unfold tailWord_2041319
  simp only [CollatzResearch.WordTrace]
  refine ⟨74453020491657367374495011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49635346994438244916330007 74453020491657367374495011)
  ·
    refine ⟨111679530737486051061742517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74453020491657367374495011 111679530737486051061742517)
    ·
      refine ⟨10469956006639317287038361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111679530737486051061742517 10469956006639317287038361)
      ·
        refine ⟨7852467004979487965278771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10469956006639317287038361 7852467004979487965278771)
        ·
          refine ⟨11778700507469231947918157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852467004979487965278771 11778700507469231947918157)
          ·
            refine ⟨4417012690300961980469309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11778700507469231947918157 4417012690300961980469309)
            ·
              refine ⟨1656379758862860742675991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4417012690300961980469309 1656379758862860742675991)
              ·
                refine ⟨2484569638294291114013987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656379758862860742675991 2484569638294291114013987)
                ·
                  refine ⟨3726854457441436671020981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484569638294291114013987 3726854457441436671020981)
                  ·
                    refine ⟨349392605385134687908217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3726854457441436671020981 349392605385134687908217)
                    ·
                      rfl

theorem cell23_2041319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_2041319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041319 prefixEnd_2041319 := by exact prefixLift 2041319
  have htrace : WordTrace (prefixWord ++ tailWord_2041319) baseStart_2041319 baseEnd_2041319 := by
    simpa [prefixWord, tailWord_2041319, baseEnd_2041319] using wordTrace_append hprefix tailTrace_2041319
  have hstable : (prefixWord ++ tailWord_2041319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041319).length < 2 ^ (prefixWord ++ tailWord_2041319).sum := by decide
  have hdescent : baseEnd_2041319 < baseStart_2041319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041328 : List Nat := [2, 1, 1, 1, 3, 15]
def baseStart_2041328 : Nat := 118140960795 + 2041328 * 2 ^ 59
def prefixEnd_2041328 : Nat := 4983230072969 + 3 ^ 40 * 2041328 * 2
def baseEnd_2041328 : Nat := 4313507973174051557663

theorem tailTrace_2041328 : CollatzResearch.WordTrace tailWord_2041328 prefixEnd_2041328 4313507973174051557663 := by
  unfold tailWord_2041328
  simp only [CollatzResearch.WordTrace]
  refine ⟨37226674374312380955786319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49635565832416507941048425 37226674374312380955786319)
  ·
    refine ⟨55840011561468571433679479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37226674374312380955786319 55840011561468571433679479)
    ·
      refine ⟨83760017342202857150519219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55840011561468571433679479 83760017342202857150519219)
      ·
        refine ⟨125640026013304285725778829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83760017342202857150519219 125640026013304285725778829)
        ·
          refine ⟨47115009754989107147167061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125640026013304285725778829 47115009754989107147167061)
          ·
            refine ⟨4313507973174051557663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 47115009754989107147167061 4313507973174051557663)
            ·
              rfl

theorem cell23_2041328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 15].length) (baseStart_2041328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041328 prefixEnd_2041328 := by exact prefixLift 2041328
  have htrace : WordTrace (prefixWord ++ tailWord_2041328) baseStart_2041328 baseEnd_2041328 := by
    simpa [prefixWord, tailWord_2041328, baseEnd_2041328] using wordTrace_append hprefix tailTrace_2041328
  have hstable : (prefixWord ++ tailWord_2041328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041328).length < 2 ^ (prefixWord ++ tailWord_2041328).sum := by decide
  have hdescent : baseEnd_2041328 < baseStart_2041328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041333 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_2041333 : Nat := 118140960795 + 2041333 * 2 ^ 59
def prefixEnd_2041333 : Nat := 4983230072969 + 3 ^ 40 * 2041333 * 2
def baseEnd_2041333 : Nat := 1048185004884567008949587

theorem tailTrace_2041333 : CollatzResearch.WordTrace tailWord_2041333 prefixEnd_2041333 1048185004884567008949587 := by
  unfold tailWord_2041333
  simp only [CollatzResearch.WordTrace]
  refine ⟨74453531113606647765504653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49635687409071098510336435 74453531113606647765504653)
  ·
    refine ⟨27920074167602492912064245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74453531113606647765504653 27920074167602492912064245)
    ·
      refine ⟨2617506953212733710506023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27920074167602492912064245 2617506953212733710506023)
      ·
        refine ⟨3926260429819100565759035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617506953212733710506023 3926260429819100565759035)
        ·
          refine ⟨5889390644728650848638553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926260429819100565759035 5889390644728650848638553)
          ·
            refine ⟨4417042983546488136478915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889390644728650848638553 4417042983546488136478915)
            ·
              refine ⟨6625564475319732204718373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417042983546488136478915 6625564475319732204718373)
              ·
                refine ⟨1242293339122449788384695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6625564475319732204718373 1242293339122449788384695)
                ·
                  refine ⟨1863440008683674682577043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242293339122449788384695 1863440008683674682577043)
                  ·
                    refine ⟨2795160013025512023865565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863440008683674682577043 2795160013025512023865565)
                    ·
                      refine ⟨1048185004884567008949587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795160013025512023865565 1048185004884567008949587)
                      ·
                        rfl

theorem cell23_2041333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_2041333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041333 prefixEnd_2041333 := by exact prefixLift 2041333
  have htrace : WordTrace (prefixWord ++ tailWord_2041333) baseStart_2041333 baseEnd_2041333 := by
    simpa [prefixWord, tailWord_2041333, baseEnd_2041333] using wordTrace_append hprefix tailTrace_2041333
  have hstable : (prefixWord ++ tailWord_2041333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041333).length < 2 ^ (prefixWord ++ tailWord_2041333).sum := by decide
  have hdescent : baseEnd_2041333 < baseStart_2041333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041350 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_2041350 : Nat := 118140960795 + 2041350 * 2 ^ 59
def prefixEnd_2041350 : Nat := 4983230072969 + 3 ^ 40 * 2041350 * 2
def baseEnd_2041350 : Nat := 1048193734055693442437009

theorem tailTrace_2041350 : CollatzResearch.WordTrace tailWord_2041350 prefixEnd_2041350 1048193734055693442437009 := by
  unfold tailWord_2041350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2326692223579533114652297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49636100769696706445915669 2326692223579533114652297)
  ·
    refine ⟨1745019167684649835989223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2326692223579533114652297 1745019167684649835989223)
    ·
      refine ⟨2617528751526974753983835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745019167684649835989223 2617528751526974753983835)
      ·
        refine ⟨3926293127290462130975753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617528751526974753983835 3926293127290462130975753)
        ·
          refine ⟨2944719845467846598231815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3926293127290462130975753 2944719845467846598231815)
          ·
            refine ⟨4417079768201769897347723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944719845467846598231815 4417079768201769897347723)
            ·
              refine ⟨6625619652302654846021585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417079768201769897347723 6625619652302654846021585)
              ·
                refine ⟨4969214739226991134516189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625619652302654846021585 4969214739226991134516189)
                ·
                  refine ⟨1863455527210121675443571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4969214739226991134516189 1863455527210121675443571)
                  ·
                    refine ⟨2795183290815182513165357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863455527210121675443571 2795183290815182513165357)
                    ·
                      refine ⟨1048193734055693442437009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795183290815182513165357 1048193734055693442437009)
                      ·
                        rfl

theorem cell23_2041350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_2041350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041350 prefixEnd_2041350 := by exact prefixLift 2041350
  have htrace : WordTrace (prefixWord ++ tailWord_2041350) baseStart_2041350 baseEnd_2041350 := by
    simpa [prefixWord, tailWord_2041350, baseEnd_2041350] using wordTrace_append hprefix tailTrace_2041350
  have hstable : (prefixWord ++ tailWord_2041350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041350).length < 2 ^ (prefixWord ++ tailWord_2041350).sum := by decide
  have hdescent : baseEnd_2041350 < baseStart_2041350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041356 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_2041356 : Nat := 118140960795 + 2041356 * 2 ^ 59
def prefixEnd_2041356 : Nat := 4983230072969 + 3 ^ 40 * 2041356 * 2
def baseEnd_2041356 : Nat := 1048196814939620418961981

theorem tailTrace_2041356 : CollatzResearch.WordTrace tailWord_2041356 prefixEnd_2041356 1048196814939620418961981 := by
  unfold tailWord_2041356
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227184996261661346795961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49636246661682215129061281 37227184996261661346795961)
  ·
    refine ⟨27920388747196246010096971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37227184996261661346795961 27920388747196246010096971)
    ·
      refine ⟨41880583120794369015145457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27920388747196246010096971 41880583120794369015145457)
      ·
        refine ⟨31410437340595776761359093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41880583120794369015145457 31410437340595776761359093)
        ·
          refine ⟨2944728500680854071377415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31410437340595776761359093 2944728500680854071377415)
          ·
            refine ⟨4417092751021281107066123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944728500680854071377415 4417092751021281107066123)
            ·
              refine ⟨6625639126531921660599185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417092751021281107066123 6625639126531921660599185)
              ·
                refine ⟨4969229344898941245449389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625639126531921660599185 4969229344898941245449389)
                ·
                  refine ⟨1863461004337102967043521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4969229344898941245449389 1863461004337102967043521)
                  ·
                    refine ⟨1397595753252827225282641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863461004337102967043521 1397595753252827225282641)
                    ·
                      refine ⟨1048196814939620418961981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397595753252827225282641 1048196814939620418961981)
                      ·
                        rfl

theorem cell23_2041356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_2041356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041356 prefixEnd_2041356 := by exact prefixLift 2041356
  have htrace : WordTrace (prefixWord ++ tailWord_2041356) baseStart_2041356 baseEnd_2041356 := by
    simpa [prefixWord, tailWord_2041356, baseEnd_2041356] using wordTrace_append hprefix tailTrace_2041356
  have hstable : (prefixWord ++ tailWord_2041356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041356).length < 2 ^ (prefixWord ++ tailWord_2041356).sum := by decide
  have hdescent : baseEnd_2041356 < baseStart_2041356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041372 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2041372 : Nat := 118140960795 + 2041372 * 2 ^ 59
def prefixEnd_2041372 : Nat := 4983230072969 + 3 ^ 40 * 2041372 * 2
def baseEnd_2041372 : Nat := 1048205030630092356361907

theorem tailTrace_2041372 : CollatzResearch.WordTrace tailWord_2041372 prefixEnd_2041372 1048205030630092356361907 := by
  unfold tailWord_2041372
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227476780232678713087185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49636635706976904950782913 37227476780232678713087185)
  ·
    refine ⟨27920607585174509034815389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37227476780232678713087185 27920607585174509034815389)
    ·
      refine ⟨10470227844440440888055771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27920607585174509034815389 10470227844440440888055771)
      ·
        refine ⟨15705341766660661332083657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10470227844440440888055771 15705341766660661332083657)
        ·
          refine ⟨11779006324995495999062743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15705341766660661332083657 11779006324995495999062743)
          ·
            refine ⟨17668509487493243998594115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779006324995495999062743 17668509487493243998594115)
            ·
              refine ⟨26502764231239865997891173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17668509487493243998594115 26502764231239865997891173)
              ·
                refine ⟨4969268293357474874604595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26502764231239865997891173 4969268293357474874604595)
                ·
                  refine ⟨7453902440036212311906893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969268293357474874604595 7453902440036212311906893)
                  ·
                    refine ⟨2795213415013579616965085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7453902440036212311906893 2795213415013579616965085)
                    ·
                      refine ⟨1048205030630092356361907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795213415013579616965085 1048205030630092356361907)
                      ·
                        rfl

theorem cell23_2041372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2041372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041372 prefixEnd_2041372 := by exact prefixLift 2041372
  have htrace : WordTrace (prefixWord ++ tailWord_2041372) baseStart_2041372 baseEnd_2041372 := by
    simpa [prefixWord, tailWord_2041372, baseEnd_2041372] using wordTrace_append hprefix tailTrace_2041372
  have hstable : (prefixWord ++ tailWord_2041372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041372).length < 2 ^ (prefixWord ++ tailWord_2041372).sum := by decide
  have hdescent : baseEnd_2041372 < baseStart_2041372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041373 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2041373 : Nat := 118140960795 + 2041373 * 2 ^ 59
def prefixEnd_2041373 : Nat := 4983230072969 + 3 ^ 40 * 2041373 * 2
def baseEnd_2041373 : Nat := 1048205544110746852449403

theorem tailTrace_2041373 : CollatzResearch.WordTrace tailWord_2041373 prefixEnd_2041373 1048205544110746852449403 := by
  unfold tailWord_2041373
  simp only [CollatzResearch.WordTrace]
  refine ⟨74454990033461734596960773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49636660022307823064640515 74454990033461734596960773)
  ·
    refine ⟨13960310631274075236930145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74454990033461734596960773 13960310631274075236930145)
    ·
      refine ⟨10470232973455556427697609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13960310631274075236930145 10470232973455556427697609)
      ·
        refine ⟨7852674730091667320773207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470232973455556427697609 7852674730091667320773207)
        ·
          refine ⟨11779012095137500981159811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852674730091667320773207 11779012095137500981159811)
          ·
            refine ⟨17668518142706251471739717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779012095137500981159811 17668518142706251471739717)
            ·
              refine ⟨3312847151757422150951197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17668518142706251471739717 3312847151757422150951197)
              ·
                refine ⟨1242317681909033306606699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312847151757422150951197 1242317681909033306606699)
                ·
                  refine ⟨1863476522863549959910049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242317681909033306606699 1863476522863549959910049)
                  ·
                    refine ⟨1397607392147662469932537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863476522863549959910049 1397607392147662469932537)
                    ·
                      refine ⟨1048205544110746852449403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397607392147662469932537 1048205544110746852449403)
                      ·
                        rfl

theorem cell23_2041373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2041373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041373 prefixEnd_2041373 := by exact prefixLift 2041373
  have htrace : WordTrace (prefixWord ++ tailWord_2041373) baseStart_2041373 baseEnd_2041373 := by
    simpa [prefixWord, tailWord_2041373, baseEnd_2041373] using wordTrace_append hprefix tailTrace_2041373
  have hstable : (prefixWord ++ tailWord_2041373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041373).length < 2 ^ (prefixWord ++ tailWord_2041373).sum := by decide
  have hdescent : baseEnd_2041373 < baseStart_2041373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041376 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2041376 : Nat := 118140960795 + 2041376 * 2 ^ 59
def prefixEnd_2041376 : Nat := 4983230072969 + 3 ^ 40 * 2041376 * 2
def baseEnd_2041376 : Nat := 1048207084552710340711889

theorem tailTrace_2041376 : CollatzResearch.WordTrace tailWord_2041376 prefixEnd_2041376 1048207084552710340711889 := by
  unfold tailWord_2041376
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227549726225433054659991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49636732968300577406213321 37227549726225433054659991)
  ·
    refine ⟨55841324589338149581989987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37227549726225433054659991 55841324589338149581989987)
    ·
      refine ⟨83761986884007224372984981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55841324589338149581989987 83761986884007224372984981)
      ·
        refine ⟨3926343135187838642483671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83761986884007224372984981 3926343135187838642483671)
        ·
          refine ⟨5889514702781757963725507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926343135187838642483671 5889514702781757963725507)
          ·
            refine ⟨8834272054172636945588261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889514702781757963725507 8834272054172636945588261)
            ·
              refine ⟨1656426010157369427297799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8834272054172636945588261 1656426010157369427297799)
              ·
                refine ⟨2484639015236054140946699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656426010157369427297799 2484639015236054140946699)
                ·
                  refine ⟨3726958522854081211420049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484639015236054140946699 3726958522854081211420049)
                  ·
                    refine ⟨2795218892140560908565037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3726958522854081211420049 2795218892140560908565037)
                    ·
                      refine ⟨1048207084552710340711889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795218892140560908565037 1048207084552710340711889)
                      ·
                        rfl

theorem cell23_2041376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2041376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041376 prefixEnd_2041376 := by exact prefixLift 2041376
  have htrace : WordTrace (prefixWord ++ tailWord_2041376) baseStart_2041376 baseEnd_2041376 := by
    simpa [prefixWord, tailWord_2041376, baseEnd_2041376] using wordTrace_append hprefix tailTrace_2041376
  have hstable : (prefixWord ++ tailWord_2041376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041376).length < 2 ^ (prefixWord ++ tailWord_2041376).sum := by decide
  have hdescent : baseEnd_2041376 < baseStart_2041376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041475 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7]
def baseStart_2041475 : Nat := 118140960795 + 2041475 * 2 ^ 59
def prefixEnd_2041475 : Nat := 4983230072969 + 3 ^ 40 * 2041475 * 2
def baseEnd_2041475 : Nat := 1048257919137505453373933

theorem tailTrace_2041475 : CollatzResearch.WordTrace tailWord_2041475 prefixEnd_2041475 1048257919137505453373933 := by
  unfold tailWord_2041475
  simp only [CollatzResearch.WordTrace]
  refine ⟨74458710279092206017173879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49639140186061470678115919 74458710279092206017173879)
  ·
    refine ⟨111688065418638309025760819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74458710279092206017173879 111688065418638309025760819)
    ·
      refine ⟨167532098127957463538641229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111688065418638309025760819 167532098127957463538641229)
      ·
        refine ⟨62824536797984048826990461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167532098127957463538641229 62824536797984048826990461)
        ·
          refine ⟨23559201299244018310121423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62824536797984048826990461 23559201299244018310121423)
          ·
            refine ⟨35338801948866027465182135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23559201299244018310121423 35338801948866027465182135)
            ·
              refine ⟨53008202923299041197773203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35338801948866027465182135 53008202923299041197773203)
              ·
                refine ⟨79512304384948561796659805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53008202923299041197773203 79512304384948561796659805)
                ·
                  refine ⟨29817114144355710673747427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79512304384948561796659805 29817114144355710673747427)
                  ·
                    refine ⟨44725671216533566010621141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29817114144355710673747427 44725671216533566010621141)
                    ·
                      refine ⟨1048257919137505453373933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44725671216533566010621141 1048257919137505453373933)
                      ·
                        rfl

theorem cell23_2041475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_2041475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041475 prefixEnd_2041475 := by exact prefixLift 2041475
  have htrace : WordTrace (prefixWord ++ tailWord_2041475) baseStart_2041475 baseEnd_2041475 := by
    simpa [prefixWord, tailWord_2041475, baseEnd_2041475] using wordTrace_append hprefix tailTrace_2041475
  have hstable : (prefixWord ++ tailWord_2041475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041475).length < 2 ^ (prefixWord ++ tailWord_2041475).sum := by decide
  have hdescent : baseEnd_2041475 < baseStart_2041475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041519 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 2, 4, 2]
def baseStart_2041519 : Nat := 118140960795 + 2041519 * 2 ^ 59
def prefixEnd_2041519 : Nat := 4983230072969 + 3 ^ 40 * 2041519 * 2
def baseEnd_2041519 : Nat := 1048280512286303281223731

theorem tailTrace_2041519 : CollatzResearch.WordTrace tailWord_2041519 prefixEnd_2041519 1048280512286303281223731 := by
  unfold tailWord_2041519
  simp only [CollatzResearch.WordTrace]
  refine ⟨74460315090932801531775611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49640210060621867687850407 74460315090932801531775611)
  ·
    refine ⟨111690472636399202297663417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74460315090932801531775611 111690472636399202297663417)
    ·
      refine ⟨83767854477299401723247563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111690472636399202297663417 83767854477299401723247563)
      ·
        refine ⟨125651781715949102584871345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83767854477299401723247563 125651781715949102584871345)
        ·
          refine ⟨94238836286961826938653509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125651781715949102584871345 94238836286961826938653509)
          ·
            refine ⟨17669781803805342550997533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94238836286961826938653509 17669781803805342550997533)
            ·
              refine ⟨6626168176427003456624075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17669781803805342550997533 6626168176427003456624075)
              ·
                refine ⟨9939252264640505184936113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626168176427003456624075 9939252264640505184936113)
                ·
                  refine ⟨7454439198480378888702085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939252264640505184936113 7454439198480378888702085)
                  ·
                    refine ⟨1397707349715071041631641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7454439198480378888702085 1397707349715071041631641)
                    ·
                      refine ⟨1048280512286303281223731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397707349715071041631641 1048280512286303281223731)
                      ·
                        rfl

theorem cell23_2041519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 4, 2].length) (baseStart_2041519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041519 prefixEnd_2041519 := by exact prefixLift 2041519
  have htrace : WordTrace (prefixWord ++ tailWord_2041519) baseStart_2041519 baseEnd_2041519 := by
    simpa [prefixWord, tailWord_2041519, baseEnd_2041519] using wordTrace_append hprefix tailTrace_2041519
  have hstable : (prefixWord ++ tailWord_2041519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041519).length < 2 ^ (prefixWord ++ tailWord_2041519).sum := by decide
  have hdescent : baseEnd_2041519 < baseStart_2041519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041562 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_2041562 : Nat := 118140960795 + 2041562 * 2 ^ 59
def prefixEnd_2041562 : Nat := 4983230072969 + 3 ^ 40 * 2041562 * 2
def baseEnd_2041562 : Nat := 1048302591954446612986033

theorem tailTrace_2041562 : CollatzResearch.WordTrace tailWord_2041562 prefixEnd_2041562 1048302591954446612986033 := by
  unfold tailWord_2041562
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615470857444254968897735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49641255619851346583727293 18615470857444254968897735)
  ·
    refine ⟨27923206286166382453346603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18615470857444254968897735 27923206286166382453346603)
    ·
      refine ⟨41884809429249573680019905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27923206286166382453346603 41884809429249573680019905)
      ·
        refine ⟨31413607071937180260014929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41884809429249573680019905 31413607071937180260014929)
        ·
          refine ⟨23560205303952885195011197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31413607071937180260014929 23560205303952885195011197)
          ·
            refine ⟨8835076988982331948129199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23560205303952885195011197 8835076988982331948129199)
            ·
              refine ⟨13252615483473497922193799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835076988982331948129199 13252615483473497922193799)
              ·
                refine ⟨19878923225210246883290699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252615483473497922193799 19878923225210246883290699)
                ·
                  refine ⟨29818384837815370324936049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19878923225210246883290699 29818384837815370324936049)
                  ·
                    refine ⟨22363788628361527743702037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29818384837815370324936049 22363788628361527743702037)
                    ·
                      refine ⟨1048302591954446612986033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22363788628361527743702037 1048302591954446612986033)
                      ·
                        rfl

theorem cell23_2041562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_2041562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041562 prefixEnd_2041562 := by exact prefixLift 2041562
  have htrace : WordTrace (prefixWord ++ tailWord_2041562) baseStart_2041562 baseEnd_2041562 := by
    simpa [prefixWord, tailWord_2041562, baseEnd_2041562] using wordTrace_append hprefix tailTrace_2041562
  have hstable : (prefixWord ++ tailWord_2041562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041562).length < 2 ^ (prefixWord ++ tailWord_2041562).sum := by decide
  have hdescent : baseEnd_2041562 < baseStart_2041562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041576 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 6]
def baseStart_2041576 : Nat := 118140960795 + 2041576 * 2 ^ 59
def prefixEnd_2041576 : Nat := 4983230072969 + 3 ^ 40 * 2041576 * 2
def baseEnd_2041576 : Nat := 116478864520401062023441

theorem tailTrace_2041576 : CollatzResearch.WordTrace tailWord_2041576 prefixEnd_2041576 116478864520401062023441 := by
  unfold tailWord_2041576
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231197025863150133300291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49641596034484200177733721 37231197025863150133300291)
  ·
    refine ⟨55846795538794725199950437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37231197025863150133300291 55846795538794725199950437)
    ·
      refine ⟨10471274163524010974990707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55846795538794725199950437 10471274163524010974990707)
      ·
        refine ⟨15706911245286016462486061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471274163524010974990707 15706911245286016462486061)
        ·
          refine ⟨5890091716982256173432273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15706911245286016462486061 5890091716982256173432273)
          ·
            refine ⟨4417568787736692130074205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5890091716982256173432273 4417568787736692130074205)
            ·
              refine ⟨1656588295401259548777827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4417568787736692130074205 1656588295401259548777827)
              ·
                refine ⟨2484882443101889323166741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656588295401259548777827 2484882443101889323166741)
                ·
                  refine ⟨116478864520401062023441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2484882443101889323166741 116478864520401062023441)
                  ·
                    rfl

theorem cell23_2041576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 6].length) (baseStart_2041576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041576 prefixEnd_2041576 := by exact prefixLift 2041576
  have htrace : WordTrace (prefixWord ++ tailWord_2041576) baseStart_2041576 baseEnd_2041576 := by
    simpa [prefixWord, tailWord_2041576, baseEnd_2041576] using wordTrace_append hprefix tailTrace_2041576
  have hstable : (prefixWord ++ tailWord_2041576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041576).length < 2 ^ (prefixWord ++ tailWord_2041576).sum := by decide
  have hdescent : baseEnd_2041576 < baseStart_2041576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041579 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 1, 5, 2]
def baseStart_2041579 : Nat := 118140960795 + 2041579 * 2 ^ 59
def prefixEnd_2041579 : Nat := 4983230072969 + 3 ^ 40 * 2041579 * 2
def baseEnd_2041579 : Nat := 1048311321125573046473455

theorem tailTrace_2041579 : CollatzResearch.WordTrace tailWord_2041579 prefixEnd_2041579 1048311321125573046473455 := by
  unfold tailWord_2041579
  simp only [CollatzResearch.WordTrace]
  refine ⟨74462503470715431778959791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49641668980476954519306527 74462503470715431778959791)
  ·
    refine ⟨111693755206073147668439687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74462503470715431778959791 111693755206073147668439687)
    ·
      refine ⟨167540632809109721502659531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111693755206073147668439687 167540632809109721502659531)
      ·
        refine ⟨251310949213664582253989297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167540632809109721502659531 251310949213664582253989297)
        ·
          refine ⟨188483211910248436690491973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251310949213664582253989297 188483211910248436690491973)
          ·
            refine ⟨35340602233171581879467245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188483211910248436690491973 35340602233171581879467245)
            ·
              refine ⟨13252725837439343204800217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35340602233171581879467245 13252725837439343204800217)
              ·
                refine ⟨9939544378079507403600163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252725837439343204800217 9939544378079507403600163)
                ·
                  refine ⟨14909316567119261105400245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939544378079507403600163 14909316567119261105400245)
                  ·
                    refine ⟨1397748428167430728631273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14909316567119261105400245 1397748428167430728631273)
                    ·
                      refine ⟨1048311321125573046473455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397748428167430728631273 1048311321125573046473455)
                      ·
                        rfl

theorem cell23_2041579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 5, 2].length) (baseStart_2041579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041579 prefixEnd_2041579 := by exact prefixLift 2041579
  have htrace : WordTrace (prefixWord ++ tailWord_2041579) baseStart_2041579 baseEnd_2041579 := by
    simpa [prefixWord, tailWord_2041579, baseEnd_2041579] using wordTrace_append hprefix tailTrace_2041579
  have hstable : (prefixWord ++ tailWord_2041579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041579).length < 2 ^ (prefixWord ++ tailWord_2041579).sum := by decide
  have hdescent : baseEnd_2041579 < baseStart_2041579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041586 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_2041586 : Nat := 118140960795 + 2041586 * 2 ^ 59
def prefixEnd_2041586 : Nat := 4983230072969 + 3 ^ 40 * 2041586 * 2
def baseEnd_2041586 : Nat := 1048314915490154519085923

theorem tailTrace_2041586 : CollatzResearch.WordTrace tailWord_2041586 prefixEnd_2041586 1048314915490154519085923 := by
  unfold tailWord_2041586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615689695422517993616153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49641839187793381316309741 18615689695422517993616153)
  ·
    refine ⟨13961767271566888495212115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18615689695422517993616153 13961767271566888495212115)
    ·
      refine ⟨20942650907350332742818173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13961767271566888495212115 20942650907350332742818173)
      ·
        refine ⟨7853494090256374778556815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20942650907350332742818173 7853494090256374778556815)
        ·
          refine ⟨11780241135384562167835223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853494090256374778556815 11780241135384562167835223)
          ·
            refine ⟨17670361703076843251752835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780241135384562167835223 17670361703076843251752835)
            ·
              refine ⟨26505542554615264877629253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17670361703076843251752835 26505542554615264877629253)
              ·
                refine ⟨4969789228990362164555485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26505542554615264877629253 4969789228990362164555485)
                ·
                  refine ⟨1863670960871385811708307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4969789228990362164555485 1863670960871385811708307)
                  ·
                    refine ⟨2795506441307078717562461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863670960871385811708307 2795506441307078717562461)
                    ·
                      refine ⟨1048314915490154519085923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795506441307078717562461 1048314915490154519085923)
                      ·
                        rfl

theorem cell23_2041586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_2041586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041586 prefixEnd_2041586 := by exact prefixLift 2041586
  have htrace : WordTrace (prefixWord ++ tailWord_2041586) baseStart_2041586 baseEnd_2041586 := by
    simpa [prefixWord, tailWord_2041586, baseEnd_2041586] using wordTrace_append hprefix tailTrace_2041586
  have hstable : (prefixWord ++ tailWord_2041586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041586).length < 2 ^ (prefixWord ++ tailWord_2041586).sum := by decide
  have hdescent : baseEnd_2041586 < baseStart_2041586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041596 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_2041596 : Nat := 118140960795 + 2041596 * 2 ^ 59
def prefixEnd_2041596 : Nat := 4983230072969 + 3 ^ 40 * 2041596 * 2
def baseEnd_2041596 : Nat := 1048320050296699479960877

theorem tailTrace_2041596 : CollatzResearch.WordTrace tailWord_2041596 prefixEnd_2041596 1048320050296699479960877 := by
  unfold tailWord_2041596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231561755826921841164321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49642082341102562454885761 37231561755826921841164321)
  ·
    refine ⟨27923671316870191380873241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37231561755826921841164321 27923671316870191380873241)
    ·
      refine ⟨20942753487652643535654931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27923671316870191380873241 20942753487652643535654931)
      ·
        refine ⟨31414130231478965303482397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20942753487652643535654931 31414130231478965303482397)
        ·
          refine ⟨11780298836804611988805899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31414130231478965303482397 11780298836804611988805899)
          ·
            refine ⟨17670448255206917983208849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780298836804611988805899 17670448255206917983208849)
            ·
              refine ⟨13252836191405188487406637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670448255206917983208849 13252836191405188487406637)
              ·
                refine ⟨4969813571776945682777489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13252836191405188487406637 4969813571776945682777489)
                ·
                  refine ⟨3727360178832709262083117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969813571776945682777489 3727360178832709262083117)
                  ·
                    refine ⟨1397760067062265973281169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727360178832709262083117 1397760067062265973281169)
                    ·
                      refine ⟨1048320050296699479960877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397760067062265973281169 1048320050296699479960877)
                      ·
                        rfl

theorem cell23_2041596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_2041596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041596 prefixEnd_2041596 := by exact prefixLift 2041596
  have htrace : WordTrace (prefixWord ++ tailWord_2041596) baseStart_2041596 baseEnd_2041596 := by
    simpa [prefixWord, tailWord_2041596, baseEnd_2041596] using wordTrace_append hprefix tailTrace_2041596
  have hstable : (prefixWord ++ tailWord_2041596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041596).length < 2 ^ (prefixWord ++ tailWord_2041596).sum := by decide
  have hdescent : baseEnd_2041596 < baseStart_2041596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041603 : List Nat := [1, 1, 1, 3, 2, 2, 5, 3, 1, 1, 3]
def baseStart_2041603 : Nat := 118140960795 + 2041603 * 2 ^ 59
def prefixEnd_2041603 : Nat := 4983230072969 + 3 ^ 40 * 2041603 * 2
def baseEnd_2041603 : Nat := 1048323644661280952573345

theorem tailTrace_2041603 : CollatzResearch.WordTrace tailWord_2041603 prefixEnd_2041603 1048323644661280952573345 := by
  unfold tailWord_2041603
  simp only [CollatzResearch.WordTrace]
  refine ⟨74463378822628483877833463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49642252548418989251888975 74463378822628483877833463)
  ·
    refine ⟨111695068233942725816750195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74463378822628483877833463 111695068233942725816750195)
    ·
      refine ⟨167542602350914088725125293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111695068233942725816750195 167542602350914088725125293)
      ·
        refine ⟨62828475881592783271921985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167542602350914088725125293 62828475881592783271921985)
        ·
          refine ⟨47121356911194587453941489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62828475881592783271921985 47121356911194587453941489)
          ·
            refine ⟨35341017683395940590456117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47121356911194587453941489 35341017683395940590456117)
            ·
              refine ⟨3313220407818369430355261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35341017683395940590456117 3313220407818369430355261)
              ·
                refine ⟨1242457652931888536383223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3313220407818369430355261 1242457652931888536383223)
                ·
                  refine ⟨1863686479397832804574835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242457652931888536383223 1863686479397832804574835)
                  ·
                    refine ⟨2795529719096749206862253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1863686479397832804574835 2795529719096749206862253)
                    ·
                      refine ⟨1048323644661280952573345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795529719096749206862253 1048323644661280952573345)
                      ·
                        rfl

theorem cell23_2041603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_2041603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041603 prefixEnd_2041603 := by exact prefixLift 2041603
  have htrace : WordTrace (prefixWord ++ tailWord_2041603) baseStart_2041603 baseEnd_2041603 := by
    simpa [prefixWord, tailWord_2041603, baseEnd_2041603] using wordTrace_append hprefix tailTrace_2041603
  have hstable : (prefixWord ++ tailWord_2041603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041603).length < 2 ^ (prefixWord ++ tailWord_2041603).sum := by decide
  have hdescent : baseEnd_2041603 < baseStart_2041603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041663 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 1, 1, 5]
def baseStart_2041663 : Nat := 118140960795 + 2041663 * 2 ^ 59
def prefixEnd_2041663 : Nat := 4983230072969 + 3 ^ 40 * 2041663 * 2
def baseEnd_2041663 : Nat := 1048354453500550717823069

theorem tailTrace_2041663 : CollatzResearch.WordTrace tailWord_2041663 prefixEnd_2041663 1048354453500550717823069 := by
  unfold tailWord_2041663
  simp only [CollatzResearch.WordTrace]
  refine ⟨74465567202411114125017643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49643711468274076083345095 74465567202411114125017643)
  ·
    refine ⟨111698350803616671187526465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74465567202411114125017643 111698350803616671187526465)
    ·
      refine ⟨83773763102712503390644849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111698350803616671187526465 83773763102712503390644849)
      ·
        refine ⟨62830322327034377542983637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83773763102712503390644849 62830322327034377542983637)
        ·
          refine ⟨1472585679539868223663679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62830322327034377542983637 1472585679539868223663679)
          ·
            refine ⟨2208878519309802335495519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472585679539868223663679 2208878519309802335495519)
            ·
              refine ⟨3313317778964703503243279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208878519309802335495519 3313317778964703503243279)
              ·
                refine ⟨4969976668447055254864919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313317778964703503243279 4969976668447055254864919)
                ·
                  refine ⟨7454965002670582882297379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969976668447055254864919 7454965002670582882297379)
                  ·
                    refine ⟨11182447504005874323446069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7454965002670582882297379 11182447504005874323446069)
                    ·
                      refine ⟨1048354453500550717823069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11182447504005874323446069 1048354453500550717823069)
                      ·
                        rfl

theorem cell23_2041663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_2041663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041663 prefixEnd_2041663 := by exact prefixLift 2041663
  have htrace : WordTrace (prefixWord ++ tailWord_2041663) baseStart_2041663 baseEnd_2041663 := by
    simpa [prefixWord, tailWord_2041663, baseEnd_2041663] using wordTrace_append hprefix tailTrace_2041663
  have hstable : (prefixWord ++ tailWord_2041663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041663).length < 2 ^ (prefixWord ++ tailWord_2041663).sum := by decide
  have hdescent : baseEnd_2041663 < baseStart_2041663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041670 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_2041670 : Nat := 118140960795 + 2041670 * 2 ^ 59
def prefixEnd_2041670 : Nat := 4983230072969 + 3 ^ 40 * 2041670 * 2
def baseEnd_2041670 : Nat := 349452682621710730145179

theorem tailTrace_2041670 : CollatzResearch.WordTrace tailWord_2041670 prefixEnd_2041670 349452682621710730145179 := by
  unfold tailWord_2041670
  simp only [CollatzResearch.WordTrace]
  refine ⟨2327056953543304822516327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49643881675590502880348309 2327056953543304822516327)
  ·
    refine ⟨3490585430314957233774491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2327056953543304822516327 3490585430314957233774491)
    ·
      refine ⟨5235878145472435850661737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3490585430314957233774491 5235878145472435850661737)
      ·
        refine ⟨3926908609104326887996303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5235878145472435850661737 3926908609104326887996303)
        ·
          refine ⟨5890362913656490331994455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926908609104326887996303 5890362913656490331994455)
          ·
            refine ⟨8835544370484735497991683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890362913656490331994455 8835544370484735497991683)
            ·
              refine ⟨13253316555727103246987525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835544370484735497991683 13253316555727103246987525)
              ·
                refine ⟨2484996854198831858810161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13253316555727103246987525 2484996854198831858810161)
                ·
                  refine ⟨1863747640649123894107621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2484996854198831858810161 1863747640649123894107621)
                  ·
                    refine ⟨349452682621710730145179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863747640649123894107621 349452682621710730145179)
                    ·
                      rfl

theorem cell23_2041670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_2041670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041670 prefixEnd_2041670 := by exact prefixLift 2041670
  have htrace : WordTrace (prefixWord ++ tailWord_2041670) baseStart_2041670 baseEnd_2041670 := by
    simpa [prefixWord, tailWord_2041670, baseEnd_2041670] using wordTrace_append hprefix tailTrace_2041670
  have hstable : (prefixWord ++ tailWord_2041670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041670).length < 2 ^ (prefixWord ++ tailWord_2041670).sum := by decide
  have hdescent : baseEnd_2041670 < baseStart_2041670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041703 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_2041703 : Nat := 118140960795 + 2041703 * 2 ^ 59
def prefixEnd_2041703 : Nat := 4983230072969 + 3 ^ 40 * 2041703 * 2
def baseEnd_2041703 : Nat := 1048374992726730561322885

theorem tailTrace_2041703 : CollatzResearch.WordTrace tailWord_2041703 prefixEnd_2041703 1048374992726730561322885 := by
  unfold tailWord_2041703
  simp only [CollatzResearch.WordTrace]
  refine ⟨74467026122266200956473763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49644684081510800637649175 74467026122266200956473763)
  ·
    refine ⟨111700539183399301434710645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74467026122266200956473763 111700539183399301434710645)
    ·
      refine ⟨10471925548443684509504123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111700539183399301434710645 10471925548443684509504123)
      ·
        refine ⟨15707888322665526764256185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471925548443684509504123 15707888322665526764256185)
        ·
          refine ⟨11780916241999145073192139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15707888322665526764256185 11780916241999145073192139)
          ·
            refine ⟨17671374362998717609788209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780916241999145073192139 17671374362998717609788209)
            ·
              refine ⟨13253530772249038207341157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17671374362998717609788209 13253530772249038207341157)
              ·
                refine ⟨2485037019796694663876467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13253530772249038207341157 2485037019796694663876467)
                ·
                  refine ⟨3727555529695041995814701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485037019796694663876467 3727555529695041995814701)
                  ·
                    refine ⟨1397833323635640748430513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727555529695041995814701 1397833323635640748430513)
                    ·
                      refine ⟨1048374992726730561322885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397833323635640748430513 1048374992726730561322885)
                      ·
                        rfl

theorem cell23_2041703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_2041703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041703 prefixEnd_2041703 := by exact prefixLift 2041703
  have htrace : WordTrace (prefixWord ++ tailWord_2041703) baseStart_2041703 baseEnd_2041703 := by
    simpa [prefixWord, tailWord_2041703, baseEnd_2041703] using wordTrace_append hprefix tailTrace_2041703
  have hstable : (prefixWord ++ tailWord_2041703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041703).length < 2 ^ (prefixWord ++ tailWord_2041703).sum := by decide
  have hdescent : baseEnd_2041703 < baseStart_2041703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041733 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_2041733 : Nat := 118140960795 + 2041733 * 2 ^ 59
def prefixEnd_2041733 : Nat := 4983230072969 + 3 ^ 40 * 2041733 * 2
def baseEnd_2041733 : Nat := 1048390397146365443947747

theorem tailTrace_2041733 : CollatzResearch.WordTrace tailWord_2041733 prefixEnd_2041733 1048390397146365443947747 := by
  unfold tailWord_2041733
  simp only [CollatzResearch.WordTrace]
  refine ⟨74468120312157516080065853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49645413541438344053377235 74468120312157516080065853)
  ·
    refine ⟨27925545117059068530024695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74468120312157516080065853 27925545117059068530024695)
    ·
      refine ⟨41888317675588602795037043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27925545117059068530024695 41888317675588602795037043)
      ·
        refine ⟨62832476513382904192555565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41888317675588602795037043 62832476513382904192555565)
        ·
          refine ⟨23562178692518589072208337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62832476513382904192555565 23562178692518589072208337)
          ·
            refine ⟨17671634019388941804156253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23562178692518589072208337 17671634019388941804156253)
            ·
              refine ⟨6626862757270853176558595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17671634019388941804156253 6626862757270853176558595)
              ·
                refine ⟨9940294135906279764837893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626862757270853176558595 9940294135906279764837893)
                ·
                  refine ⟨1863805150482427455907105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9940294135906279764837893 1863805150482427455907105)
                  ·
                    refine ⟨1397853862861820591930329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863805150482427455907105 1397853862861820591930329)
                    ·
                      refine ⟨1048390397146365443947747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397853862861820591930329 1048390397146365443947747)
                      ·
                        rfl

theorem cell23_2041733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_2041733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041733 prefixEnd_2041733 := by exact prefixLift 2041733
  have htrace : WordTrace (prefixWord ++ tailWord_2041733) baseStart_2041733 baseEnd_2041733 := by
    simpa [prefixWord, tailWord_2041733, baseEnd_2041733] using wordTrace_append hprefix tailTrace_2041733
  have hstable : (prefixWord ++ tailWord_2041733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041733).length < 2 ^ (prefixWord ++ tailWord_2041733).sum := by decide
  have hdescent : baseEnd_2041733 < baseStart_2041733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041756 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 7]
def baseStart_2041756 : Nat := 118140960795 + 2041756 * 2 ^ 59
def prefixEnd_2041756 : Nat := 4983230072969 + 3 ^ 40 * 2041756 * 2
def baseEnd_2041756 : Nat := 116489134133490983773349

theorem tailTrace_2041756 : CollatzResearch.WordTrace tailWord_2041756 prefixEnd_2041756 116489134133490983773349 := by
  unfold tailWord_2041756
  simp only [CollatzResearch.WordTrace]
  refine ⟨37234479595537095504076561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49645972794049460672102081 37234479595537095504076561)
  ·
    refine ⟨27925859696652821628057421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37234479595537095504076561 27925859696652821628057421)
    ·
      refine ⟨10472197386244808110521533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27925859696652821628057421 10472197386244808110521533)
      ·
        refine ⟨3927074019841803041445575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10472197386244808110521533 3927074019841803041445575)
        ·
          refine ⟨5890611029762704562168363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927074019841803041445575 5890611029762704562168363)
          ·
            refine ⟨8835916544644056843252545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890611029762704562168363 8835916544644056843252545)
            ·
              refine ⟨6626937408483042632439409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8835916544644056843252545 6626937408483042632439409)
              ·
                refine ⟨4970203056362281974329557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6626937408483042632439409 4970203056362281974329557)
                ·
                  refine ⟨116489134133490983773349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4970203056362281974329557 116489134133490983773349)
                  ·
                    rfl

theorem cell23_2041756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_2041756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041756 prefixEnd_2041756 := by exact prefixLift 2041756
  have htrace : WordTrace (prefixWord ++ tailWord_2041756) baseStart_2041756 baseEnd_2041756 := by
    simpa [prefixWord, tailWord_2041756, baseEnd_2041756] using wordTrace_append hprefix tailTrace_2041756
  have hstable : (prefixWord ++ tailWord_2041756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041756).length < 2 ^ (prefixWord ++ tailWord_2041756).sum := by decide
  have hdescent : baseEnd_2041756 < baseStart_2041756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041779 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5]
def baseStart_2041779 : Nat := 118140960795 + 2041779 * 2 ^ 59
def prefixEnd_2041779 : Nat := 4983230072969 + 3 ^ 40 * 2041779 * 2
def baseEnd_2041779 : Nat := 1048414017256472263972535

theorem tailTrace_2041779 : CollatzResearch.WordTrace tailWord_2041779 prefixEnd_2041779 1048414017256472263972535 := by
  unfold tailWord_2041779
  simp only [CollatzResearch.WordTrace]
  refine ⟨74469798069990865936240391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49646532046660577290826927 74469798069990865936240391)
  ·
    refine ⟨111704697104986298904360587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74469798069990865936240391 111704697104986298904360587)
    ·
      refine ⟨167557045657479448356540881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111704697104986298904360587 167557045657479448356540881)
      ·
        refine ⟨125667784243109586267405661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167557045657479448356540881 125667784243109586267405661)
        ·
          refine ⟨47125419091166094850277123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125667784243109586267405661 47125419091166094850277123)
          ·
            refine ⟨70688128636749142275415685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47125419091166094850277123 70688128636749142275415685)
            ·
              refine ⟨13254024119390464176640441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70688128636749142275415685 13254024119390464176640441)
              ·
                refine ⟨9940518089542848132480331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13254024119390464176640441 9940518089542848132480331)
                ·
                  refine ⟨14910777134314272198720497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940518089542848132480331 14910777134314272198720497)
                  ·
                    refine ⟨11183082850735704149040373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14910777134314272198720497 11183082850735704149040373)
                    ·
                      refine ⟨1048414017256472263972535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11183082850735704149040373 1048414017256472263972535)
                      ·
                        rfl

theorem cell23_2041779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_2041779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041779 prefixEnd_2041779 := by exact prefixLift 2041779
  have htrace : WordTrace (prefixWord ++ tailWord_2041779) baseStart_2041779 baseEnd_2041779 := by
    simpa [prefixWord, tailWord_2041779, baseEnd_2041779] using wordTrace_append hprefix tailTrace_2041779
  have hstable : (prefixWord ++ tailWord_2041779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041779).length < 2 ^ (prefixWord ++ tailWord_2041779).sum := by decide
  have hdescent : baseEnd_2041779 < baseStart_2041779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041790 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_2041790 : Nat := 118140960795 + 2041790 * 2 ^ 59
def prefixEnd_2041790 : Nat := 4983230072969 + 3 ^ 40 * 2041790 * 2
def baseEnd_2041790 : Nat := 116491073949296857881665

theorem tailTrace_2041790 : CollatzResearch.WordTrace tailWord_2041790 prefixEnd_2041790 116491073949296857881665 := by
  unfold tailWord_2041790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308774909118876851861353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49646799515300676543260549 9308774909118876851861353)
  ·
    refine ⟨6981581181839157638896015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9308774909118876851861353 6981581181839157638896015)
    ·
      refine ⟨10472371772758736458344023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6981581181839157638896015 10472371772758736458344023)
      ·
        refine ⟨15708557659138104687516035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472371772758736458344023 15708557659138104687516035)
        ·
          refine ⟨23562836488707157031274053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15708557659138104687516035 23562836488707157031274053)
          ·
            refine ⟨4418031841632591943363885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23562836488707157031274053 4418031841632591943363885)
            ·
              refine ⟨1656761940612221978761457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4418031841632591943363885 1656761940612221978761457)
              ·
                refine ⟨1242571455459166484071093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656761940612221978761457 1242571455459166484071093)
                ·
                  refine ⟨116491073949296857881665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242571455459166484071093 116491073949296857881665)
                  ·
                    rfl

theorem cell23_2041790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_2041790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041790 prefixEnd_2041790 := by exact prefixLift 2041790
  have htrace : WordTrace (prefixWord ++ tailWord_2041790) baseStart_2041790 baseEnd_2041790 := by
    simpa [prefixWord, tailWord_2041790, baseEnd_2041790] using wordTrace_append hprefix tailTrace_2041790
  have hstable : (prefixWord ++ tailWord_2041790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041790).length < 2 ^ (prefixWord ++ tailWord_2041790).sum := by decide
  have hdescent : baseEnd_2041790 < baseStart_2041790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041806 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_2041806 : Nat := 118140960795 + 2041806 * 2 ^ 59
def prefixEnd_2041806 : Nat := 4983230072969 + 3 ^ 40 * 2041806 * 2
def baseEnd_2041806 : Nat := 1048427881234143658334911

theorem tailTrace_2041806 : CollatzResearch.WordTrace tailWord_2041806 prefixEnd_2041806 1048427881234143658334911 := by
  unfold tailWord_2041806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308847855111631193434159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49647188560595366364982181 9308847855111631193434159)
  ·
    refine ⟨13963271782667446790151239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9308847855111631193434159 13963271782667446790151239)
    ·
      refine ⟨20944907674001170185226859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13963271782667446790151239 20944907674001170185226859)
      ·
        refine ⟨31417361511001755277840289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20944907674001170185226859 31417361511001755277840289)
        ·
          refine ⟨23563021133251316458380217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31417361511001755277840289 23563021133251316458380217)
          ·
            refine ⟨17672265849938487343785163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23563021133251316458380217 17672265849938487343785163)
            ·
              refine ⟨26508398774907731015677745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17672265849938487343785163 26508398774907731015677745)
              ·
                refine ⟨19881299081180798261758309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26508398774907731015677745 19881299081180798261758309)
                ·
                  refine ⟨3727743577721399674079683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19881299081180798261758309 3727743577721399674079683)
                  ·
                    refine ⟨5591615366582099511119525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727743577721399674079683 5591615366582099511119525)
                    ·
                      refine ⟨1048427881234143658334911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5591615366582099511119525 1048427881234143658334911)
                      ·
                        rfl

theorem cell23_2041806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_2041806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041806 prefixEnd_2041806 := by exact prefixLift 2041806
  have htrace : WordTrace (prefixWord ++ tailWord_2041806) baseStart_2041806 baseEnd_2041806 := by
    simpa [prefixWord, tailWord_2041806, baseEnd_2041806] using wordTrace_append hprefix tailTrace_2041806
  have hstable : (prefixWord ++ tailWord_2041806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041806).length < 2 ^ (prefixWord ++ tailWord_2041806).sum := by decide
  have hdescent : baseEnd_2041806 < baseStart_2041806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041816 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_2041816 : Nat := 118140960795 + 2041816 * 2 ^ 59
def prefixEnd_2041816 : Nat := 4983230072969 + 3 ^ 40 * 2041816 * 2
def baseEnd_2041816 : Nat := 349477672013562873069955

theorem tailTrace_2041816 : CollatzResearch.WordTrace tailWord_2041816 prefixEnd_2041816 349477672013562873069955 := by
  unfold tailWord_2041816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37235573785428410627668651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49647431713904547503558201 37235573785428410627668651)
  ·
    refine ⟨55853360678142615941502977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37235573785428410627668651 55853360678142615941502977)
    ·
      refine ⟨41890020508606961956127233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55853360678142615941502977 41890020508606961956127233)
      ·
        refine ⟨31417515381455221467095425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41890020508606961956127233 31417515381455221467095425)
        ·
          refine ⟨23563136536091416100321569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31417515381455221467095425 23563136536091416100321569)
          ·
            refine ⟨17672352402068562075241177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23563136536091416100321569 17672352402068562075241177)
            ·
              refine ⟨13254264301551421556430883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17672352402068562075241177 13254264301551421556430883)
              ·
                refine ⟨19881396452327132334646325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254264301551421556430883 19881396452327132334646325)
                ·
                  refine ⟨1863880917405668656373093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19881396452327132334646325 1863880917405668656373093)
                  ·
                    refine ⟨349477672013562873069955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863880917405668656373093 349477672013562873069955)
                    ·
                      rfl

theorem cell23_2041816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_2041816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041816 prefixEnd_2041816 := by exact prefixLift 2041816
  have htrace : WordTrace (prefixWord ++ tailWord_2041816) baseStart_2041816 baseEnd_2041816 := by
    simpa [prefixWord, tailWord_2041816, baseEnd_2041816] using wordTrace_append hprefix tailTrace_2041816
  have hstable : (prefixWord ++ tailWord_2041816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041816).length < 2 ^ (prefixWord ++ tailWord_2041816).sum := by decide
  have hdescent : baseEnd_2041816 < baseStart_2041816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041823 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4]
def baseStart_2041823 : Nat := 118140960795 + 2041823 * 2 ^ 59
def prefixEnd_2041823 : Nat := 4983230072969 + 3 ^ 40 * 2041823 * 2
def baseEnd_2041823 : Nat := 1048436610405270091822333

theorem tailTrace_2041823 : CollatzResearch.WordTrace tailWord_2041823 prefixEnd_2041823 1048436610405270091822333 := by
  unfold tailWord_2041823
  simp only [CollatzResearch.WordTrace]
  refine ⟨74471402881831461450842123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49647601921220974300561415 74471402881831461450842123)
  ·
    refine ⟨111707104322747192176263185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74471402881831461450842123 111707104322747192176263185)
    ·
      refine ⟨83780328242060394132197389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111707104322747192176263185 83780328242060394132197389)
      ·
        refine ⟨31417623090772647799574021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83780328242060394132197389 31417623090772647799574021)
        ·
          refine ⟨5890804329519871462420129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31417623090772647799574021 5890804329519871462420129)
          ·
            refine ⟨4418103247139903596815097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5890804329519871462420129 4418103247139903596815097)
            ·
              refine ⟨3313577435354927697611323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418103247139903596815097 3313577435354927697611323)
              ·
                refine ⟨4970366153032391546416985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313577435354927697611323 4970366153032391546416985)
                ·
                  refine ⟨3727774614774293659812739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970366153032391546416985 3727774614774293659812739)
                  ·
                    refine ⟨5591661922161440489719109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727774614774293659812739 5591661922161440489719109)
                    ·
                      refine ⟨1048436610405270091822333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5591661922161440489719109 1048436610405270091822333)
                      ·
                        rfl

theorem cell23_2041823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_2041823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041823 prefixEnd_2041823 := by exact prefixLift 2041823
  have htrace : WordTrace (prefixWord ++ tailWord_2041823) baseStart_2041823 baseEnd_2041823 := by
    simpa [prefixWord, tailWord_2041823, baseEnd_2041823] using wordTrace_append hprefix tailTrace_2041823
  have hstable : (prefixWord ++ tailWord_2041823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041823).length < 2 ^ (prefixWord ++ tailWord_2041823).sum := by decide
  have hdescent : baseEnd_2041823 < baseStart_2041823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041877 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_2041877 : Nat := 118140960795 + 2041877 * 2 ^ 59
def prefixEnd_2041877 : Nat := 4983230072969 + 3 ^ 40 * 2041877 * 2
def baseEnd_2041877 : Nat := 1048464338360612880547085

theorem tailTrace_2041877 : CollatzResearch.WordTrace tailWord_2041877 prefixEnd_2041877 1048464338360612880547085 := by
  unfold tailWord_2041877
  simp only [CollatzResearch.WordTrace]
  refine ⟨74473372423635828673307885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49648914949090552448871923 74473372423635828673307885)
  ·
    refine ⟨27927514658863435752490457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74473372423635828673307885 27927514658863435752490457)
    ·
      refine ⟨20945635994147576814367843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27927514658863435752490457 20945635994147576814367843)
      ·
        refine ⟨31418453991221365221551765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20945635994147576814367843 31418453991221365221551765)
        ·
          refine ⟨1472740030838501494760239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31418453991221365221551765 1472740030838501494760239)
          ·
            refine ⟨2209110046257752242140359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472740030838501494760239 2209110046257752242140359)
            ·
              refine ⟨3313665069386628363210539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209110046257752242140359 3313665069386628363210539)
              ·
                refine ⟨4970497604079942544815809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313665069386628363210539 4970497604079942544815809)
                ·
                  refine ⟨3727873203059956908611857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970497604079942544815809 3727873203059956908611857)
                  ·
                    refine ⟨2795904902294967681458893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3727873203059956908611857 2795904902294967681458893)
                    ·
                      refine ⟨1048464338360612880547085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2795904902294967681458893 1048464338360612880547085)
                      ·
                        rfl

theorem cell23_2041877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_2041877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041877 prefixEnd_2041877 := by exact prefixLift 2041877
  have htrace : WordTrace (prefixWord ++ tailWord_2041877) baseStart_2041877 baseEnd_2041877 := by
    simpa [prefixWord, tailWord_2041877, baseEnd_2041877] using wordTrace_append hprefix tailTrace_2041877
  have hstable : (prefixWord ++ tailWord_2041877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041877).length < 2 ^ (prefixWord ++ tailWord_2041877).sum := by decide
  have hdescent : baseEnd_2041877 < baseStart_2041877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041883 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 2, 3, 2]
def baseStart_2041883 : Nat := 118140960795 + 2041883 * 2 ^ 59
def prefixEnd_2041883 : Nat := 4983230072969 + 3 ^ 40 * 2041883 * 2
def baseEnd_2041883 : Nat := 1048467419244539857072057

theorem tailTrace_2041883 : CollatzResearch.WordTrace tailWord_2041883 prefixEnd_2041883 1048467419244539857072057 := by
  unfold tailWord_2041883
  simp only [CollatzResearch.WordTrace]
  refine ⟨74473591261614091698026303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49649060841076061132017535 74473591261614091698026303)
  ·
    refine ⟨111710386892421137547039455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74473591261614091698026303 111710386892421137547039455)
    ·
      refine ⟨167565580338631706320559183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111710386892421137547039455 167565580338631706320559183)
      ·
        refine ⟨251348370507947559480838775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167565580338631706320559183 251348370507947559480838775)
        ·
          refine ⟨377022555761921339221258163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251348370507947559480838775 377022555761921339221258163)
          ·
            refine ⟨565533833642882008831887245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377022555761921339221258163 565533833642882008831887245)
            ·
              refine ⟨212075187616080753311957717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565533833642882008831887245 212075187616080753311957717)
              ·
                refine ⟨4970512209751892655749009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 212075187616080753311957717 4970512209751892655749009)
                ·
                  refine ⟨3727884157313919491811757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970512209751892655749009 3727884157313919491811757)
                  ·
                    refine ⟨1397956558992719809429409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3727884157313919491811757 1397956558992719809429409)
                    ·
                      refine ⟨1048467419244539857072057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397956558992719809429409 1048467419244539857072057)
                      ·
                        rfl

theorem cell23_2041883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 3, 2].length) (baseStart_2041883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041883 prefixEnd_2041883 := by exact prefixLift 2041883
  have htrace : WordTrace (prefixWord ++ tailWord_2041883) baseStart_2041883 baseEnd_2041883 := by
    simpa [prefixWord, tailWord_2041883, baseEnd_2041883] using wordTrace_append hprefix tailTrace_2041883
  have hstable : (prefixWord ++ tailWord_2041883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041883).length < 2 ^ (prefixWord ++ tailWord_2041883).sum := by decide
  have hdescent : baseEnd_2041883 < baseStart_2041883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041893 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_2041893 : Nat := 118140960795 + 2041893 * 2 ^ 59
def prefixEnd_2041893 : Nat := 4983230072969 + 3 ^ 40 * 2041893 * 2
def baseEnd_2041893 : Nat := 349490851350361605982337

theorem tailTrace_2041893 : CollatzResearch.WordTrace tailWord_2041893 prefixEnd_2041893 349490851350361605982337 := by
  unfold tailWord_2041893
  simp only [CollatzResearch.WordTrace]
  refine ⟨74473955991577863405890333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49649303994385242270593555 74473955991577863405890333)
  ·
    refine ⟨27927733496841698777208875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74473955991577863405890333 27927733496841698777208875)
    ·
      refine ⟨41891600245262548165813313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27927733496841698777208875 41891600245262548165813313)
      ·
        refine ⟨31418700183946911124359985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41891600245262548165813313 31418700183946911124359985)
        ·
          refine ⟨23564025137960183343269989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31418700183946911124359985 23564025137960183343269989)
          ·
            refine ⟨4418254713367534376863123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23564025137960183343269989 4418254713367534376863123)
            ·
              refine ⟨6627382070051301565294685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418254713367534376863123 6627382070051301565294685)
              ·
                refine ⟨2485268276269238086985507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6627382070051301565294685 2485268276269238086985507)
                ·
                  refine ⟨3727902414403857130478261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485268276269238086985507 3727902414403857130478261)
                  ·
                    refine ⟨349490851350361605982337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3727902414403857130478261 349490851350361605982337)
                    ·
                      rfl

theorem cell23_2041893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_2041893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041893 prefixEnd_2041893 := by exact prefixLift 2041893
  have htrace : WordTrace (prefixWord ++ tailWord_2041893) baseStart_2041893 baseEnd_2041893 := by
    simpa [prefixWord, tailWord_2041893, baseEnd_2041893] using wordTrace_append hprefix tailTrace_2041893
  have hstable : (prefixWord ++ tailWord_2041893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041893).length < 2 ^ (prefixWord ++ tailWord_2041893).sum := by decide
  have hdescent : baseEnd_2041893 < baseStart_2041893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041933 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_2041933 : Nat := 118140960795 + 2041933 * 2 ^ 59
def prefixEnd_2041933 : Nat := 4983230072969 + 3 ^ 40 * 2041933 * 2
def baseEnd_2041933 : Nat := 1048493093277264661446827

theorem tailTrace_2041933 : CollatzResearch.WordTrace tailWord_2041933 prefixEnd_2041933 1048493093277264661446827 := by
  unfold tailWord_2041933
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475414911432950237346453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49650276607621966824897635 74475414911432950237346453)
  ·
    refine ⟨3491035073973419542375615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74475414911432950237346453 3491035073973419542375615)
    ·
      refine ⟨5236552610960129313563423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491035073973419542375615 5236552610960129313563423)
      ·
        refine ⟨7854828916440193970345135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236552610960129313563423 7854828916440193970345135)
        ·
          refine ⟨11782243374660290955517703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854828916440193970345135 11782243374660290955517703)
          ·
            refine ⟨17673365061990436433276555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782243374660290955517703 17673365061990436433276555)
            ·
              refine ⟨26510047592985654649914833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17673365061990436433276555 26510047592985654649914833)
              ·
                refine ⟨19882535694739240987436125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26510047592985654649914833 19882535694739240987436125)
                ·
                  refine ⟨7455950885527215370288547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19882535694739240987436125 7455950885527215370288547)
                  ·
                    refine ⟨11183926328290823055432821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455950885527215370288547 11183926328290823055432821)
                    ·
                      refine ⟨1048493093277264661446827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11183926328290823055432821 1048493093277264661446827)
                      ·
                        rfl

theorem cell23_2041933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_2041933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041933 prefixEnd_2041933 := by exact prefixLift 2041933
  have htrace : WordTrace (prefixWord ++ tailWord_2041933) baseStart_2041933 baseEnd_2041933 := by
    simpa [prefixWord, tailWord_2041933, baseEnd_2041933] using wordTrace_append hprefix tailTrace_2041933
  have hstable : (prefixWord ++ tailWord_2041933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041933).length < 2 ^ (prefixWord ++ tailWord_2041933).sum := by decide
  have hdescent : baseEnd_2041933 < baseStart_2041933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041974 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 2, 4]
def baseStart_2041974 : Nat := 118140960795 + 2041974 * 2 ^ 59
def prefixEnd_2041974 : Nat := 4983230072969 + 3 ^ 40 * 2041974 * 2
def baseEnd_2041974 : Nat := 349504715328033000344713

theorem tailTrace_2041974 : CollatzResearch.WordTrace tailWord_2041974 prefixEnd_2041974 349504715328033000344713 := by
  unfold tailWord_2041974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654806894017775889974311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49651273536189609493059317 4654806894017775889974311)
  ·
    refine ⟨6982210341026663834961467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4654806894017775889974311 6982210341026663834961467)
    ·
      refine ⟨10473315511539995752442201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982210341026663834961467 10473315511539995752442201)
      ·
        refine ⟨7854986633654996814331651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10473315511539995752442201 7854986633654996814331651)
        ·
          refine ⟨11782479950482495221497477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854986633654996814331651 11782479950482495221497477)
          ·
            refine ⟨2209214990715467854030777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11782479950482495221497477 2209214990715467854030777)
            ·
              refine ⟨1656911243036600890523083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209214990715467854030777 1656911243036600890523083)
              ·
                refine ⟨2485366864554901335784625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656911243036600890523083 2485366864554901335784625)
                ·
                  refine ⟨1864025148416176001838469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485366864554901335784625 1864025148416176001838469)
                  ·
                    refine ⟨349504715328033000344713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864025148416176001838469 349504715328033000344713)
                    ·
                      rfl

theorem cell23_2041974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_2041974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041974 prefixEnd_2041974 := by exact prefixLift 2041974
  have htrace : WordTrace (prefixWord ++ tailWord_2041974) baseStart_2041974 baseEnd_2041974 := by
    simpa [prefixWord, tailWord_2041974, baseEnd_2041974] using wordTrace_append hprefix tailTrace_2041974
  have hstable : (prefixWord ++ tailWord_2041974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041974).length < 2 ^ (prefixWord ++ tailWord_2041974).sum := by decide
  have hdescent : baseEnd_2041974 < baseStart_2041974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041996 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_2041996 : Nat := 118140960795 + 2041996 * 2 ^ 59
def prefixEnd_2041996 : Nat := 4983230072969 + 3 ^ 40 * 2041996 * 2
def baseEnd_2041996 : Nat := 349508480852832638319679

theorem tailTrace_2041996 : CollatzResearch.WordTrace tailWord_2041996 prefixEnd_2041996 349508480852832638319679 := by
  unfold tailWord_2041996
  simp only [CollatzResearch.WordTrace]
  refine ⟨37238856355102355998444921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49651808473469807997926561 37238856355102355998444921)
  ·
    refine ⟨27929142266326766998833691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37238856355102355998444921 27929142266326766998833691)
    ·
      refine ⟨41893713399490150498250537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27929142266326766998833691 41893713399490150498250537)
      ·
        refine ⟨31420285049617612873687903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41893713399490150498250537 31420285049617612873687903)
        ·
          refine ⟨47130427574426419310531855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31420285049617612873687903 47130427574426419310531855)
          ·
            refine ⟨70695641361639628965797783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47130427574426419310531855 70695641361639628965797783)
            ·
              refine ⟨106043462042459443448696675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70695641361639628965797783 106043462042459443448696675)
              ·
                refine ⟨159065193063689165173045013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106043462042459443448696675 159065193063689165173045013)
                ·
                  refine ⟨7456180924860429617486485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159065193063689165173045013 7456180924860429617486485)
                  ·
                    refine ⟨349508480852832638319679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7456180924860429617486485 349508480852832638319679)
                    ·
                      rfl

theorem cell23_2041996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_2041996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041996 prefixEnd_2041996 := by exact prefixLift 2041996
  have htrace : WordTrace (prefixWord ++ tailWord_2041996) baseStart_2041996 baseEnd_2041996 := by
    simpa [prefixWord, tailWord_2041996, baseEnd_2041996] using wordTrace_append hprefix tailTrace_2041996
  have hstable : (prefixWord ++ tailWord_2041996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041996).length < 2 ^ (prefixWord ++ tailWord_2041996).sum := by decide
  have hdescent : baseEnd_2041996 < baseStart_2041996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042073 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_2042073 : Nat := 118140960795 + 2042073 * 2 ^ 59
def prefixEnd_2042073 : Nat := 4983230072969 + 3 ^ 40 * 2042073 * 2
def baseEnd_2042073 : Nat := 349521660189631371232061

theorem tailTrace_2042073 : CollatzResearch.WordTrace tailWord_2042073 prefixEnd_2042073 349521660189631371232061 := by
  unfold tailWord_2042073
  simp only [CollatzResearch.WordTrace]
  refine ⟨74480521130925754147442873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49653680753950502764961915 74480521130925754147442873)
  ·
    refine ⟨55860390848194315610582155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74480521130925754147442873 55860390848194315610582155)
    ·
      refine ⟨83790586272291473415873233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55860390848194315610582155 83790586272291473415873233)
      ·
        refine ⟨62842939704218605061904925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83790586272291473415873233 62842939704218605061904925)
        ·
          refine ⟨23566102389081976898214347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62842939704218605061904925 23566102389081976898214347)
          ·
            refine ⟨35349153583622965347321521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23566102389081976898214347 35349153583622965347321521)
            ·
              refine ⟨26511865187717224010491141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35349153583622965347321521 26511865187717224010491141)
              ·
                refine ⟨4970974722696979501967089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26511865187717224010491141 4970974722696979501967089)
                ·
                  refine ⟨3728231042022734626475317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970974722696979501967089 3728231042022734626475317)
                  ·
                    refine ⟨349521660189631371232061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3728231042022734626475317 349521660189631371232061)
                    ·
                      rfl

theorem cell23_2042073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_2042073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042073 prefixEnd_2042073 := by exact prefixLift 2042073
  have htrace : WordTrace (prefixWord ++ tailWord_2042073) baseStart_2042073 baseEnd_2042073 := by
    simpa [prefixWord, tailWord_2042073, baseEnd_2042073] using wordTrace_append hprefix tailTrace_2042073
  have hstable : (prefixWord ++ tailWord_2042073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042073).length < 2 ^ (prefixWord ++ tailWord_2042073).sum := by decide
  have hdescent : baseEnd_2042073 < baseStart_2042073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042077 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 5]
def baseStart_2042077 : Nat := 118140960795 + 2042077 * 2 ^ 59
def prefixEnd_2042077 : Nat := 4983230072969 + 3 ^ 40 * 2042077 * 2
def baseEnd_2042077 : Nat := 116507448276834677560685

theorem tailTrace_2042077 : CollatzResearch.WordTrace tailWord_2042077 prefixEnd_2042077 116507448276834677560685 := by
  unfold tailWord_2042077
  simp only [CollatzResearch.WordTrace]
  refine ⟨74480667022911262830588485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49653778015274175220392323 74480667022911262830588485)
  ·
    refine ⟨13965125066795861780735341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74480667022911262830588485 13965125066795861780735341)
    ·
      refine ⟨5236921900048448167775753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13965125066795861780735341 5236921900048448167775753)
      ·
        refine ⟨3927691425036336125831815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236921900048448167775753 3927691425036336125831815)
        ·
          refine ⟨5891537137554504188747723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927691425036336125831815 5891537137554504188747723)
          ·
            refine ⟨8837305706331756283121585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891537137554504188747723 8837305706331756283121585)
            ·
              refine ⟨6627979279748817212341189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8837305706331756283121585 6627979279748817212341189)
              ·
                refine ⟨1242746114952903227313973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6627979279748817212341189 1242746114952903227313973)
                ·
                  refine ⟨116507448276834677560685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242746114952903227313973 116507448276834677560685)
                  ·
                    rfl

theorem cell23_2042077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_2042077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042077 prefixEnd_2042077 := by exact prefixLift 2042077
  have htrace : WordTrace (prefixWord ++ tailWord_2042077) baseStart_2042077 baseEnd_2042077 := by
    simpa [prefixWord, tailWord_2042077, baseEnd_2042077] using wordTrace_append hprefix tailTrace_2042077
  have hstable : (prefixWord ++ tailWord_2042077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042077).length < 2 ^ (prefixWord ++ tailWord_2042077).sum := by decide
  have hdescent : baseEnd_2042077 < baseStart_2042077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042110 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_2042110 : Nat := 118140960795 + 2042110 * 2 ^ 59
def prefixEnd_2042110 : Nat := 4983230072969 + 3 ^ 40 * 2042110 * 2
def baseEnd_2042110 : Nat := 1048583979353110468933513

theorem tailTrace_2042110 : CollatzResearch.WordTrace tailWord_2042110 prefixEnd_2042110 1048583979353110468933513 := by
  unfold tailWord_2042110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310233828973963683317473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49654580421194472977693189 9310233828973963683317473)
  ·
    refine ⟨6982675371730472762488105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9310233828973963683317473 6982675371730472762488105)
    ·
      refine ⟨5237006528797854571866079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6982675371730472762488105 5237006528797854571866079)
      ·
        refine ⟨7855509793196781857799119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237006528797854571866079 7855509793196781857799119)
        ·
          refine ⟨11783264689795172786698679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7855509793196781857799119 11783264689795172786698679)
          ·
            refine ⟨17674897034692759180048019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11783264689795172786698679 17674897034692759180048019)
            ·
              refine ⟨26512345552039138770072029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17674897034692759180048019 26512345552039138770072029)
              ·
                refine ⟨9942129582014677038777011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26512345552039138770072029 9942129582014677038777011)
                ·
                  refine ⟨14913194373022015558165517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9942129582014677038777011 14913194373022015558165517)
                  ·
                    refine ⟨5592447889883255834312069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14913194373022015558165517 5592447889883255834312069)
                    ·
                      refine ⟨1048583979353110468933513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5592447889883255834312069 1048583979353110468933513)
                      ·
                        rfl

theorem cell23_2042110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_2042110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042110 prefixEnd_2042110 := by exact prefixLift 2042110
  have htrace : WordTrace (prefixWord ++ tailWord_2042110) baseStart_2042110 baseEnd_2042110 := by
    simpa [prefixWord, tailWord_2042110, baseEnd_2042110] using wordTrace_append hprefix tailTrace_2042110
  have hstable : (prefixWord ++ tailWord_2042110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042110).length < 2 ^ (prefixWord ++ tailWord_2042110).sum := by decide
  have hdescent : baseEnd_2042110 < baseStart_2042110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042133 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 8]
def baseStart_2042133 : Nat := 118140960795 + 2042133 * 2 ^ 59
def prefixEnd_2042133 : Nat := 4983230072969 + 3 ^ 40 * 2042133 * 2
def baseEnd_2042133 : Nat := 116510643267573764327323

theorem tailTrace_2042133 : CollatzResearch.WordTrace tailWord_2042133 prefixEnd_2042133 116510643267573764327323 := by
  unfold tailWord_2042133
  simp only [CollatzResearch.WordTrace]
  refine ⟨74482709510708384394627053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49655139673805589596418035 74482709510708384394627053)
  ·
    refine ⟨27931016066515644147985145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74482709510708384394627053 27931016066515644147985145)
    ·
      refine ⟨20948262049886733110988859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27931016066515644147985145 20948262049886733110988859)
      ·
        refine ⟨31422393074830099666483289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20948262049886733110988859 31422393074830099666483289)
        ·
          refine ⟨23566794806122574749862467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31422393074830099666483289 23566794806122574749862467)
          ·
            refine ⟨35350192209183862124793701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23566794806122574749862467 35350192209183862124793701)
            ·
              refine ⟨6628161039221974148398819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35350192209183862124793701 6628161039221974148398819)
              ·
                refine ⟨9942241558832961222598229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6628161039221974148398819 9942241558832961222598229)
                ·
                  refine ⟨116510643267573764327323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9942241558832961222598229 116510643267573764327323)
                  ·
                    rfl

theorem cell23_2042133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_2042133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042133 prefixEnd_2042133 := by exact prefixLift 2042133
  have htrace : WordTrace (prefixWord ++ tailWord_2042133) baseStart_2042133 baseEnd_2042133 := by
    simpa [prefixWord, tailWord_2042133, baseEnd_2042133] using wordTrace_append hprefix tailTrace_2042133
  have hstable : (prefixWord ++ tailWord_2042133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042133).length < 2 ^ (prefixWord ++ tailWord_2042133).sum := by decide
  have hdescent : baseEnd_2042133 < baseStart_2042133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042164 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_2042164 : Nat := 118140960795 + 2042164 * 2 ^ 59
def prefixEnd_2042164 : Nat := 4983230072969 + 3 ^ 40 * 2042164 * 2
def baseEnd_2042164 : Nat := 1048611707308453257658265

theorem tailTrace_2042164 : CollatzResearch.WordTrace tailWord_2042164 prefixEnd_2042164 1048611707308453257658265 := by
  unfold tailWord_2042164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37241920086798038344502773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49655893449064051126003697 37241920086798038344502773)
  ·
    refine ⟨3491430008137316094797135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37241920086798038344502773 3491430008137316094797135)
    ·
      refine ⟨5237145012205974142195703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491430008137316094797135 5237145012205974142195703)
      ·
        refine ⟨7855717518308961213293555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237145012205974142195703 7855717518308961213293555)
        ·
          refine ⟨11783576277463441819940333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7855717518308961213293555 11783576277463441819940333)
          ·
            refine ⟨4418841104048790682477625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11783576277463441819940333 4418841104048790682477625)
            ·
              refine ⟨3314130828036593011858219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418841104048790682477625 3314130828036593011858219)
              ·
                refine ⟨4971196242054889517787329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314130828036593011858219 4971196242054889517787329)
                ·
                  refine ⟨3728397181541167138340497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971196242054889517787329 3728397181541167138340497)
                  ·
                    refine ⟨2796297886155875353755373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3728397181541167138340497 2796297886155875353755373)
                    ·
                      refine ⟨1048611707308453257658265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2796297886155875353755373 1048611707308453257658265)
                      ·
                        rfl

theorem cell23_2042164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_2042164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042164 prefixEnd_2042164 := by exact prefixLift 2042164
  have htrace : WordTrace (prefixWord ++ tailWord_2042164) baseStart_2042164 baseEnd_2042164 := by
    simpa [prefixWord, tailWord_2042164, baseEnd_2042164] using wordTrace_append hprefix tailTrace_2042164
  have hstable : (prefixWord ++ tailWord_2042164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042164).length < 2 ^ (prefixWord ++ tailWord_2042164).sum := by decide
  have hdescent : baseEnd_2042164 < baseStart_2042164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042251 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 1, 2, 2]
def baseStart_2042251 : Nat := 118140960795 + 2042251 * 2 ^ 59
def prefixEnd_2042251 : Nat := 4983230072969 + 3 ^ 40 * 2042251 * 2
def baseEnd_2042251 : Nat := 1048656380125394417270365

theorem tailTrace_2042251 : CollatzResearch.WordTrace tailWord_2042251 prefixEnd_2042251 1048656380125394417270365 := by
  unfold tailWord_2042251
  simp only [CollatzResearch.WordTrace]
  refine ⟨74487013324280890547422607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49658008882853927031615071 74487013324280890547422607)
  ·
    refine ⟨111730519986421335821133911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74487013324280890547422607 111730519986421335821133911)
    ·
      refine ⟨167595779979632003731700867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111730519986421335821133911 167595779979632003731700867)
      ·
        refine ⟨251393669969448005597551301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167595779979632003731700867 251393669969448005597551301)
        ·
          refine ⟨47136313119271501049540869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251393669969448005597551301 47136313119271501049540869)
          ·
            refine ⟨8838058709863406446788913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47136313119271501049540869 8838058709863406446788913)
            ·
              refine ⟨6628544032397554835091685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8838058709863406446788913 6628544032397554835091685)
              ·
                refine ⟨1242852006074541531579691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6628544032397554835091685 1242852006074541531579691)
                ·
                  refine ⟨1864278009111812297369537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242852006074541531579691 1864278009111812297369537)
                  ·
                    refine ⟨1398208506833859223027153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1864278009111812297369537 1398208506833859223027153)
                    ·
                      refine ⟨1048656380125394417270365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398208506833859223027153 1048656380125394417270365)
                      ·
                        rfl

theorem cell23_2042251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 2, 2].length) (baseStart_2042251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042251 prefixEnd_2042251 := by exact prefixLift 2042251
  have htrace : WordTrace (prefixWord ++ tailWord_2042251) baseStart_2042251 baseEnd_2042251 := by
    simpa [prefixWord, tailWord_2042251, baseEnd_2042251] using wordTrace_append hprefix tailTrace_2042251
  have hstable : (prefixWord ++ tailWord_2042251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042251).length < 2 ^ (prefixWord ++ tailWord_2042251).sum := by decide
  have hdescent : baseEnd_2042251 < baseStart_2042251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042264 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4]
def baseStart_2042264 : Nat := 118140960795 + 2042264 * 2 ^ 59
def prefixEnd_2042264 : Nat := 4983230072969 + 3 ^ 40 * 2042264 * 2
def baseEnd_2042264 : Nat := 1048663055373902866407805

theorem tailTrace_2042264 : CollatzResearch.WordTrace tailWord_2042264 prefixEnd_2042264 1048663055373902866407805 := by
  unfold tailWord_2042264
  simp only [CollatzResearch.WordTrace]
  refine ⟨37243743736616896883822923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49658324982155862511763897 37243743736616896883822923)
  ·
    refine ⟨55865615604925345325734385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37243743736616896883822923 55865615604925345325734385)
    ·
      refine ⟨41899211703694008994300789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55865615604925345325734385 41899211703694008994300789)
      ·
        refine ⟨3928051097221313343215699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41899211703694008994300789 3928051097221313343215699)
        ·
          refine ⟨5892076645831970014823549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928051097221313343215699 5892076645831970014823549)
          ·
            refine ⟨2209528742186988755558831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5892076645831970014823549 2209528742186988755558831)
            ·
              refine ⟨3314293113280483133338247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209528742186988755558831 3314293113280483133338247)
              ·
                refine ⟨4971439669920724700007371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314293113280483133338247 4971439669920724700007371)
                ·
                  refine ⟨7457159504881087050011057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971439669920724700007371 7457159504881087050011057)
                  ·
                    refine ⟨5592869628660815287508293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457159504881087050011057 5592869628660815287508293)
                    ·
                      refine ⟨1048663055373902866407805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5592869628660815287508293 1048663055373902866407805)
                      ·
                        rfl

theorem cell23_2042264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_2042264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042264 prefixEnd_2042264 := by exact prefixLift 2042264
  have htrace : WordTrace (prefixWord ++ tailWord_2042264) baseStart_2042264 baseEnd_2042264 := by
    simpa [prefixWord, tailWord_2042264, baseEnd_2042264] using wordTrace_append hprefix tailTrace_2042264
  have hstable : (prefixWord ++ tailWord_2042264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042264).length < 2 ^ (prefixWord ++ tailWord_2042264).sum := by decide
  have hdescent : baseEnd_2042264 < baseStart_2042264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042330 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_2042330 : Nat := 118140960795 + 2042330 * 2 ^ 59
def prefixEnd_2042330 : Nat := 4983230072969 + 3 ^ 40 * 2042330 * 2
def baseEnd_2042330 : Nat := 116521882788566623131389

theorem tailTrace_2042330 : CollatzResearch.WordTrace tailWord_2042330 prefixEnd_2042330 116521882788566623131389 := by
  unfold tailWord_2042330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622473672748671759887111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49659929793996458026365629 18622473672748671759887111)
  ·
    refine ⟨27933710509123007639830667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18622473672748671759887111 27933710509123007639830667)
    ·
      refine ⟨41900565763684511459746001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933710509123007639830667 41900565763684511459746001)
      ·
        refine ⟨31425424322763383594809501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41900565763684511459746001 31425424322763383594809501)
        ·
          refine ⟨11784534121036268848053563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31425424322763383594809501 11784534121036268848053563)
          ·
            refine ⟨17676801181554403272080345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11784534121036268848053563 17676801181554403272080345)
            ·
              refine ⟨13257600886165802454060259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17676801181554403272080345 13257600886165802454060259)
              ·
                refine ⟨19886401329248703681090389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257600886165802454060259 19886401329248703681090389)
                ·
                  refine ⟨116521882788566623131389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19886401329248703681090389 116521882788566623131389)
                  ·
                    rfl

theorem cell23_2042330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_2042330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042330 prefixEnd_2042330 := by exact prefixLift 2042330
  have htrace : WordTrace (prefixWord ++ tailWord_2042330) baseStart_2042330 baseEnd_2042330 := by
    simpa [prefixWord, tailWord_2042330, baseEnd_2042330] using wordTrace_append hprefix tailTrace_2042330
  have hstable : (prefixWord ++ tailWord_2042330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042330).length < 2 ^ (prefixWord ++ tailWord_2042330).sum := by decide
  have hdescent : baseEnd_2042330 < baseStart_2042330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042341 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2042341 : Nat := 118140960795 + 2042341 * 2 ^ 59
def prefixEnd_2042341 : Nat := 4983230072969 + 3 ^ 40 * 2042341 * 2
def baseEnd_2042341 : Nat := 1048702593384299065144951

theorem tailTrace_2042341 : CollatzResearch.WordTrace tailWord_2042341 prefixEnd_2042341 1048702593384299065144951 := by
  unfold tailWord_2042341
  simp only [CollatzResearch.WordTrace]
  refine ⟨74490295893954835918198877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49660197262636557278799251 74490295893954835918198877)
  ·
    refine ⟨27933860960233063469324579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74490295893954835918198877 27933860960233063469324579)
    ·
      refine ⟨41900791440349595203986869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27933860960233063469324579 41900791440349595203986869)
      ·
        refine ⟨3928199197532774550373769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41900791440349595203986869 3928199197532774550373769)
        ·
          refine ⟨2946149398149580912780327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3928199197532774550373769 2946149398149580912780327)
          ·
            refine ⟨4419224097224371369170491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946149398149580912780327 4419224097224371369170491)
            ·
              refine ⟨6628836145836557053755737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419224097224371369170491 6628836145836557053755737)
              ·
                refine ⟨4971627109377417790316803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628836145836557053755737 4971627109377417790316803)
                ·
                  refine ⟨7457440664066126685475205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971627109377417790316803 7457440664066126685475205)
                  ·
                    refine ⟨1398270124512398753526601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7457440664066126685475205 1398270124512398753526601)
                    ·
                      refine ⟨1048702593384299065144951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398270124512398753526601 1048702593384299065144951)
                      ·
                        rfl

theorem cell23_2042341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2042341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042341 prefixEnd_2042341 := by exact prefixLift 2042341
  have htrace : WordTrace (prefixWord ++ tailWord_2042341) baseStart_2042341 baseEnd_2042341 := by
    simpa [prefixWord, tailWord_2042341, baseEnd_2042341] using wordTrace_append hprefix tailTrace_2042341
  have hstable : (prefixWord ++ tailWord_2042341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042341).length < 2 ^ (prefixWord ++ tailWord_2042341).sum := by decide
  have hdescent : baseEnd_2042341 < baseStart_2042341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042347 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 5]
def baseStart_2042347 : Nat := 118140960795 + 2042347 * 2 ^ 59
def prefixEnd_2042347 : Nat := 4983230072969 + 3 ^ 40 * 2042347 * 2
def baseEnd_2042347 : Nat := 116522852696469560185547

theorem tailTrace_2042347 : CollatzResearch.WordTrace tailWord_2042347 prefixEnd_2042347 116522852696469560185547 := by
  unfold tailWord_2042347
  simp only [CollatzResearch.WordTrace]
  refine ⟨74490514731933098942917295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49660343154622065961944863 74490514731933098942917295)
  ·
    refine ⟨111735772097899648414375943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74490514731933098942917295 111735772097899648414375943)
    ·
      refine ⟨167603658146849472621563915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111735772097899648414375943 167603658146849472621563915)
      ·
        refine ⟨251405487220274208932345873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167603658146849472621563915 251405487220274208932345873)
        ·
          refine ⟨188554115415205656699259405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251405487220274208932345873 188554115415205656699259405)
          ·
            refine ⟨70707793280702121262222277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188554115415205656699259405 70707793280702121262222277)
            ·
              refine ⟨13257711240131647736666677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70707793280702121262222277 13257711240131647736666677)
              ·
                refine ⟨1242910428762341975312501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13257711240131647736666677 1242910428762341975312501)
                ·
                  refine ⟨116522852696469560185547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242910428762341975312501 116522852696469560185547)
                  ·
                    rfl

theorem cell23_2042347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 5].length) (baseStart_2042347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042347 prefixEnd_2042347 := by exact prefixLift 2042347
  have htrace : WordTrace (prefixWord ++ tailWord_2042347) baseStart_2042347 baseEnd_2042347 := by
    simpa [prefixWord, tailWord_2042347, baseEnd_2042347] using wordTrace_append hprefix tailTrace_2042347
  have hstable : (prefixWord ++ tailWord_2042347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042347).length < 2 ^ (prefixWord ++ tailWord_2042347).sum := by decide
  have hdescent : baseEnd_2042347 < baseStart_2042347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042358 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_2042358 : Nat := 118140960795 + 2042358 * 2 ^ 59
def prefixEnd_2042358 : Nat := 4983230072969 + 3 ^ 40 * 2042358 * 2
def baseEnd_2042358 : Nat := 1048711322555425498632373

theorem tailTrace_2042358 : CollatzResearch.WordTrace tailWord_2042358 prefixEnd_2042358 1048711322555425498632373 := by
  unfold tailWord_2042358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655682245930827988847983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49660610623262165214378485 4655682245930827988847983)
  ·
    refine ⟨6983523368896241983271975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4655682245930827988847983 6983523368896241983271975)
    ·
      refine ⟨10475285053344362974907963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983523368896241983271975 10475285053344362974907963)
      ·
        refine ⟨15712927580016544462361945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475285053344362974907963 15712927580016544462361945)
        ·
          refine ⟨11784695685012408346771459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15712927580016544462361945 11784695685012408346771459)
          ·
            refine ⟨17677043527518612520157189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11784695685012408346771459 17677043527518612520157189)
            ·
              refine ⟨3314445661409739847529473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17677043527518612520157189 3314445661409739847529473)
              ·
                refine ⟨2485834246057304885647105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3314445661409739847529473 2485834246057304885647105)
                ·
                  refine ⟨1864375684542978664235329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2485834246057304885647105 1864375684542978664235329)
                  ·
                    refine ⟨1398281763407233998176497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1864375684542978664235329 1398281763407233998176497)
                    ·
                      refine ⟨1048711322555425498632373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398281763407233998176497 1048711322555425498632373)
                      ·
                        rfl

theorem cell23_2042358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_2042358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042358 prefixEnd_2042358 := by exact prefixLift 2042358
  have htrace : WordTrace (prefixWord ++ tailWord_2042358) baseStart_2042358 baseEnd_2042358 := by
    simpa [prefixWord, tailWord_2042358, baseEnd_2042358] using wordTrace_append hprefix tailTrace_2042358
  have hstable : (prefixWord ++ tailWord_2042358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042358).length < 2 ^ (prefixWord ++ tailWord_2042358).sum := by decide
  have hdescent : baseEnd_2042358 < baseStart_2042358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042367 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 7, 2]
def baseStart_2042367 : Nat := 118140960795 + 2042367 * 2 ^ 59
def prefixEnd_2042367 : Nat := 4983230072969 + 3 ^ 40 * 2042367 * 2
def baseEnd_2042367 : Nat := 1048715943881315963419831

theorem tailTrace_2042367 : CollatzResearch.WordTrace tailWord_2042367 prefixEnd_2042367 1048715943881315963419831 := by
  unfold tailWord_2042367
  simp only [CollatzResearch.WordTrace]
  refine ⟨74491244191860642358645355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49660829461240428239096903 74491244191860642358645355)
  ·
    refine ⟨111736866287790963537968033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74491244191860642358645355 111736866287790963537968033)
    ·
      refine ⟨83802649715843222653476025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111736866287790963537968033 83802649715843222653476025)
      ·
        refine ⟨62851987286882416990107019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83802649715843222653476025 62851987286882416990107019)
        ·
          refine ⟨94277980930323625485160529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62851987286882416990107019 94277980930323625485160529)
          ·
            refine ⟨70708485697742719113870397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94277980930323625485160529 70708485697742719113870397)
            ·
              refine ⟨26515682136653519667701399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70708485697742719113870397 26515682136653519667701399)
              ·
                refine ⟨39773523204980279501552099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26515682136653519667701399 39773523204980279501552099)
                ·
                  refine ⟨59660284807470419252328149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39773523204980279501552099 59660284807470419252328149)
                  ·
                    refine ⟨1398287925175087951226441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59660284807470419252328149 1398287925175087951226441)
                    ·
                      refine ⟨1048715943881315963419831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398287925175087951226441 1048715943881315963419831)
                      ·
                        rfl

theorem cell23_2042367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_2042367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042367 prefixEnd_2042367 := by exact prefixLift 2042367
  have htrace : WordTrace (prefixWord ++ tailWord_2042367) baseStart_2042367 baseEnd_2042367 := by
    simpa [prefixWord, tailWord_2042367, baseEnd_2042367] using wordTrace_append hprefix tailTrace_2042367
  have hstable : (prefixWord ++ tailWord_2042367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042367).length < 2 ^ (prefixWord ++ tailWord_2042367).sum := by decide
  have hdescent : baseEnd_2042367 < baseStart_2042367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042381 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 7]
def baseStart_2042381 : Nat := 118140960795 + 2042381 * 2 ^ 59
def prefixEnd_2042381 : Nat := 4983230072969 + 3 ^ 40 * 2042381 * 2
def baseEnd_2042381 : Nat := 116524792512275434293863

theorem tailTrace_2042381 : CollatzResearch.WordTrace tailWord_2042381 prefixEnd_2042381 116524792512275434293863 := by
  unfold tailWord_2042381
  simp only [CollatzResearch.WordTrace]
  refine ⟨74491754813809922749654997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49661169875873281833103331 74491754813809922749654997)
  ·
    refine ⟨1745900503448670064445039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 74491754813809922749654997 1745900503448670064445039)
    ·
      refine ⟨2618850755173005096667559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745900503448670064445039 2618850755173005096667559)
      ·
        refine ⟨3928276132759507645001339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618850755173005096667559 3928276132759507645001339)
        ·
          refine ⟨5892414199139261467502009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928276132759507645001339 5892414199139261467502009)
          ·
            refine ⟨4419310649354446100626507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5892414199139261467502009 4419310649354446100626507)
            ·
              refine ⟨6628965974031669150939761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419310649354446100626507 6628965974031669150939761)
              ·
                refine ⟨4971724480523751863204821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628965974031669150939761 4971724480523751863204821)
                ·
                  refine ⟨116524792512275434293863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4971724480523751863204821 116524792512275434293863)
                  ·
                    rfl

theorem cell23_2042381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_2042381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042381 prefixEnd_2042381 := by exact prefixLift 2042381
  have htrace : WordTrace (prefixWord ++ tailWord_2042381) baseStart_2042381 baseEnd_2042381 := by
    simpa [prefixWord, tailWord_2042381, baseEnd_2042381] using wordTrace_append hprefix tailTrace_2042381
  have hstable : (prefixWord ++ tailWord_2042381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042381).length < 2 ^ (prefixWord ++ tailWord_2042381).sum := by decide
  have hdescent : baseEnd_2042381 < baseStart_2042381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042424 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 3, 4]
def baseStart_2042424 : Nat := 118140960795 + 2042424 * 2 ^ 59
def prefixEnd_2042424 : Nat := 4983230072969 + 3 ^ 40 * 2042424 * 2
def baseEnd_2042424 : Nat := 349581737426207413469023

theorem tailTrace_2042424 : CollatzResearch.WordTrace tailWord_2042424 prefixEnd_2042424 349581737426207413469023 := by
  unfold tailWord_2042424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37246661576327070546735163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49662215435102760728980217 37246661576327070546735163)
  ·
    refine ⟨55869992364490605820102745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37246661576327070546735163 55869992364490605820102745)
    ·
      refine ⟨41902494273367954365077059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55869992364490605820102745 41902494273367954365077059)
      ·
        refine ⟨62853741410051931547615589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41902494273367954365077059 62853741410051931547615589)
        ·
          refine ⟨11785076514384737165177923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62853741410051931547615589 11785076514384737165177923)
          ·
            refine ⟨17677614771577105747766885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785076514384737165177923 17677614771577105747766885)
            ·
              refine ⟨3314552769670707327706291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17677614771577105747766885 3314552769670707327706291)
              ·
                refine ⟨4971829154506060991559437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314552769670707327706291 4971829154506060991559437)
                ·
                  refine ⟨1864435932939772871834789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4971829154506060991559437 1864435932939772871834789)
                  ·
                    refine ⟨349581737426207413469023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864435932939772871834789 349581737426207413469023)
                    ·
                      rfl

theorem cell23_2042424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_2042424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042424 prefixEnd_2042424 := by exact prefixLift 2042424
  have htrace : WordTrace (prefixWord ++ tailWord_2042424) baseStart_2042424 baseEnd_2042424 := by
    simpa [prefixWord, tailWord_2042424, baseEnd_2042424] using wordTrace_append hprefix tailTrace_2042424
  have hstable : (prefixWord ++ tailWord_2042424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042424).length < 2 ^ (prefixWord ++ tailWord_2042424).sum := by decide
  have hdescent : baseEnd_2042424 < baseStart_2042424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042464 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3]
def baseStart_2042464 : Nat := 118140960795 + 2042464 * 2 ^ 59
def prefixEnd_2042464 : Nat := 4983230072969 + 3 ^ 40 * 2042464 * 2
def baseEnd_2042464 : Nat := 1048765751504802083906885

theorem tailTrace_2042464 : CollatzResearch.WordTrace tailWord_2042464 prefixEnd_2042464 1048765751504802083906885 := by
  unfold tailWord_2042464
  simp only [CollatzResearch.WordTrace]
  refine ⟨37247391036254613962463223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49663188048339485283284297 37247391036254613962463223)
  ·
    refine ⟨55871086554381920943694835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37247391036254613962463223 55871086554381920943694835)
    ·
      refine ⟨83806629831572881415542253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55871086554381920943694835 83806629831572881415542253)
      ·
        refine ⟨31427486186839830530828345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83806629831572881415542253 31427486186839830530828345)
        ·
          refine ⟨23570614640129872898121259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31427486186839830530828345 23570614640129872898121259)
          ·
            refine ⟨35355921960194809347181889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570614640129872898121259 35355921960194809347181889)
            ·
              refine ⟨26516941470146107010386417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35355921960194809347181889 26516941470146107010386417)
              ·
                refine ⟨19887706102609580257789813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26516941470146107010386417 19887706102609580257789813)
                ·
                  refine ⟨1864472447119648149167795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19887706102609580257789813 1864472447119648149167795)
                  ·
                    refine ⟨2796708670679472223751693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1864472447119648149167795 2796708670679472223751693)
                    ·
                      refine ⟨1048765751504802083906885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2796708670679472223751693 1048765751504802083906885)
                      ·
                        rfl

theorem cell23_2042464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_2042464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042464 prefixEnd_2042464 := by exact prefixLift 2042464
  have htrace : WordTrace (prefixWord ++ tailWord_2042464) baseStart_2042464 baseEnd_2042464 := by
    simpa [prefixWord, tailWord_2042464, baseEnd_2042464] using wordTrace_append hprefix tailTrace_2042464
  have hstable : (prefixWord ++ tailWord_2042464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042464).length < 2 ^ (prefixWord ++ tailWord_2042464).sum := by decide
  have hdescent : baseEnd_2042464 < baseStart_2042464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042501 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_2042501 : Nat := 118140960795 + 2042501 * 2 ^ 59
def prefixEnd_2042501 : Nat := 4983230072969 + 3 ^ 40 * 2042501 * 2
def baseEnd_2042501 : Nat := 349594916763006146381405

theorem tailTrace_2042501 : CollatzResearch.WordTrace tailWord_2042501 prefixEnd_2042501 349594916763006146381405 := by
  unfold tailWord_2042501
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496131573375183244023357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49664087715583455496015571 74496131573375183244023357)
  ·
    refine ⟨27936049340015693716508759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74496131573375183244023357 27936049340015693716508759)
    ·
      refine ⟨41904074010023540574763139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27936049340015693716508759 41904074010023540574763139)
      ·
        refine ⟨62856111015035310862144709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41904074010023540574763139 62856111015035310862144709)
        ·
          refine ⟨11785520815319120786652133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62856111015035310862144709 11785520815319120786652133)
          ·
            refine ⟨2209785152872335147497275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11785520815319120786652133 2209785152872335147497275)
            ·
              refine ⟨3314677729308502721245913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2209785152872335147497275 3314677729308502721245913)
              ·
                refine ⟨2486008296981377040934435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3314677729308502721245913 2486008296981377040934435)
                ·
                  refine ⟨3729012445472065561401653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486008296981377040934435 3729012445472065561401653)
                  ·
                    refine ⟨349594916763006146381405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3729012445472065561401653 349594916763006146381405)
                    ·
                      rfl

theorem cell23_2042501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_2042501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042501 prefixEnd_2042501 := by exact prefixLift 2042501
  have htrace : WordTrace (prefixWord ++ tailWord_2042501) baseStart_2042501 baseEnd_2042501 := by
    simpa [prefixWord, tailWord_2042501, baseEnd_2042501] using wordTrace_append hprefix tailTrace_2042501
  have hstable : (prefixWord ++ tailWord_2042501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042501).length < 2 ^ (prefixWord ++ tailWord_2042501).sum := by decide
  have hdescent : baseEnd_2042501 < baseStart_2042501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042514 : List Nat := [3, 2, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_2042514 : Nat := 118140960795 + 2042514 * 2 ^ 59
def prefixEnd_2042514 : Nat := 4983230072969 + 3 ^ 40 * 2042514 * 2
def baseEnd_2042514 : Nat := 349597141845842296093885

theorem tailTrace_2042514 : CollatzResearch.WordTrace tailWord_2042514 prefixEnd_2042514 349597141845842296093885 := by
  unfold tailWord_2042514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624151430582021616061649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49664403814885390976164397 18624151430582021616061649)
  ·
    refine ⟨13968113572936516212046237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18624151430582021616061649 13968113572936516212046237)
    ·
      refine ⟨5238042589851193579517339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13968113572936516212046237 5238042589851193579517339)
      ·
        refine ⟨7857063884776790369276009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238042589851193579517339 7857063884776790369276009)
        ·
          refine ⟨5892797913582592776957007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7857063884776790369276009 5892797913582592776957007)
          ·
            refine ⟨8839196870373889165435511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892797913582592776957007 8839196870373889165435511)
            ·
              refine ⟨13258795305560833748153267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839196870373889165435511 13258795305560833748153267)
              ·
                refine ⟨19888192958341250622229901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13258795305560833748153267 19888192958341250622229901)
                ·
                  refine ⟨7458072359377968983336213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19888192958341250622229901 7458072359377968983336213)
                  ·
                    refine ⟨349597141845842296093885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7458072359377968983336213 349597141845842296093885)
                    ·
                      rfl

theorem cell23_2042514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_2042514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042514 prefixEnd_2042514 := by exact prefixLift 2042514
  have htrace : WordTrace (prefixWord ++ tailWord_2042514) baseStart_2042514 baseEnd_2042514 := by
    simpa [prefixWord, tailWord_2042514, baseEnd_2042514] using wordTrace_append hprefix tailTrace_2042514
  have hstable : (prefixWord ++ tailWord_2042514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042514).length < 2 ^ (prefixWord ++ tailWord_2042514).sum := by decide
  have hdescent : baseEnd_2042514 < baseStart_2042514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042521 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 1, 1, 4]
def baseStart_2042521 : Nat := 118140960795 + 2042521 * 2 ^ 59
def prefixEnd_2042521 : Nat := 4983230072969 + 3 ^ 40 * 2042521 * 2
def baseEnd_2042521 : Nat := 1048795019902108360894123

theorem tailTrace_2042521 : CollatzResearch.WordTrace tailWord_2042521 prefixEnd_2042521 1048795019902108360894123 := by
  unfold tailWord_2042521
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496861033302726659751417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49664574022201817773167611 74496861033302726659751417)
  ·
    refine ⟨55872645774977044994813563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74496861033302726659751417 55872645774977044994813563)
    ·
      refine ⟨83808968662465567492220345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55872645774977044994813563 83808968662465567492220345)
      ·
        refine ⟨62856726496849175619165259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83808968662465567492220345 62856726496849175619165259)
        ·
          refine ⟨94285089745273763428747889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62856726496849175619165259 94285089745273763428747889)
          ·
            refine ⟨70713817308955322571560917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94285089745273763428747889 70713817308955322571560917)
            ·
              refine ⟨1657355093178640372770959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70713817308955322571560917 1657355093178640372770959)
              ·
                refine ⟨2486032639767960559156439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657355093178640372770959 2486032639767960559156439)
                ·
                  refine ⟨3729048959651940838734659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486032639767960559156439 3729048959651940838734659)
                  ·
                    refine ⟨5593573439477911258101989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729048959651940838734659 5593573439477911258101989)
                    ·
                      refine ⟨1048795019902108360894123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5593573439477911258101989 1048795019902108360894123)
                      ·
                        rfl

theorem cell23_2042521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_2042521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042521 prefixEnd_2042521 := by exact prefixLift 2042521
  have htrace : WordTrace (prefixWord ++ tailWord_2042521) baseStart_2042521 baseEnd_2042521 := by
    simpa [prefixWord, tailWord_2042521, baseEnd_2042521] using wordTrace_append hprefix tailTrace_2042521
  have hstable : (prefixWord ++ tailWord_2042521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042521).length < 2 ^ (prefixWord ++ tailWord_2042521).sum := by decide
  have hdescent : baseEnd_2042521 < baseStart_2042521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042541 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_2042541 : Nat := 118140960795 + 2042541 * 2 ^ 59
def prefixEnd_2042541 : Nat := 4983230072969 + 3 ^ 40 * 2042541 * 2
def baseEnd_2042541 : Nat := 1048805289515198282644031

theorem tailTrace_2042541 : CollatzResearch.WordTrace tailWord_2042541 prefixEnd_2042541 1048805289515198282644031 := by
  unfold tailWord_2042541
  simp only [CollatzResearch.WordTrace]
  refine ⟨74497590493230270075479477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49665060328820180050319651 74497590493230270075479477)
  ·
    refine ⟨6984149108740337819576201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74497590493230270075479477 6984149108740337819576201)
    ·
      refine ⟨5238111831555253364682151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6984149108740337819576201 5238111831555253364682151)
      ·
        refine ⟨7857167747332880047023227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238111831555253364682151 7857167747332880047023227)
        ·
          refine ⟨11785751620999320070534841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857167747332880047023227 11785751620999320070534841)
          ·
            refine ⟨8839313715749490052901131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11785751620999320070534841 8839313715749490052901131)
            ·
              refine ⟨13258970573624235079351697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839313715749490052901131 13258970573624235079351697)
              ·
                refine ⟨9944227930218176309513773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13258970573624235079351697 9944227930218176309513773)
                ·
                  refine ⟨3729085473831816116067665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9944227930218176309513773 3729085473831816116067665)
                  ·
                    refine ⟨2796814105373862087050749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729085473831816116067665 2796814105373862087050749)
                    ·
                      refine ⟨1048805289515198282644031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2796814105373862087050749 1048805289515198282644031)
                      ·
                        rfl

theorem cell23_2042541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_2042541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042541 prefixEnd_2042541 := by exact prefixLift 2042541
  have htrace : WordTrace (prefixWord ++ tailWord_2042541) baseStart_2042541 baseEnd_2042541 := by
    simpa [prefixWord, tailWord_2042541, baseEnd_2042541] using wordTrace_append hprefix tailTrace_2042541
  have hstable : (prefixWord ++ tailWord_2042541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042541).length < 2 ^ (prefixWord ++ tailWord_2042541).sum := by decide
  have hdescent : baseEnd_2042541 < baseStart_2042541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042551 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_2042551 : Nat := 118140960795 + 2042551 * 2 ^ 59
def prefixEnd_2042551 : Nat := 4983230072969 + 3 ^ 40 * 2042551 * 2
def baseEnd_2042551 : Nat := 1048810424321743243518985

theorem tailTrace_2042551 : CollatzResearch.WordTrace tailWord_2042551 prefixEnd_2042551 1048810424321743243518985 := by
  unfold tailWord_2042551
  simp only [CollatzResearch.WordTrace]
  refine ⟨74497955223194041783343507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49665303482129361188895671 74497955223194041783343507)
  ·
    refine ⟨111746932834791062675015261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74497955223194041783343507 111746932834791062675015261)
    ·
      refine ⟨41905099813046648503130723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111746932834791062675015261 41905099813046648503130723)
      ·
        refine ⟨62857649719569972754696085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41905099813046648503130723 62857649719569972754696085)
        ·
          refine ⟨2946452330604842472876379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62857649719569972754696085 2946452330604842472876379)
          ·
            refine ⟨4419678495907263709314569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946452330604842472876379 4419678495907263709314569)
            ·
              refine ⟨3314758871930447781985927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419678495907263709314569 3314758871930447781985927)
              ·
                refine ⟨4972138307895671672978891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314758871930447781985927 4972138307895671672978891)
                ·
                  refine ⟨7458207461843507509468337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972138307895671672978891 7458207461843507509468337)
                  ·
                    refine ⟨5593655596382630632101253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458207461843507509468337 5593655596382630632101253)
                    ·
                      refine ⟨1048810424321743243518985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5593655596382630632101253 1048810424321743243518985)
                      ·
                        rfl

theorem cell23_2042551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_2042551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042551 prefixEnd_2042551 := by exact prefixLift 2042551
  have htrace : WordTrace (prefixWord ++ tailWord_2042551) baseStart_2042551 baseEnd_2042551 := by
    simpa [prefixWord, tailWord_2042551, baseEnd_2042551] using wordTrace_append hprefix tailTrace_2042551
  have hstable : (prefixWord ++ tailWord_2042551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042551).length < 2 ^ (prefixWord ++ tailWord_2042551).sum := by decide
  have hdescent : baseEnd_2042551 < baseStart_2042551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042572 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 1, 2, 2]
def baseStart_2042572 : Nat := 118140960795 + 2042572 * 2 ^ 59
def prefixEnd_2042572 : Nat := 4983230072969 + 3 ^ 40 * 2042572 * 2
def baseEnd_2042572 : Nat := 1048821207415487661356389

theorem tailTrace_2042572 : CollatzResearch.WordTrace tailWord_2042572 prefixEnd_2042572 1048821207415487661356389 := by
  unfold tailWord_2042572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37249360578058981184928985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49665814104078641579905313 37249360578058981184928985)
  ·
    refine ⟨27937020433544235888696739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37249360578058981184928985 27937020433544235888696739)
    ·
      refine ⟨41905530650316353833045109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937020433544235888696739 41905530650316353833045109)
      ·
        refine ⟨3928643498467158171847979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41905530650316353833045109 3928643498467158171847979)
        ·
          refine ⟨5892965247700737257771969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928643498467158171847979 5892965247700737257771969)
          ·
            refine ⟨4419723935775552943328977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5892965247700737257771969 4419723935775552943328977)
            ·
              refine ⟨3314792951831664707496733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419723935775552943328977 3314792951831664707496733)
              ·
                refine ⟨1243047356936874265311275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3314792951831664707496733 1243047356936874265311275)
                ·
                  refine ⟨1864571035405311397966913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243047356936874265311275 1864571035405311397966913)
                  ·
                    refine ⟨1398428276553983548475185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1864571035405311397966913 1398428276553983548475185)
                    ·
                      refine ⟨1048821207415487661356389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398428276553983548475185 1048821207415487661356389)
                      ·
                        rfl

theorem cell23_2042572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_2042572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042572 prefixEnd_2042572 := by exact prefixLift 2042572
  have htrace : WordTrace (prefixWord ++ tailWord_2042572) baseStart_2042572 baseEnd_2042572 := by
    simpa [prefixWord, tailWord_2042572, baseEnd_2042572] using wordTrace_append hprefix tailTrace_2042572
  have hstable : (prefixWord ++ tailWord_2042572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042572).length < 2 ^ (prefixWord ++ tailWord_2042572).sum := by decide
  have hdescent : baseEnd_2042572 < baseStart_2042572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042605 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_2042605 : Nat := 118140960795 + 2042605 * 2 ^ 59
def prefixEnd_2042605 : Nat := 4983230072969 + 3 ^ 40 * 2042605 * 2
def baseEnd_2042605 : Nat := 1048838152277086032243737

theorem tailTrace_2042605 : CollatzResearch.WordTrace tailWord_2042605 prefixEnd_2042605 1048838152277086032243737 := by
  unfold tailWord_2042605
  simp only [CollatzResearch.WordTrace]
  refine ⟨74499924764998409005809269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49666616509998939337206179 74499924764998409005809269)
  ·
    refine ⟨6984367946718600844294619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74499924764998409005809269 6984367946718600844294619)
    ·
      refine ⟨10476551920077901266441929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6984367946718600844294619 10476551920077901266441929)
      ·
        refine ⟨7857413940058425949831447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10476551920077901266441929 7857413940058425949831447)
        ·
          refine ⟨11786120910087638924747171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857413940058425949831447 11786120910087638924747171)
          ·
            refine ⟨17679181365131458387120757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786120910087638924747171 17679181365131458387120757)
            ·
              refine ⟨1657423252981074223792571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17679181365131458387120757 1657423252981074223792571)
              ·
                refine ⟨2486134879471611335688857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1657423252981074223792571 2486134879471611335688857)
                ·
                  refine ⟨1864601159603708501766643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486134879471611335688857 1864601159603708501766643)
                  ·
                    refine ⟨2796901739405562752649965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1864601159603708501766643 2796901739405562752649965)
                    ·
                      refine ⟨1048838152277086032243737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2796901739405562752649965 1048838152277086032243737)
                      ·
                        rfl

theorem cell23_2042605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_2042605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042605 prefixEnd_2042605 := by exact prefixLift 2042605
  have htrace : WordTrace (prefixWord ++ tailWord_2042605) baseStart_2042605 baseEnd_2042605 := by
    simpa [prefixWord, tailWord_2042605, baseEnd_2042605] using wordTrace_append hprefix tailTrace_2042605
  have hstable : (prefixWord ++ tailWord_2042605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042605).length < 2 ^ (prefixWord ++ tailWord_2042605).sum := by decide
  have hdescent : baseEnd_2042605 < baseStart_2042605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042612 : List Nat := [2, 6, 1, 1, 3, 1, 2, 7]
def baseStart_2042612 : Nat := 118140960795 + 2042612 * 2 ^ 59
def prefixEnd_2042612 : Nat := 4983230072969 + 3 ^ 40 * 2042612 * 2
def baseEnd_2042612 : Nat := 38845990616358055735415

theorem tailTrace_2042612 : CollatzResearch.WordTrace tailWord_2042612 prefixEnd_2042612 38845990616358055735415 := by
  unfold tailWord_2042612
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250090037986524600657045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49666786717315366134209393 37250090037986524600657045)
  ·
    refine ⟨1746097970530618340655799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37250090037986524600657045 1746097970530618340655799)
    ·
      refine ⟨2619146955795927510983699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746097970530618340655799 2619146955795927510983699)
      ·
        refine ⟨3928720433693891266475549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619146955795927510983699 3928720433693891266475549)
        ·
          refine ⟨1473270162635209224928331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3928720433693891266475549 1473270162635209224928331)
          ·
            refine ⟨2209905243952813837392497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473270162635209224928331 2209905243952813837392497)
            ·
              refine ⟨1657428932964610378044373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2209905243952813837392497 1657428932964610378044373)
              ·
                refine ⟨38845990616358055735415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1657428932964610378044373 38845990616358055735415)
                ·
                  rfl

theorem cell23_2042612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 7].length) (baseStart_2042612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042612 prefixEnd_2042612 := by exact prefixLift 2042612
  have htrace : WordTrace (prefixWord ++ tailWord_2042612) baseStart_2042612 baseEnd_2042612 := by
    simpa [prefixWord, tailWord_2042612, baseEnd_2042612] using wordTrace_append hprefix tailTrace_2042612
  have hstable : (prefixWord ++ tailWord_2042612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042612).length < 2 ^ (prefixWord ++ tailWord_2042612).sum := by decide
  have hdescent : baseEnd_2042612 < baseStart_2042612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042628 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_2042628 : Nat := 118140960795 + 2042628 * 2 ^ 59
def prefixEnd_2042628 : Nat := 4983230072969 + 3 ^ 40 * 2042628 * 2
def baseEnd_2042628 : Nat := 1048849962332139442256131

theorem tailTrace_2042628 : CollatzResearch.WordTrace tailWord_2042628 prefixEnd_2042628 1048849962332139442256131 := by
  unfold tailWord_2042628
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250381821957541966948269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49667175762610055955931025 37250381821957541966948269)
  ·
    refine ⟨13968893183234078237605601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37250381821957541966948269 13968893183234078237605601)
    ·
      refine ⟨10476669887425558678204201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13968893183234078237605601 10476669887425558678204201)
      ·
        refine ⟨7857502415569169008653151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10476669887425558678204201 7857502415569169008653151)
        ·
          refine ⟨11786253623353753512979727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857502415569169008653151 11786253623353753512979727)
          ·
            refine ⟨17679380435030630269469591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786253623353753512979727 17679380435030630269469591)
            ·
              refine ⟨26519070652545945404204387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17679380435030630269469591 26519070652545945404204387)
              ·
                refine ⟨39778605978818918106306581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26519070652545945404204387 39778605978818918106306581)
                ·
                  refine ⟨1864622155257136786233121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39778605978818918106306581 1864622155257136786233121)
                  ·
                    refine ⟨1398466616442852589674841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1864622155257136786233121 1398466616442852589674841)
                    ·
                      refine ⟨1048849962332139442256131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398466616442852589674841 1048849962332139442256131)
                      ·
                        rfl

theorem cell23_2042628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_2042628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042628 prefixEnd_2042628 := by exact prefixLift 2042628
  have htrace : WordTrace (prefixWord ++ tailWord_2042628) baseStart_2042628 baseEnd_2042628 := by
    simpa [prefixWord, tailWord_2042628, baseEnd_2042628] using wordTrace_append hprefix tailTrace_2042628
  have hstable : (prefixWord ++ tailWord_2042628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042628).length < 2 ^ (prefixWord ++ tailWord_2042628).sum := by decide
  have hdescent : baseEnd_2042628 < baseStart_2042628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042631 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_2042631 : Nat := 118140960795 + 2042631 * 2 ^ 59
def prefixEnd_2042631 : Nat := 4983230072969 + 3 ^ 40 * 2042631 * 2
def baseEnd_2042631 : Nat := 1048851502774102930518617

theorem tailTrace_2042631 : CollatzResearch.WordTrace tailWord_2042631 prefixEnd_2042631 1048851502774102930518617 := by
  unfold tailWord_2042631
  simp only [CollatzResearch.WordTrace]
  refine ⟨74500873062904215446255747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49667248708602810297503831 74500873062904215446255747)
  ·
    refine ⟨111751309594356323169383621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74500873062904215446255747 111751309594356323169383621)
    ·
      refine ⟨20953370548941810594259429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111751309594356323169383621 20953370548941810594259429)
      ·
        refine ⟨3928756977926589486423643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20953370548941810594259429 3928756977926589486423643)
        ·
          refine ⟨5893135466889884229635465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928756977926589486423643 5893135466889884229635465)
          ·
            refine ⟨4419851600167413172226599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893135466889884229635465 4419851600167413172226599)
            ·
              refine ⟨6629777400251119758339899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419851600167413172226599 6629777400251119758339899)
              ·
                refine ⟨9944666100376679637509849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629777400251119758339899 9944666100376679637509849)
                ·
                  refine ⟨7458499575282509728132387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9944666100376679637509849 7458499575282509728132387)
                  ·
                    refine ⟨11187749362923764592198581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7458499575282509728132387 11187749362923764592198581)
                    ·
                      refine ⟨1048851502774102930518617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11187749362923764592198581 1048851502774102930518617)
                      ·
                        rfl

theorem cell23_2042631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_2042631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042631 prefixEnd_2042631 := by exact prefixLift 2042631
  have htrace : WordTrace (prefixWord ++ tailWord_2042631) baseStart_2042631 baseEnd_2042631 := by
    simpa [prefixWord, tailWord_2042631, baseEnd_2042631] using wordTrace_append hprefix tailTrace_2042631
  have hstable : (prefixWord ++ tailWord_2042631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042631).length < 2 ^ (prefixWord ++ tailWord_2042631).sum := by decide
  have hdescent : baseEnd_2042631 < baseStart_2042631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042674 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2042674 : Nat := 118140960795 + 2042674 * 2 ^ 59
def prefixEnd_2042674 : Nat := 4983230072969 + 3 ^ 40 * 2042674 * 2
def baseEnd_2042674 : Nat := 1048873582442246262280919

theorem tailTrace_2042674 : CollatzResearch.WordTrace tailWord_2042674 prefixEnd_2042674 1048873582442246262280919 := by
  unfold tailWord_2042674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625610350437108447517769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49668294267832289193380717 18625610350437108447517769)
  ·
    refine ⟨13969207762827831335638327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18625610350437108447517769 13969207762827831335638327)
    ·
      refine ⟨20953811644241747003457491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13969207762827831335638327 20953811644241747003457491)
      ·
        refine ⟨31430717466362620505186237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953811644241747003457491 31430717466362620505186237)
        ·
          refine ⟨11786519049885982689444839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31430717466362620505186237 11786519049885982689444839)
          ·
            refine ⟨17679778574828974034167259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786519049885982689444839 17679778574828974034167259)
            ·
              refine ⟨26519667862243461051250889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17679778574828974034167259 26519667862243461051250889)
              ·
                refine ⟨19889750896682595788438167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26519667862243461051250889 19889750896682595788438167)
                ·
                  refine ⟨29834626345023893682657251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19889750896682595788438167 29834626345023893682657251)
                  ·
                    refine ⟨44751939517535840523985877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29834626345023893682657251 44751939517535840523985877)
                    ·
                      refine ⟨1048873582442246262280919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44751939517535840523985877 1048873582442246262280919)
                      ·
                        rfl

theorem cell23_2042674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2042674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042674 prefixEnd_2042674 := by exact prefixLift 2042674
  have htrace : WordTrace (prefixWord ++ tailWord_2042674) baseStart_2042674 baseEnd_2042674 := by
    simpa [prefixWord, tailWord_2042674, baseEnd_2042674] using wordTrace_append hprefix tailTrace_2042674
  have hstable : (prefixWord ++ tailWord_2042674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042674).length < 2 ^ (prefixWord ++ tailWord_2042674).sum := by decide
  have hdescent : baseEnd_2042674 < baseStart_2042674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042728 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_2042728 : Nat := 118140960795 + 2042728 * 2 ^ 59
def prefixEnd_2042728 : Nat := 4983230072969 + 3 ^ 40 * 2042728 * 2
def baseEnd_2042728 : Nat := 349633770132529683668557

theorem tailTrace_2042728 : CollatzResearch.WordTrace tailWord_2042728 prefixEnd_2042728 349633770132529683668557 := by
  unfold tailWord_2042728
  simp only [CollatzResearch.WordTrace]
  refine ⟨37252205471776400506268419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49669607295701867341691225 37252205471776400506268419)
  ·
    refine ⟨55878308207664600759402629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37252205471776400506268419 55878308207664600759402629)
    ·
      refine ⟨10477182788937112642387993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55878308207664600759402629 10477182788937112642387993)
      ·
        refine ⟨7857887091702834481790995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10477182788937112642387993 7857887091702834481790995)
        ·
          refine ⟨11786830637554251722686493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857887091702834481790995 11786830637554251722686493)
          ·
            refine ⟨4420061489082844396007435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11786830637554251722686493 4420061489082844396007435)
            ·
              refine ⟨6630092233624266594011153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420061489082844396007435 6630092233624266594011153)
              ·
                refine ⟨4972569175218199945508365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630092233624266594011153 4972569175218199945508365)
                ·
                  refine ⟨1864713440706824979565637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4972569175218199945508365 1864713440706824979565637)
                  ·
                    refine ⟨349633770132529683668557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864713440706824979565637 349633770132529683668557)
                    ·
                      rfl

theorem cell23_2042728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_2042728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042728 prefixEnd_2042728 := by exact prefixLift 2042728
  have htrace : WordTrace (prefixWord ++ tailWord_2042728) baseStart_2042728 baseEnd_2042728 := by
    simpa [prefixWord, tailWord_2042728, baseEnd_2042728] using wordTrace_append hprefix tailTrace_2042728
  have hstable : (prefixWord ++ tailWord_2042728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042728).length < 2 ^ (prefixWord ++ tailWord_2042728).sum := by decide
  have hdescent : baseEnd_2042728 < baseStart_2042728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042738 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_2042738 : Nat := 118140960795 + 2042738 * 2 ^ 59
def prefixEnd_2042738 : Nat := 4983230072969 + 3 ^ 40 * 2042738 * 2
def baseEnd_2042738 : Nat := 1048906445204134011880625

theorem tailTrace_2042738 : CollatzResearch.WordTrace tailWord_2042738 prefixEnd_2042738 1048906445204134011880625 := by
  unfold tailWord_2042738
  simp only [CollatzResearch.WordTrace]
  refine ⟨18626193918379143180100217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49669850449011048480267245 18626193918379143180100217)
  ·
    refine ⟨13969645438784357385075163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18626193918379143180100217 13969645438784357385075163)
    ·
      refine ⟨20954468158176536077612745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13969645438784357385075163 20954468158176536077612745)
      ·
        refine ⟨15715851118632402058209559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20954468158176536077612745 15715851118632402058209559)
        ·
          refine ⟨23573776677948603087314339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715851118632402058209559 23573776677948603087314339)
          ·
            refine ⟨35360665016922904630971509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23573776677948603087314339 35360665016922904630971509)
            ·
              refine ⟨3315062345336522309153579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35360665016922904630971509 3315062345336522309153579)
              ·
                refine ⟨4972593518004783463730369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315062345336522309153579 4972593518004783463730369)
                ·
                  refine ⟨3729445138503587597797777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972593518004783463730369 3729445138503587597797777)
                  ·
                    refine ⟨2797083853877690698348333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729445138503587597797777 2797083853877690698348333)
                    ·
                      refine ⟨1048906445204134011880625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797083853877690698348333 1048906445204134011880625)
                      ·
                        rfl

theorem cell23_2042738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_2042738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042738 prefixEnd_2042738 := by exact prefixLift 2042738
  have htrace : WordTrace (prefixWord ++ tailWord_2042738) baseStart_2042738 baseEnd_2042738 := by
    simpa [prefixWord, tailWord_2042738, baseEnd_2042738] using wordTrace_append hprefix tailTrace_2042738
  have hstable : (prefixWord ++ tailWord_2042738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042738).length < 2 ^ (prefixWord ++ tailWord_2042738).sum := by decide
  have hdescent : baseEnd_2042738 < baseStart_2042738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042745 : List Nat := [1, 2, 1, 3, 2, 4, 2, 3, 1, 4]
def baseStart_2042745 : Nat := 118140960795 + 2042745 * 2 ^ 59
def prefixEnd_2042745 : Nat := 4983230072969 + 3 ^ 40 * 2042745 * 2
def baseEnd_2042745 : Nat := 349636679856238494831031

theorem tailTrace_2042745 : CollatzResearch.WordTrace tailWord_2042745 prefixEnd_2042745 349636679856238494831031 := by
  unfold tailWord_2042745
  simp only [CollatzResearch.WordTrace]
  refine ⟨74505030984491212915905689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49670020656327475277270459 74505030984491212915905689)
  ·
    refine ⟨55878773238368409686929267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74505030984491212915905689 55878773238368409686929267)
    ·
      refine ⟨83818159857552614530393901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55878773238368409686929267 83818159857552614530393901)
      ·
        refine ⟨31431809946582230448897713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83818159857552614530393901 31431809946582230448897713)
        ·
          refine ⟨23573857459936672836673285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31431809946582230448897713 23573857459936672836673285)
          ·
            refine ⟨4420098273738126156876241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23573857459936672836673285 4420098273738126156876241)
            ·
              refine ⟨3315073705303594617657181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420098273738126156876241 3315073705303594617657181)
              ·
                refine ⟨1243152639488847981621443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3315073705303594617657181 1243152639488847981621443)
                ·
                  refine ⟨1864728959233271972432165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243152639488847981621443 1864728959233271972432165)
                  ·
                    refine ⟨349636679856238494831031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864728959233271972432165 349636679856238494831031)
                    ·
                      rfl

theorem cell23_2042745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 3, 1, 4].length) (baseStart_2042745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042745 prefixEnd_2042745 := by exact prefixLift 2042745
  have htrace : WordTrace (prefixWord ++ tailWord_2042745) baseStart_2042745 baseEnd_2042745 := by
    simpa [prefixWord, tailWord_2042745, baseEnd_2042745] using wordTrace_append hprefix tailTrace_2042745
  have hstable : (prefixWord ++ tailWord_2042745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042745).length < 2 ^ (prefixWord ++ tailWord_2042745).sum := by decide
  have hdescent : baseEnd_2042745 < baseStart_2042745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042785 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2042785 : Nat := 118140960795 + 2042785 * 2 ^ 59
def prefixEnd_2042785 : Nat := 4983230072969 + 3 ^ 40 * 2042785 * 2
def baseEnd_2042785 : Nat := 1048930578794895327992909

theorem tailTrace_2042785 : CollatzResearch.WordTrace tailWord_2042785 prefixEnd_2042785 1048930578794895327992909 := by
  unfold tailWord_2042785
  simp only [CollatzResearch.WordTrace]
  refine ⟨74506489904346299747361809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49670993269564199831574539 74506489904346299747361809)
  ·
    refine ⟨55879867428259724810521357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74506489904346299747361809 55879867428259724810521357)
    ·
      refine ⟨20954950285597396803945509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55879867428259724810521357 20954950285597396803945509)
      ·
        refine ⟨3929053178549511900739783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20954950285597396803945509 3929053178549511900739783)
        ·
          refine ⟨5893579767824267851109675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929053178549511900739783 5893579767824267851109675)
          ·
            refine ⟨8840369651736401776664513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893579767824267851109675 8840369651736401776664513)
            ·
              refine ⟨6630277238802301332498385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840369651736401776664513 6630277238802301332498385)
              ·
                refine ⟨4972707929101725999373789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630277238802301332498385 4972707929101725999373789)
                ·
                  refine ⟨1864765473413147249765171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4972707929101725999373789 1864765473413147249765171)
                  ·
                    refine ⟨2797148210119720874647757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1864765473413147249765171 2797148210119720874647757)
                    ·
                      refine ⟨1048930578794895327992909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797148210119720874647757 1048930578794895327992909)
                      ·
                        rfl

theorem cell23_2042785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2042785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042785 prefixEnd_2042785 := by exact prefixLift 2042785
  have htrace : WordTrace (prefixWord ++ tailWord_2042785) baseStart_2042785 baseEnd_2042785 := by
    simpa [prefixWord, tailWord_2042785, baseEnd_2042785] using wordTrace_append hprefix tailTrace_2042785
  have hstable : (prefixWord ++ tailWord_2042785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042785).length < 2 ^ (prefixWord ++ tailWord_2042785).sum := by decide
  have hdescent : baseEnd_2042785 < baseStart_2042785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042788 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_2042788 : Nat := 118140960795 + 2042788 * 2 ^ 59
def prefixEnd_2042788 : Nat := 4983230072969 + 3 ^ 40 * 2042788 * 2
def baseEnd_2042788 : Nat := 349644039745619605418465

theorem tailTrace_2042788 : CollatzResearch.WordTrace tailWord_2042788 prefixEnd_2042788 349644039745619605418465 := by
  unfold tailWord_2042788
  simp only [CollatzResearch.WordTrace]
  refine ⟨37253299661667715629860509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49671066215556954173147345 37253299661667715629860509)
  ·
    refine ⟨13969987373125393361197691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37253299661667715629860509 13969987373125393361197691)
    ·
      refine ⟨20954981059688090041796537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13969987373125393361197691 20954981059688090041796537)
      ·
        refine ⟨15716235794766067531347403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20954981059688090041796537 15716235794766067531347403)
        ·
          refine ⟨23574353692149101297021105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15716235794766067531347403 23574353692149101297021105)
          ·
            refine ⟨17680765269111825972765829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23574353692149101297021105 17680765269111825972765829)
            ·
              refine ⟨3315143487958467369893593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17680765269111825972765829 3315143487958467369893593)
              ·
                refine ⟨2486357615968850527420195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315143487958467369893593 2486357615968850527420195)
                ·
                  refine ⟨3729536423953275791130293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486357615968850527420195 3729536423953275791130293)
                  ·
                    refine ⟨349644039745619605418465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3729536423953275791130293 349644039745619605418465)
                    ·
                      rfl

theorem cell23_2042788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_2042788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042788 prefixEnd_2042788 := by exact prefixLift 2042788
  have htrace : WordTrace (prefixWord ++ tailWord_2042788) baseStart_2042788 baseEnd_2042788 := by
    simpa [prefixWord, tailWord_2042788, baseEnd_2042788] using wordTrace_append hprefix tailTrace_2042788
  have hstable : (prefixWord ++ tailWord_2042788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042788).length < 2 ^ (prefixWord ++ tailWord_2042788).sum := by decide
  have hdescent : baseEnd_2042788 < baseStart_2042788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042808 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4]
def baseStart_2042808 : Nat := 118140960795 + 2042808 * 2 ^ 59
def prefixEnd_2042808 : Nat := 4983230072969 + 3 ^ 40 * 2042808 * 2
def baseEnd_2042808 : Nat := 1048942388849948738005303

theorem tailTrace_2042808 : CollatzResearch.WordTrace tailWord_2042808 prefixEnd_2042808 1048942388849948738005303 := by
  unfold tailWord_2042808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37253664391631487337724539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49671552522175316450299385 37253664391631487337724539)
  ·
    refine ⟨55880496587447231006586809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37253664391631487337724539 55880496587447231006586809)
    ·
      refine ⟨41910372440585423254940107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55880496587447231006586809 41910372440585423254940107)
      ·
        refine ⟨62865558660878134882410161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41910372440585423254940107 62865558660878134882410161)
        ·
          refine ⟨47149168995658601161807621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62865558660878134882410161 47149168995658601161807621)
          ·
            refine ⟨8840469186685987717838929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47149168995658601161807621 8840469186685987717838929)
            ·
              refine ⟨6630351890014490788379197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840469186685987717838929 6630351890014490788379197)
              ·
                refine ⟨2486381958755434045642199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6630351890014490788379197 2486381958755434045642199)
                ·
                  refine ⟨3729572938133151068463299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486381958755434045642199 3729572938133151068463299)
                  ·
                    refine ⟨5594359407199726602694949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729572938133151068463299 5594359407199726602694949)
                    ·
                      refine ⟨1048942388849948738005303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5594359407199726602694949 1048942388849948738005303)
                      ·
                        rfl

theorem cell23_2042808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_2042808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042808 prefixEnd_2042808 := by exact prefixLift 2042808
  have htrace : WordTrace (prefixWord ++ tailWord_2042808) baseStart_2042808 baseEnd_2042808 := by
    simpa [prefixWord, tailWord_2042808, baseEnd_2042808] using wordTrace_append hprefix tailTrace_2042808
  have hstable : (prefixWord ++ tailWord_2042808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042808).length < 2 ^ (prefixWord ++ tailWord_2042808).sum := by decide
  have hdescent : baseEnd_2042808 < baseStart_2042808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042828 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_2042828 : Nat := 118140960795 + 2042828 * 2 ^ 59
def prefixEnd_2042828 : Nat := 4983230072969 + 3 ^ 40 * 2042828 * 2
def baseEnd_2042828 : Nat := 1048952658463038659755211

theorem tailTrace_2042828 : CollatzResearch.WordTrace tailWord_2042828 prefixEnd_2042828 1048952658463038659755211 := by
  unfold tailWord_2042828
  simp only [CollatzResearch.WordTrace]
  refine ⟨37254029121595259045588569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49672038828793678727451425 37254029121595259045588569)
  ·
    refine ⟨27940521841196444284191427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37254029121595259045588569 27940521841196444284191427)
    ·
      refine ⟨41910782761794666426287141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27940521841196444284191427 41910782761794666426287141)
      ·
        refine ⟨7858271767836499954928839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41910782761794666426287141 7858271767836499954928839)
        ·
          refine ⟨11787407651754749932393259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858271767836499954928839 11787407651754749932393259)
          ·
            refine ⟨17681111477632124898589889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787407651754749932393259 17681111477632124898589889)
            ·
              refine ⟨13260833608224093673942417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17681111477632124898589889 13260833608224093673942417)
              ·
                refine ⟨9945625206168070255456813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13260833608224093673942417 9945625206168070255456813)
                ·
                  refine ⟨3729609452313026345796305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9945625206168070255456813 3729609452313026345796305)
                  ·
                    refine ⟨2797207089234769759347229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729609452313026345796305 2797207089234769759347229)
                    ·
                      refine ⟨1048952658463038659755211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797207089234769759347229 1048952658463038659755211)
                      ·
                        rfl

theorem cell23_2042828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_2042828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042828 prefixEnd_2042828 := by exact prefixLift 2042828
  have htrace : WordTrace (prefixWord ++ tailWord_2042828) baseStart_2042828 baseEnd_2042828 := by
    simpa [prefixWord, tailWord_2042828, baseEnd_2042828] using wordTrace_append hprefix tailTrace_2042828
  have hstable : (prefixWord ++ tailWord_2042828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042828).length < 2 ^ (prefixWord ++ tailWord_2042828).sum := by decide
  have hdescent : baseEnd_2042828 < baseStart_2042828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042831 : List Nat := [1, 1, 2, 1, 1, 7, 2, 8]
def baseStart_2042831 : Nat := 118140960795 + 2042831 * 2 ^ 59
def prefixEnd_2042831 : Nat := 4983230072969 + 3 ^ 40 * 2042831 * 2
def baseEnd_2042831 : Nat := 38850155515000079556211

theorem tailTrace_2042831 : CollatzResearch.WordTrace tailWord_2042831 prefixEnd_2042831 38850155515000079556211 := by
  unfold tailWord_2042831
  simp only [CollatzResearch.WordTrace]
  refine ⟨74508167662179649603536347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49672111774786433069024231 74508167662179649603536347)
  ·
    refine ⟨111762251493269474405304521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74508167662179649603536347 111762251493269474405304521)
    ·
      refine ⟨83821688619952105803978391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111762251493269474405304521 83821688619952105803978391)
      ·
        refine ⟨125732532929928158705967587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83821688619952105803978391 125732532929928158705967587)
        ·
          refine ⟨188598799394892238058951381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125732532929928158705967587 188598799394892238058951381)
          ·
            refine ⟨4420284360817786829506673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188598799394892238058951381 4420284360817786829506673)
            ·
              refine ⟨3315213270613340122130005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420284360817786829506673 3315213270613340122130005)
              ·
                refine ⟨38850155515000079556211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3315213270613340122130005 38850155515000079556211)
                ·
                  rfl

theorem cell23_2042831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 8].length) (baseStart_2042831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042831 prefixEnd_2042831 := by exact prefixLift 2042831
  have htrace : WordTrace (prefixWord ++ tailWord_2042831) baseStart_2042831 baseEnd_2042831 := by
    simpa [prefixWord, tailWord_2042831, baseEnd_2042831] using wordTrace_append hprefix tailTrace_2042831
  have hstable : (prefixWord ++ tailWord_2042831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042831).length < 2 ^ (prefixWord ++ tailWord_2042831).sum := by decide
  have hdescent : baseEnd_2042831 < baseStart_2042831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042845 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_2042845 : Nat := 118140960795 + 2042845 * 2 ^ 59
def prefixEnd_2042845 : Nat := 4983230072969 + 3 ^ 40 * 2042845 * 2
def baseEnd_2042845 : Nat := 1048961387634165093242633

theorem tailTrace_2042845 : CollatzResearch.WordTrace tailWord_2042845 prefixEnd_2042845 1048961387634165093242633 := by
  unfold tailWord_2042845
  simp only [CollatzResearch.WordTrace]
  refine ⟨74508678284128929994545989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49672452189419286663030659 74508678284128929994545989)
  ·
    refine ⟨13970377178274174373977373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74508678284128929994545989 13970377178274174373977373)
    ·
      refine ⟨5238891441852815390241515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13970377178274174373977373 5238891441852815390241515)
      ·
        refine ⟨7858337162779223085362273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5238891441852815390241515 7858337162779223085362273)
        ·
          refine ⟨5893752872084417314021705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7858337162779223085362273 5893752872084417314021705)
          ·
            refine ⟨4420314654063312985516279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893752872084417314021705 4420314654063312985516279)
            ·
              refine ⟨6630471981094969478274419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420314654063312985516279 6630471981094969478274419)
              ·
                refine ⟨9945707971642454217411629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630471981094969478274419 9945707971642454217411629)
                ·
                  refine ⟨3729640489365920331529361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9945707971642454217411629 3729640489365920331529361)
                  ·
                    refine ⟨2797230367024440248647021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729640489365920331529361 2797230367024440248647021)
                    ·
                      refine ⟨1048961387634165093242633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797230367024440248647021 1048961387634165093242633)
                      ·
                        rfl

theorem cell23_2042845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_2042845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042845 prefixEnd_2042845 := by exact prefixLift 2042845
  have htrace : WordTrace (prefixWord ++ tailWord_2042845) baseStart_2042845 baseEnd_2042845 := by
    simpa [prefixWord, tailWord_2042845, baseEnd_2042845] using wordTrace_append hprefix tailTrace_2042845
  have hstable : (prefixWord ++ tailWord_2042845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042845).length < 2 ^ (prefixWord ++ tailWord_2042845).sum := by decide
  have hdescent : baseEnd_2042845 < baseStart_2042845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042858 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_2042858 : Nat := 118140960795 + 2042858 * 2 ^ 59
def prefixEnd_2042858 : Nat := 4983230072969 + 3 ^ 40 * 2042858 * 2
def baseEnd_2042858 : Nat := 1048968062882673542380073

theorem tailTrace_2042858 : CollatzResearch.WordTrace tailWord_2042858 prefixEnd_2042858 1048968062882673542380073 := by
  unfold tailWord_2042858
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627288108270458303692307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49672768288721222143179485 18627288108270458303692307)
  ·
    refine ⟨27940932162405687455538461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18627288108270458303692307 27940932162405687455538461)
    ·
      refine ⟨10477849560902132795826923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27940932162405687455538461 10477849560902132795826923)
      ·
        refine ⟨15716774341353199193740385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477849560902132795826923 15716774341353199193740385)
        ·
          refine ⟨11787580756014899395305289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15716774341353199193740385 11787580756014899395305289)
          ·
            refine ⟨8840685567011174546478967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787580756014899395305289 8840685567011174546478967)
            ·
              refine ⟨13261028350516761819718451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840685567011174546478967 13261028350516761819718451)
              ·
                refine ⟨19891542525775142729577677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261028350516761819718451 19891542525775142729577677)
                ·
                  refine ⟨7459328447165678523591629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19891542525775142729577677 7459328447165678523591629)
                  ·
                    refine ⟨2797248167687129446346861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7459328447165678523591629 2797248167687129446346861)
                    ·
                      refine ⟨1048968062882673542380073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797248167687129446346861 1048968062882673542380073)
                      ·
                        rfl

theorem cell23_2042858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_2042858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042858 prefixEnd_2042858 := by exact prefixLift 2042858
  have htrace : WordTrace (prefixWord ++ tailWord_2042858) baseStart_2042858 baseEnd_2042858 := by
    simpa [prefixWord, tailWord_2042858, baseEnd_2042858] using wordTrace_append hprefix tailTrace_2042858
  have hstable : (prefixWord ++ tailWord_2042858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042858).length < 2 ^ (prefixWord ++ tailWord_2042858).sum := by decide
  have hdescent : baseEnd_2042858 < baseStart_2042858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042862 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_2042862 : Nat := 118140960795 + 2042862 * 2 ^ 59
def prefixEnd_2042862 : Nat := 4983230072969 + 3 ^ 40 * 2042862 * 2
def baseEnd_2042862 : Nat := 1048970116805291526730055

theorem tailTrace_2042862 : CollatzResearch.WordTrace tailWord_2042862 prefixEnd_2042862 1048970116805291526730055 := by
  unfold tailWord_2042862
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313662290633417737239355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49672865550044894598609893 9313662290633417737239355)
  ·
    refine ⟨13970493435950126605859033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313662290633417737239355 13970493435950126605859033)
    ·
      refine ⟨10477870076962594954394275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13970493435950126605859033 10477870076962594954394275)
      ·
        refine ⟨15716805115443892431591413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477870076962594954394275 15716805115443892431591413)
        ·
          refine ⟨1473450479572864915461695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15716805115443892431591413 1473450479572864915461695)
          ·
            refine ⟨2210175719359297373192543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473450479572864915461695 2210175719359297373192543)
            ·
              refine ⟨3315263579038946059788815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210175719359297373192543 3315263579038946059788815)
              ·
                refine ⟨4972895368558419089683223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315263579038946059788815 4972895368558419089683223)
                ·
                  refine ⟨7459343052837628634524835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972895368558419089683223 7459343052837628634524835)
                  ·
                    refine ⟨11189014579256442951787253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7459343052837628634524835 11189014579256442951787253)
                    ·
                      refine ⟨1048970116805291526730055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11189014579256442951787253 1048970116805291526730055)
                      ·
                        rfl

theorem cell23_2042862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_2042862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042862 prefixEnd_2042862 := by exact prefixLift 2042862
  have htrace : WordTrace (prefixWord ++ tailWord_2042862) baseStart_2042862 baseEnd_2042862 := by
    simpa [prefixWord, tailWord_2042862, baseEnd_2042862] using wordTrace_append hprefix tailTrace_2042862
  have hstable : (prefixWord ++ tailWord_2042862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042862).length < 2 ^ (prefixWord ++ tailWord_2042862).sum := by decide
  have hdescent : baseEnd_2042862 < baseStart_2042862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042869 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_2042869 : Nat := 118140960795 + 2042869 * 2 ^ 59
def prefixEnd_2042869 : Nat := 4983230072969 + 3 ^ 40 * 2042869 * 2
def baseEnd_2042869 : Nat := 349657903723290999780841

theorem tailTrace_2042869 : CollatzResearch.WordTrace tailWord_2042869 prefixEnd_2042869 349657903723290999780841 := by
  unfold tailWord_2042869
  simp only [CollatzResearch.WordTrace]
  refine ⟨74509553636041982093419661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49673035757361321395613107 74509553636041982093419661)
  ·
    refine ⟨27941082613515743285032373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74509553636041982093419661 27941082613515743285032373)
    ·
      refine ⟨2619476495017100932971785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27941082613515743285032373 2619476495017100932971785)
      ·
        refine ⟨1964607371262825699728839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2619476495017100932971785 1964607371262825699728839)
        ·
          refine ⟨2946911056894238549593259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964607371262825699728839 2946911056894238549593259)
          ·
            refine ⟨4420366585341357824389889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946911056894238549593259 4420366585341357824389889)
            ·
              refine ⟨3315274939006018368292417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420366585341357824389889 3315274939006018368292417)
              ·
                refine ⟨2486456204254513776219313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315274939006018368292417 2486456204254513776219313)
                ·
                  refine ⟨1864842153190885332164485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486456204254513776219313 1864842153190885332164485)
                  ·
                    refine ⟨349657903723290999780841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1864842153190885332164485 349657903723290999780841)
                    ·
                      rfl

theorem cell23_2042869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_2042869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042869 prefixEnd_2042869 := by exact prefixLift 2042869
  have htrace : WordTrace (prefixWord ++ tailWord_2042869) baseStart_2042869 baseEnd_2042869 := by
    simpa [prefixWord, tailWord_2042869, baseEnd_2042869] using wordTrace_append hprefix tailTrace_2042869
  have hstable : (prefixWord ++ tailWord_2042869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042869).length < 2 ^ (prefixWord ++ tailWord_2042869).sum := by decide
  have hdescent : baseEnd_2042869 < baseStart_2042869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042876 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_2042876 : Nat := 118140960795 + 2042876 * 2 ^ 59
def prefixEnd_2042876 : Nat := 4983230072969 + 3 ^ 40 * 2042876 * 2
def baseEnd_2042876 : Nat := 1048977305534454471954991

theorem tailTrace_2042876 : CollatzResearch.WordTrace tailWord_2042876 prefixEnd_2042876 1048977305534454471954991 := by
  unfold tailWord_2042876
  simp only [CollatzResearch.WordTrace]
  refine ⟨37254904473508311144462241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49673205964677748192616321 37254904473508311144462241)
  ·
    refine ⟨27941178355131233358346681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37254904473508311144462241 27941178355131233358346681)
    ·
      refine ⟨20955883766348425018760011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27941178355131233358346681 20955883766348425018760011)
      ·
        refine ⟨31433825649522637528140017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20955883766348425018760011 31433825649522637528140017)
        ·
          refine ⟨23575369237141978146105013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31433825649522637528140017 23575369237141978146105013)
          ·
            refine ⟨2210190865982060451197345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23575369237141978146105013 2210190865982060451197345)
            ·
              refine ⟨1657643149486545338398009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2210190865982060451197345 1657643149486545338398009)
              ·
                refine ⟨1243232362114909003798507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1657643149486545338398009 1243232362114909003798507)
                ·
                  refine ⟨1864848543172363505697761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243232362114909003798507 1864848543172363505697761)
                  ·
                    refine ⟨1398636407379272629273321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1864848543172363505697761 1398636407379272629273321)
                    ·
                      refine ⟨1048977305534454471954991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398636407379272629273321 1048977305534454471954991)
                      ·
                        rfl

theorem cell23_2042876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_2042876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042876 prefixEnd_2042876 := by exact prefixLift 2042876
  have htrace : WordTrace (prefixWord ++ tailWord_2042876) baseStart_2042876 baseEnd_2042876 := by
    simpa [prefixWord, tailWord_2042876, baseEnd_2042876] using wordTrace_append hprefix tailTrace_2042876
  have hstable : (prefixWord ++ tailWord_2042876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042876).length < 2 ^ (prefixWord ++ tailWord_2042876).sum := by decide
  have hdescent : baseEnd_2042876 < baseStart_2042876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042882 : List Nat := [3, 4, 1, 3, 1, 2, 1, 8]
def baseStart_2042882 : Nat := 118140960795 + 2042882 * 2 ^ 59
def prefixEnd_2042882 : Nat := 4983230072969 + 3 ^ 40 * 2042882 * 2
def baseEnd_2042882 : Nat := 38851125422903016610369

theorem tailTrace_2042882 : CollatzResearch.WordTrace tailWord_2042882 prefixEnd_2042882 38851125422903016610369 := by
  unfold tailWord_2042882
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627506946248721328410725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49673351856663256875761933 18627506946248721328410725)
  ·
    refine ⟨3492657552421635249077011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18627506946248721328410725 3492657552421635249077011)
    ·
      refine ⟨5238986328632452873615517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3492657552421635249077011 5238986328632452873615517)
      ·
        refine ⟨1964619873237169827605819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5238986328632452873615517 1964619873237169827605819)
        ·
          refine ⟨2946929809855754741408729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964619873237169827605819 2946929809855754741408729)
          ·
            refine ⟨2210197357391816056056547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2946929809855754741408729 2210197357391816056056547)
            ·
              refine ⟨3315296036087724084084821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210197357391816056056547 3315296036087724084084821)
              ·
                refine ⟨38851125422903016610369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3315296036087724084084821 38851125422903016610369)
                ·
                  rfl

theorem cell23_2042882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_2042882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042882 prefixEnd_2042882 := by exact prefixLift 2042882
  have htrace : WordTrace (prefixWord ++ tailWord_2042882) baseStart_2042882 baseEnd_2042882 := by
    simpa [prefixWord, tailWord_2042882, baseEnd_2042882] using wordTrace_append hprefix tailTrace_2042882
  have hstable : (prefixWord ++ tailWord_2042882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042882).length < 2 ^ (prefixWord ++ tailWord_2042882).sum := by decide
  have hdescent : baseEnd_2042882 < baseStart_2042882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042891 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 1, 8]
def baseStart_2042891 : Nat := 118140960795 + 2042891 * 2 ^ 59
def prefixEnd_2042891 : Nat := 4983230072969 + 3 ^ 40 * 2042891 * 2
def baseEnd_2042891 : Nat := 349661669248090637755807

theorem tailTrace_2042891 : CollatzResearch.WordTrace tailWord_2042891 prefixEnd_2042891 349661669248090637755807 := by
  unfold tailWord_2042891
  simp only [CollatzResearch.WordTrace]
  refine ⟨74510356041962279850720527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49673570694641519900480351 74510356041962279850720527)
  ·
    refine ⟨111765534062943419776080791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74510356041962279850720527 111765534062943419776080791)
    ·
      refine ⟨167648301094415129664121187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111765534062943419776080791 167648301094415129664121187)
      ·
        refine ⟨251472451641622694496181781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167648301094415129664121187 251472451641622694496181781)
        ·
          refine ⟨11787771170701063804508521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251472451641622694496181781 11787771170701063804508521)
          ·
            refine ⟨8840828378025797853381391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787771170701063804508521 8840828378025797853381391)
            ·
              refine ⟨13261242567038696780072087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840828378025797853381391 13261242567038696780072087)
              ·
                refine ⟨19891863850558045170108131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261242567038696780072087 19891863850558045170108131)
                ·
                  refine ⟨29837795775837067755162197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19891863850558045170108131 29837795775837067755162197)
                  ·
                    refine ⟨349661669248090637755807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29837795775837067755162197 349661669248090637755807)
                    ·
                      rfl

theorem cell23_2042891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 8].length) (baseStart_2042891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042891 prefixEnd_2042891 := by exact prefixLift 2042891
  have htrace : WordTrace (prefixWord ++ tailWord_2042891) baseStart_2042891 baseEnd_2042891 := by
    simpa [prefixWord, tailWord_2042891, baseEnd_2042891] using wordTrace_append hprefix tailTrace_2042891
  have hstable : (prefixWord ++ tailWord_2042891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042891).length < 2 ^ (prefixWord ++ tailWord_2042891).sum := by decide
  have hdescent : baseEnd_2042891 < baseStart_2042891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042915 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 1, 4, 2]
def baseStart_2042915 : Nat := 118140960795 + 2042915 * 2 ^ 59
def prefixEnd_2042915 : Nat := 4983230072969 + 3 ^ 40 * 2042915 * 2
def baseEnd_2042915 : Nat := 1048997331279979819367311

theorem tailTrace_2042915 : CollatzResearch.WordTrace tailWord_2042915 prefixEnd_2042915 1048997331279979819367311 := by
  unfold tailWord_2042915
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511231393875331949594199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49674154262583554633062799 74511231393875331949594199)
  ·
    refine ⟨111766847090812997924391299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74511231393875331949594199 111766847090812997924391299)
    ·
      refine ⟨167650270636219496886586949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111766847090812997924391299 167650270636219496886586949)
      ·
        refine ⟨31434425744291155666235053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167650270636219496886586949 31434425744291155666235053)
        ·
          refine ⟨11787909654109183374838145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31434425744291155666235053 11787909654109183374838145)
          ·
            refine ⟨8840932240581887531128609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787909654109183374838145 8840932240581887531128609)
            ·
              refine ⟨6630699180436415648346457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840932240581887531128609 6630699180436415648346457)
              ·
                refine ⟨4973024385327311736259843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630699180436415648346457 4973024385327311736259843)
                ·
                  refine ⟨7459536577990967604389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973024385327311736259843 7459536577990967604389765)
                  ·
                    refine ⟨1398663108373306425823081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7459536577990967604389765 1398663108373306425823081)
                    ·
                      refine ⟨1048997331279979819367311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398663108373306425823081 1048997331279979819367311)
                      ·
                        rfl

theorem cell23_2042915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_2042915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042915 prefixEnd_2042915 := by exact prefixLift 2042915
  have htrace : WordTrace (prefixWord ++ tailWord_2042915) baseStart_2042915 baseEnd_2042915 := by
    simpa [prefixWord, tailWord_2042915, baseEnd_2042915] using wordTrace_append hprefix tailTrace_2042915
  have hstable : (prefixWord ++ tailWord_2042915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042915).length < 2 ^ (prefixWord ++ tailWord_2042915).sum := by decide
  have hdescent : baseEnd_2042915 < baseStart_2042915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042919 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2042919 : Nat := 118140960795 + 2042919 * 2 ^ 59
def prefixEnd_2042919 : Nat := 4983230072969 + 3 ^ 40 * 2042919 * 2
def baseEnd_2042919 : Nat := 1048999385202597803717293

theorem tailTrace_2042919 : CollatzResearch.WordTrace tailWord_2042919 prefixEnd_2042919 1048999385202597803717293 := by
  unfold tailWord_2042919
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511377285860840632739811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49674251523907227088493207 74511377285860840632739811)
  ·
    refine ⟨111767065928791260949109717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74511377285860840632739811 111767065928791260949109717)
    ·
      refine ⟨2619540607706045178494759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 111767065928791260949109717 2619540607706045178494759)
      ·
        refine ⟨3929310911559067767742139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619540607706045178494759 3929310911559067767742139)
        ·
          refine ⟨5893966367338601651613209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929310911559067767742139 5893966367338601651613209)
          ·
            refine ⟨4420474775503951238709907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893966367338601651613209 4420474775503951238709907)
            ·
              refine ⟨6630712163255926858064861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420474775503951238709907 6630712163255926858064861)
              ·
                refine ⟨2486517061220972571774323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6630712163255926858064861 2486517061220972571774323)
                ·
                  refine ⟨3729775591831458857661485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486517061220972571774323 3729775591831458857661485)
                  ·
                    refine ⟨1398665846936797071623057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3729775591831458857661485 1398665846936797071623057)
                    ·
                      refine ⟨1048999385202597803717293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398665846936797071623057 1048999385202597803717293)
                      ·
                        rfl

theorem cell23_2042919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2042919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042919 prefixEnd_2042919 := by exact prefixLift 2042919
  have htrace : WordTrace (prefixWord ++ tailWord_2042919) baseStart_2042919 baseEnd_2042919 := by
    simpa [prefixWord, tailWord_2042919, baseEnd_2042919] using wordTrace_append hprefix tailTrace_2042919
  have hstable : (prefixWord ++ tailWord_2042919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042919).length < 2 ^ (prefixWord ++ tailWord_2042919).sum := by decide
  have hdescent : baseEnd_2042919 < baseStart_2042919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2042968 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 2, 5]
def baseStart_2042968 : Nat := 118140960795 + 2042968 * 2 ^ 59
def prefixEnd_2042968 : Nat := 4983230072969 + 3 ^ 40 * 2042968 * 2
def baseEnd_2042968 : Nat := 349674848584889370668189

theorem tailTrace_2042968 : CollatzResearch.WordTrace tailWord_2042968 prefixEnd_2042968 349674848584889370668189 := by
  unfold tailWord_2042968
  simp only [CollatzResearch.WordTrace]
  refine ⟨37256582231341661000636779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49675442975122214667515705 37256582231341661000636779)
  ·
    refine ⟨55884873347012491500955169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37256582231341661000636779 55884873347012491500955169)
    ·
      refine ⟨41913655010259368625716377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55884873347012491500955169 41913655010259368625716377)
      ·
        refine ⟨31435241257694526469287283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41913655010259368625716377 31435241257694526469287283)
        ·
          refine ⟨47152861886541789703930925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31435241257694526469287283 47152861886541789703930925)
          ·
            refine ⟨17682323207453171138974097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47152861886541789703930925 17682323207453171138974097)
            ·
              refine ⟨13261742405589878354230573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17682323207453171138974097 13261742405589878354230573)
              ·
                refine ⟨4973153402096204382836465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13261742405589878354230573 4973153402096204382836465)
                ·
                  refine ⟨3729865051572153287127349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973153402096204382836465 3729865051572153287127349)
                  ·
                    refine ⟨349674848584889370668189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3729865051572153287127349 349674848584889370668189)
                    ·
                      rfl

theorem cell23_2042968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_2042968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2042968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2042968 prefixEnd_2042968 := by exact prefixLift 2042968
  have htrace : WordTrace (prefixWord ++ tailWord_2042968) baseStart_2042968 baseEnd_2042968 := by
    simpa [prefixWord, tailWord_2042968, baseEnd_2042968] using wordTrace_append hprefix tailTrace_2042968
  have hstable : (prefixWord ++ tailWord_2042968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2042968).length < 2 ^ (prefixWord ++ tailWord_2042968).sum := by decide
  have hdescent : baseEnd_2042968 < baseStart_2042968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2042968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043005 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_2043005 : Nat := 118140960795 + 2043005 * 2 ^ 59
def prefixEnd_2043005 : Nat := 4983230072969 + 3 ^ 40 * 2043005 * 2
def baseEnd_2043005 : Nat := 1049043544538884467241897

theorem tailTrace_2043005 : CollatzResearch.WordTrace tailWord_2043005 prefixEnd_2043005 1049043544538884467241897 := by
  unfold tailWord_2043005
  simp only [CollatzResearch.WordTrace]
  refine ⟨74514513963549277320370469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49676342642366184880246979 74514513963549277320370469)
  ·
    refine ⟨13971471368165489497569463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74514513963549277320370469 13971471368165489497569463)
    ·
      refine ⟨20957207052248234246354195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971471368165489497569463 20957207052248234246354195)
      ·
        refine ⟨31435810578372351369531293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957207052248234246354195 31435810578372351369531293)
        ·
          refine ⟨11788428966889631763574235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31435810578372351369531293 11788428966889631763574235)
          ·
            refine ⟨17682643450334447645361353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11788428966889631763574235 17682643450334447645361353)
            ·
              refine ⟨13261982587750835734021015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17682643450334447645361353 13261982587750835734021015)
              ·
                refine ⟨19892973881626253601031523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261982587750835734021015 19892973881626253601031523)
                ·
                  refine ⟨29839460822439380401547285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19892973881626253601031523 29839460822439380401547285)
                  ·
                    refine ⟨1398724726051845956322529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29839460822439380401547285 1398724726051845956322529)
                    ·
                      refine ⟨1049043544538884467241897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398724726051845956322529 1049043544538884467241897)
                      ·
                        rfl

theorem cell23_2043005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_2043005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043005 prefixEnd_2043005 := by exact prefixLift 2043005
  have htrace : WordTrace (prefixWord ++ tailWord_2043005) baseStart_2043005 baseEnd_2043005 := by
    simpa [prefixWord, tailWord_2043005, baseEnd_2043005] using wordTrace_append hprefix tailTrace_2043005
  have hstable : (prefixWord ++ tailWord_2043005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043005).length < 2 ^ (prefixWord ++ tailWord_2043005).sum := by decide
  have hdescent : baseEnd_2043005 < baseStart_2043005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043008 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3]
def baseStart_2043008 : Nat := 118140960795 + 2043008 * 2 ^ 59
def prefixEnd_2043008 : Nat := 4983230072969 + 3 ^ 40 * 2043008 * 2
def baseEnd_2043008 : Nat := 1049045084980847955504383

theorem tailTrace_2043008 : CollatzResearch.WordTrace tailWord_2043008 prefixEnd_2043008 1049045084980847955504383 := by
  unfold tailWord_2043008
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257311691269204416364839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49676415588358939221819785 37257311691269204416364839)
  ·
    refine ⟨55885967536903806624547259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37257311691269204416364839 55885967536903806624547259)
    ·
      refine ⟨83828951305355709936820889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55885967536903806624547259 83828951305355709936820889)
      ·
        refine ⟨62871713479016782452615667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83828951305355709936820889 62871713479016782452615667)
        ·
          refine ⟨94307570218525173678923501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62871713479016782452615667 94307570218525173678923501)
          ·
            refine ⟨35365338831946940129596313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94307570218525173678923501 35365338831946940129596313)
            ·
              refine ⟨26524004123960205097197235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35365338831946940129596313 26524004123960205097197235)
              ·
                refine ⟨39786006185940307645795853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26524004123960205097197235 39786006185940307645795853)
                ·
                  refine ⟨14919752319727615367173445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39786006185940307645795853 14919752319727615367173445)
                  ·
                    refine ⟨2797453559948927881345021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14919752319727615367173445 2797453559948927881345021)
                    ·
                      refine ⟨1049045084980847955504383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797453559948927881345021 1049045084980847955504383)
                      ·
                        rfl

theorem cell23_2043008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_2043008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043008 prefixEnd_2043008 := by exact prefixLift 2043008
  have htrace : WordTrace (prefixWord ++ tailWord_2043008) baseStart_2043008 baseEnd_2043008 := by
    simpa [prefixWord, tailWord_2043008, baseEnd_2043008] using wordTrace_append hprefix tailTrace_2043008
  have hstable : (prefixWord ++ tailWord_2043008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043008).length < 2 ^ (prefixWord ++ tailWord_2043008).sum := by decide
  have hdescent : baseEnd_2043008 < baseStart_2043008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043022 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_2043022 : Nat := 118140960795 + 2043022 * 2 ^ 59
def prefixEnd_2043022 : Nat := 4983230072969 + 3 ^ 40 * 2043022 * 2
def baseEnd_2043022 : Nat := 1049052273710010900729319

theorem tailTrace_2043022 : CollatzResearch.WordTrace tailWord_2043022 prefixEnd_2043022 1049052273710010900729319 := by
  unfold tailWord_2043022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314391750560961152967415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49676756002991792815826213 9314391750560961152967415)
  ·
    refine ⟨13971587625841441729451123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9314391750560961152967415 13971587625841441729451123)
    ·
      refine ⟨20957381438762162594176685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971587625841441729451123 20957381438762162594176685)
      ·
        refine ⟨7859018039535810972816257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20957381438762162594176685 7859018039535810972816257)
        ·
          refine ⟨5894263529651858229612193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7859018039535810972816257 5894263529651858229612193)
          ·
            refine ⟨4420697647238893672209145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894263529651858229612193 4420697647238893672209145)
            ·
              refine ⟨3315523235429170254156859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420697647238893672209145 3315523235429170254156859)
              ·
                refine ⟨4973284853143755381235289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315523235429170254156859 4973284853143755381235289)
                ·
                  refine ⟨3729963639857816535926467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973284853143755381235289 3729963639857816535926467)
                  ·
                    refine ⟨5594945459786724803889701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729963639857816535926467 5594945459786724803889701)
                    ·
                      refine ⟨1049052273710010900729319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5594945459786724803889701 1049052273710010900729319)
                      ·
                        rfl

theorem cell23_2043022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_2043022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043022 prefixEnd_2043022 := by exact prefixLift 2043022
  have htrace : WordTrace (prefixWord ++ tailWord_2043022) baseStart_2043022 baseEnd_2043022 := by
    simpa [prefixWord, tailWord_2043022, baseEnd_2043022] using wordTrace_append hprefix tailTrace_2043022
  have hstable : (prefixWord ++ tailWord_2043022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043022).length < 2 ^ (prefixWord ++ tailWord_2043022).sum := by decide
  have hdescent : baseEnd_2043022 < baseStart_2043022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043045 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 6]
def baseStart_2043045 : Nat := 118140960795 + 2043045 * 2 ^ 59
def prefixEnd_2043045 : Nat := 4983230072969 + 3 ^ 40 * 2043045 * 2
def baseEnd_2043045 : Nat := 116562675973896034526857

theorem tailTrace_2043045 : CollatzResearch.WordTrace tailWord_2043045 prefixEnd_2043045 116562675973896034526857 := by
  unfold tailWord_2043045
  simp only [CollatzResearch.WordTrace]
  refine ⟨74515972883404364151826589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49677315255602909434551059 74515972883404364151826589)
  ·
    refine ⟨27943489831276636556934971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74515972883404364151826589 27943489831276636556934971)
    ·
      refine ⟨41915234746914954835402457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27943489831276636556934971 41915234746914954835402457)
      ·
        refine ⟨31436426060186216126551843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41915234746914954835402457 31436426060186216126551843)
        ·
          refine ⟨47154639090279324189827765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31436426060186216126551843 47154639090279324189827765)
          ·
            refine ⟨4420747414713686642796353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47154639090279324189827765 4420747414713686642796353)
            ·
              refine ⟨3315560561035264982097265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420747414713686642796353 3315560561035264982097265)
              ·
                refine ⟨2486670420776448736572949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3315560561035264982097265 2486670420776448736572949)
                ·
                  refine ⟨116562675973896034526857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2486670420776448736572949 116562675973896034526857)
                  ·
                    rfl

theorem cell23_2043045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_2043045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043045 prefixEnd_2043045 := by exact prefixLift 2043045
  have htrace : WordTrace (prefixWord ++ tailWord_2043045) baseStart_2043045 baseEnd_2043045 := by
    simpa [prefixWord, tailWord_2043045, baseEnd_2043045] using wordTrace_append hprefix tailTrace_2043045
  have hstable : (prefixWord ++ tailWord_2043045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043045).length < 2 ^ (prefixWord ++ tailWord_2043045).sum := by decide
  have hdescent : baseEnd_2043045 < baseStart_2043045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043076 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_2043076 : Nat := 118140960795 + 2043076 * 2 ^ 59
def prefixEnd_2043076 : Nat := 4983230072969 + 3 ^ 40 * 2043076 * 2
def baseEnd_2043076 : Nat := 1049080001665353689454071

theorem tailTrace_2043076 : CollatzResearch.WordTrace tailWord_2043076 prefixEnd_2043076 1049080001665353689454071 := by
  unfold tailWord_2043076
  simp only [CollatzResearch.WordTrace]
  refine ⟨37258551773146028223102541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49678069030861370964136721 37258551773146028223102541)
  ·
    refine ⟨13971956914929760583663453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37258551773146028223102541 13971956914929760583663453)
    ·
      refine ⟨5239483843098660218873795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13971956914929760583663453 5239483843098660218873795)
      ·
        refine ⟨7859225764647990328310693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5239483843098660218873795 7859225764647990328310693)
        ·
          refine ⟨1473604830871498186558255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7859225764647990328310693 1473604830871498186558255)
          ·
            refine ⟨2210407246307247279837383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473604830871498186558255 2210407246307247279837383)
            ·
              refine ⟨3315610869460870919756075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210407246307247279837383 3315610869460870919756075)
              ·
                refine ⟨4973416304191306379634113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315610869460870919756075 4973416304191306379634113)
                ·
                  refine ⟨3730062228143479784725585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973416304191306379634113 3730062228143479784725585)
                  ·
                    refine ⟨2797546671107609838544189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730062228143479784725585 2797546671107609838544189)
                    ·
                      refine ⟨1049080001665353689454071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797546671107609838544189 1049080001665353689454071)
                      ·
                        rfl

theorem cell23_2043076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_2043076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043076 prefixEnd_2043076 := by exact prefixLift 2043076
  have htrace : WordTrace (prefixWord ++ tailWord_2043076) baseStart_2043076 baseEnd_2043076 := by
    simpa [prefixWord, tailWord_2043076, baseEnd_2043076] using wordTrace_append hprefix tailTrace_2043076
  have hstable : (prefixWord ++ tailWord_2043076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043076).length < 2 ^ (prefixWord ++ tailWord_2043076).sum := by decide
  have hdescent : baseEnd_2043076 < baseStart_2043076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043082 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_2043082 : Nat := 118140960795 + 2043082 * 2 ^ 59
def prefixEnd_2043082 : Nat := 4983230072969 + 3 ^ 40 * 2043082 * 2
def baseEnd_2043082 : Nat := 1049083082549280665979043

theorem tailTrace_2043082 : CollatzResearch.WordTrace tailWord_2043082 prefixEnd_2043082 1049083082549280665979043 := by
  unfold tailWord_2043082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18629330596067579867730875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49678214922846879647282333 18629330596067579867730875)
  ·
    refine ⟨27943995894101369801596313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18629330596067579867730875 27943995894101369801596313)
    ·
      refine ⟨20957996920576027351197235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27943995894101369801596313 20957996920576027351197235)
      ·
        refine ⟨31436995380864041026795853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957996920576027351197235 31436995380864041026795853)
        ·
          refine ⟨11788873267824015385048445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31436995380864041026795853 11788873267824015385048445)
          ·
            refine ⟨4420827475434005769393167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11788873267824015385048445 4420827475434005769393167)
            ·
              refine ⟨6631241213151008654089751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420827475434005769393167 6631241213151008654089751)
              ·
                refine ⟨9946861819726512981134627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631241213151008654089751 9946861819726512981134627)
                ·
                  refine ⟨14920292729589769471701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9946861819726512981134627 14920292729589769471701941)
                  ·
                    refine ⟨1398777443399040887972057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14920292729589769471701941 1398777443399040887972057)
                    ·
                      refine ⟨1049083082549280665979043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398777443399040887972057 1049083082549280665979043)
                      ·
                        rfl

theorem cell23_2043082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_2043082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043082 prefixEnd_2043082 := by exact prefixLift 2043082
  have htrace : WordTrace (prefixWord ++ tailWord_2043082) baseStart_2043082 baseEnd_2043082 := by
    simpa [prefixWord, tailWord_2043082, baseEnd_2043082] using wordTrace_append hprefix tailTrace_2043082
  have hstable : (prefixWord ++ tailWord_2043082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043082).length < 2 ^ (prefixWord ++ tailWord_2043082).sum := by decide
  have hdescent : baseEnd_2043082 < baseStart_2043082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043115 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5]
def baseStart_2043115 : Nat := 118140960795 + 2043115 * 2 ^ 59
def prefixEnd_2043115 : Nat := 4983230072969 + 3 ^ 40 * 2043115 * 2
def baseEnd_2043115 : Nat := 1049100027410879036866391

theorem tailTrace_2043115 : CollatzResearch.WordTrace tailWord_2043115 prefixEnd_2043115 1049100027410879036866391 := by
  unfold tailWord_2043115
  simp only [CollatzResearch.WordTrace]
  refine ⟨74518525993150766106874799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49679017328767177404583199 74518525993150766106874799)
  ·
    refine ⟨111777788989726149160312199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74518525993150766106874799 111777788989726149160312199)
    ·
      refine ⟨167666683484589223740468299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111777788989726149160312199 167666683484589223740468299)
      ·
        refine ⟨251500025226883835610702449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167666683484589223740468299 251500025226883835610702449)
        ·
          refine ⟨188625018920162876708026837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251500025226883835610702449 188625018920162876708026837)
          ·
            refine ⟨4420898880941317422844379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 188625018920162876708026837 4420898880941317422844379)
            ·
              refine ⟨6631348321411976134266569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420898880941317422844379 6631348321411976134266569)
              ·
                refine ⟨4973511241058982100699927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6631348321411976134266569 4973511241058982100699927)
                ·
                  refine ⟨7460266861588473151049891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973511241058982100699927 7460266861588473151049891)
                  ·
                    refine ⟨11190400292382709726574837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460266861588473151049891 11190400292382709726574837)
                    ·
                      refine ⟨1049100027410879036866391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11190400292382709726574837 1049100027410879036866391)
                      ·
                        rfl

theorem cell23_2043115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_2043115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043115 prefixEnd_2043115 := by exact prefixLift 2043115
  have htrace : WordTrace (prefixWord ++ tailWord_2043115) baseStart_2043115 baseEnd_2043115 := by
    simpa [prefixWord, tailWord_2043115, baseEnd_2043115] using wordTrace_append hprefix tailTrace_2043115
  have hstable : (prefixWord ++ tailWord_2043115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043115).length < 2 ^ (prefixWord ++ tailWord_2043115).sum := by decide
  have hdescent : baseEnd_2043115 < baseStart_2043115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043135 : List Nat := [1, 1, 2, 2, 1, 5, 4, 7]
def baseStart_2043135 : Nat := 118140960795 + 2043135 * 2 ^ 59
def prefixEnd_2043135 : Nat := 4983230072969 + 3 ^ 40 * 2043135 * 2
def baseEnd_2043135 : Nat := 38855936926813665133937

theorem tailTrace_2043135 : CollatzResearch.WordTrace tailWord_2043135 prefixEnd_2043135 38855936926813665133937 := by
  unfold tailWord_2043135
  simp only [CollatzResearch.WordTrace]
  refine ⟨74519255453078309522602859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49679503635385539681735239 74519255453078309522602859)
  ·
    refine ⟨111778883179617464283904289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74519255453078309522602859 111778883179617464283904289)
    ·
      refine ⟨83834162384713098212928217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111778883179617464283904289 83834162384713098212928217)
      ·
        refine ⟨62875621788534823659696163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83834162384713098212928217 62875621788534823659696163)
        ·
          refine ⟨94313432682802235489544245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62875621788534823659696163 94313432682802235489544245)
          ·
            refine ⟨8841884314012709577144773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94313432682802235489544245 8841884314012709577144773)
            ·
              refine ⟨1657853308877383045714645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8841884314012709577144773 1657853308877383045714645)
              ·
                refine ⟨38855936926813665133937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1657853308877383045714645 38855936926813665133937)
                ·
                  rfl

theorem cell23_2043135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 7].length) (baseStart_2043135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043135 prefixEnd_2043135 := by exact prefixLift 2043135
  have htrace : WordTrace (prefixWord ++ tailWord_2043135) baseStart_2043135 baseEnd_2043135 := by
    simpa [prefixWord, tailWord_2043135, baseEnd_2043135] using wordTrace_append hprefix tailTrace_2043135
  have hstable : (prefixWord ++ tailWord_2043135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043135).length < 2 ^ (prefixWord ++ tailWord_2043135).sum := by decide
  have hdescent : baseEnd_2043135 < baseStart_2043135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043145 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_2043145 : Nat := 118140960795 + 2043145 * 2 ^ 59
def prefixEnd_2043145 : Nat := 4983230072969 + 3 ^ 40 * 2043145 * 2
def baseEnd_2043145 : Nat := 1049115431830513919491253

theorem tailTrace_2043145 : CollatzResearch.WordTrace tailWord_2043145 prefixEnd_2043145 1049115431830513919491253 := by
  unfold tailWord_2043145
  simp only [CollatzResearch.WordTrace]
  refine ⟨74519620183042081230466889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49679746788694720820311259 74519620183042081230466889)
  ·
    refine ⟨55889715137281560922850167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74519620183042081230466889 55889715137281560922850167)
    ·
      refine ⟨83834572705922341384275251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55889715137281560922850167 83834572705922341384275251)
      ·
        refine ⟨125751859058883512076412877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83834572705922341384275251 125751859058883512076412877)
        ·
          refine ⟨47156947147081317028654829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125751859058883512076412877 47156947147081317028654829)
          ·
            refine ⟨17683855180155493885745561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47156947147081317028654829 17683855180155493885745561)
            ·
              refine ⟨13262891385116620414309171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17683855180155493885745561 13262891385116620414309171)
              ·
                refine ⟨19894337077674930621463757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13262891385116620414309171 19894337077674930621463757)
                ·
                  refine ⟨7460376404128098983048909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19894337077674930621463757 7460376404128098983048909)
                  ·
                    refine ⟨2797641151548037118643341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7460376404128098983048909 2797641151548037118643341)
                    ·
                      refine ⟨1049115431830513919491253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797641151548037118643341 1049115431830513919491253)
                      ·
                        rfl

theorem cell23_2043145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_2043145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043145 prefixEnd_2043145 := by exact prefixLift 2043145
  have htrace : WordTrace (prefixWord ++ tailWord_2043145) baseStart_2043145 baseEnd_2043145 := by
    simpa [prefixWord, tailWord_2043145, baseEnd_2043145] using wordTrace_append hprefix tailTrace_2043145
  have hstable : (prefixWord ++ tailWord_2043145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043145).length < 2 ^ (prefixWord ++ tailWord_2043145).sum := by decide
  have hdescent : baseEnd_2043145 < baseStart_2043145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043189 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_2043189 : Nat := 118140960795 + 2043189 * 2 ^ 59
def prefixEnd_2043189 : Nat := 4983230072969 + 3 ^ 40 * 2043189 * 2
def baseEnd_2043189 : Nat := 1049138024979311747341051

theorem tailTrace_2043189 : CollatzResearch.WordTrace tailWord_2043189 prefixEnd_2043189 1049138024979311747341051 := by
  unfold tailWord_2043189
  simp only [CollatzResearch.WordTrace]
  refine ⟨74521224994882676745068621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49680816663255117830045747 74521224994882676745068621)
  ·
    refine ⟨27945459373081003779400733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74521224994882676745068621 27945459373081003779400733)
    ·
      refine ⟨10479547264905376417275275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27945459373081003779400733 10479547264905376417275275)
      ·
        refine ⟨15719320897358064625912913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10479547264905376417275275 15719320897358064625912913)
        ·
          refine ⟨11789490673018548469434685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15719320897358064625912913 11789490673018548469434685)
          ·
            refine ⟨4421059002381955676038007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11789490673018548469434685 4421059002381955676038007)
            ·
              refine ⟨6631588503572933514057011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421059002381955676038007 6631588503572933514057011)
              ·
                refine ⟨9947382755359400271085517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631588503572933514057011 9947382755359400271085517)
                ·
                  refine ⟨3730268533259775101657069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9947382755359400271085517 3730268533259775101657069)
                  ·
                    refine ⟨1398850699972415663121401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730268533259775101657069 1398850699972415663121401)
                    ·
                      refine ⟨1049138024979311747341051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398850699972415663121401 1049138024979311747341051)
                      ·
                        rfl

theorem cell23_2043189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_2043189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043189 prefixEnd_2043189 := by exact prefixLift 2043189
  have htrace : WordTrace (prefixWord ++ tailWord_2043189) baseStart_2043189 baseEnd_2043189 := by
    simpa [prefixWord, tailWord_2043189, baseEnd_2043189] using wordTrace_append hprefix tailTrace_2043189
  have hstable : (prefixWord ++ tailWord_2043189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043189).length < 2 ^ (prefixWord ++ tailWord_2043189).sum := by decide
  have hdescent : baseEnd_2043189 < baseStart_2043189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043205 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_2043205 : Nat := 118140960795 + 2043205 * 2 ^ 59
def prefixEnd_2043205 : Nat := 4983230072969 + 3 ^ 40 * 2043205 * 2
def baseEnd_2043205 : Nat := 1049146240669783684740977

theorem tailTrace_2043205 : CollatzResearch.WordTrace tailWord_2043205 prefixEnd_2043205 1049146240669783684740977 := by
  unfold tailWord_2043205
  simp only [CollatzResearch.WordTrace]
  refine ⟨74521808562824711477651069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49681205708549807651767379 74521808562824711477651069)
  ·
    refine ⟨27945678211059266804119151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74521808562824711477651069 27945678211059266804119151)
    ·
      refine ⟨41918517316588900206178727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945678211059266804119151 41918517316588900206178727)
      ·
        refine ⟨62877775974883350309268091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41918517316588900206178727 62877775974883350309268091)
        ·
          refine ⟨94316663962325025463902137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62877775974883350309268091 94316663962325025463902137)
          ·
            refine ⟨70737497971743769097926603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94316663962325025463902137 70737497971743769097926603)
            ·
              refine ⟨106106246957615653646889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70737497971743769097926603 106106246957615653646889905)
              ·
                refine ⟨79579685218211740235167429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106106246957615653646889905 79579685218211740235167429)
                ·
                  refine ⟨14921190978414701294093893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79579685218211740235167429 14921190978414701294093893)
                  ·
                    refine ⟨2797723308452756492642605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14921190978414701294093893 2797723308452756492642605)
                    ·
                      refine ⟨1049146240669783684740977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797723308452756492642605 1049146240669783684740977)
                      ·
                        rfl

theorem cell23_2043205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_2043205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043205 prefixEnd_2043205 := by exact prefixLift 2043205
  have htrace : WordTrace (prefixWord ++ tailWord_2043205) baseStart_2043205 baseEnd_2043205 := by
    simpa [prefixWord, tailWord_2043205, baseEnd_2043205] using wordTrace_append hprefix tailTrace_2043205
  have hstable : (prefixWord ++ tailWord_2043205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043205).length < 2 ^ (prefixWord ++ tailWord_2043205).sum := by decide
  have hdescent : baseEnd_2043205 < baseStart_2043205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043232 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_2043232 : Nat := 118140960795 + 2043232 * 2 ^ 59
def prefixEnd_2043232 : Nat := 4983230072969 + 3 ^ 40 * 2043232 * 2
def baseEnd_2043232 : Nat := 1049160104647455079103353

theorem tailTrace_2043232 : CollatzResearch.WordTrace tailWord_2043232 prefixEnd_2043232 1049160104647455079103353 := by
  unfold tailWord_2043232
  simp only [CollatzResearch.WordTrace]
  refine ⟨37261396666863447544441975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49681862222484596725922633 37261396666863447544441975)
  ·
    refine ⟨55892095000295171316662963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37261396666863447544441975 55892095000295171316662963)
    ·
      refine ⟨83838142500442756974994445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55892095000295171316662963 83838142500442756974994445)
      ·
        refine ⟨31439303437666033865622917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83838142500442756974994445 31439303437666033865622917)
        ·
          refine ⟨5894869394562381349804297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31439303437666033865622917 5894869394562381349804297)
          ·
            refine ⟨4421152045921786012353223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5894869394562381349804297 4421152045921786012353223)
            ·
              refine ⟨6631728068882679018529835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421152045921786012353223 6631728068882679018529835)
              ·
                refine ⟨9947592103324018527794753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631728068882679018529835 9947592103324018527794753)
                ·
                  refine ⟨7460694077493013895846065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9947592103324018527794753 7460694077493013895846065)
                  ·
                    refine ⟨5595520558119760421884549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460694077493013895846065 5595520558119760421884549)
                    ·
                      refine ⟨1049160104647455079103353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5595520558119760421884549 1049160104647455079103353)
                      ·
                        rfl

theorem cell23_2043232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_2043232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043232 prefixEnd_2043232 := by exact prefixLift 2043232
  have htrace : WordTrace (prefixWord ++ tailWord_2043232) baseStart_2043232 baseEnd_2043232 := by
    simpa [prefixWord, tailWord_2043232, baseEnd_2043232] using wordTrace_append hprefix tailTrace_2043232
  have hstable : (prefixWord ++ tailWord_2043232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043232).length < 2 ^ (prefixWord ++ tailWord_2043232).sum := by decide
  have hdescent : baseEnd_2043232 < baseStart_2043232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043236 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_2043236 : Nat := 118140960795 + 2043236 * 2 ^ 59
def prefixEnd_2043236 : Nat := 4983230072969 + 3 ^ 40 * 2043236 * 2
def baseEnd_2043236 : Nat := 1049162158570073063453335

theorem tailTrace_2043236 : CollatzResearch.WordTrace tailWord_2043236 prefixEnd_2043236 1049162158570073063453335 := by
  unfold tailWord_2043236
  simp only [CollatzResearch.WordTrace]
  refine ⟨37261469612856201886014781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49681959483808269181353041 37261469612856201886014781)
  ·
    refine ⟨13973051104821075707255543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37261469612856201886014781 13973051104821075707255543)
    ·
      refine ⟨20959576657231613560883315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13973051104821075707255543 20959576657231613560883315)
      ·
        refine ⟨31439364985847420341324973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20959576657231613560883315 31439364985847420341324973)
        ·
          refine ⟨11789761869692782627996865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31439364985847420341324973 11789761869692782627996865)
          ·
            refine ⟨8842321402269586970997649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11789761869692782627996865 8842321402269586970997649)
            ·
              refine ⟨6631741051702190228248237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8842321402269586970997649 6631741051702190228248237)
              ·
                refine ⟨2486902894388321335593089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6631741051702190228248237 2486902894388321335593089)
                ·
                  refine ⟨1865177170791241001694817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2486902894388321335593089 1865177170791241001694817)
                  ·
                    refine ⟨1398882878093430751271113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865177170791241001694817 1398882878093430751271113)
                    ·
                      refine ⟨1049162158570073063453335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1398882878093430751271113 1049162158570073063453335)
                      ·
                        rfl

theorem cell23_2043236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_2043236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043236 prefixEnd_2043236 := by exact prefixLift 2043236
  have htrace : WordTrace (prefixWord ++ tailWord_2043236) baseStart_2043236 baseEnd_2043236 := by
    simpa [prefixWord, tailWord_2043236, baseEnd_2043236] using wordTrace_append hprefix tailTrace_2043236
  have hstable : (prefixWord ++ tailWord_2043236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043236).length < 2 ^ (prefixWord ++ tailWord_2043236).sum := by decide
  have hdescent : baseEnd_2043236 < baseStart_2043236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043255 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 1, 7]
def baseStart_2043255 : Nat := 118140960795 + 2043255 * 2 ^ 59
def prefixEnd_2043255 : Nat := 4983230072969 + 3 ^ 40 * 2043255 * 2
def baseEnd_2043255 : Nat := 349723971567502829705249

theorem tailTrace_2043255 : CollatzResearch.WordTrace tailWord_2043255 prefixEnd_2043255 349723971567502829705249 := by
  unfold tailWord_2043255
  simp only [CollatzResearch.WordTrace]
  refine ⟨74523632212643570016971219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49682421475095713344647479 74523632212643570016971219)
  ·
    refine ⟨111785448318965355025456829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74523632212643570016971219 111785448318965355025456829)
    ·
      refine ⟨41919543119612008134546311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111785448318965355025456829 41919543119612008134546311)
      ·
        refine ⟨62879314679418012201819467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41919543119612008134546311 62879314679418012201819467)
        ·
          refine ⟨94318972019127018302729201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62879314679418012201819467 94318972019127018302729201)
          ·
            refine ⟨70739229014345263727046901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94318972019127018302729201 70739229014345263727046901)
            ·
              refine ⟨6631802720094868474410647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70739229014345263727046901 6631802720094868474410647)
              ·
                refine ⟨9947704080142302711615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631802720094868474410647 9947704080142302711615971)
                ·
                  refine ⟨14921556120213454067423957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947704080142302711615971 14921556120213454067423957)
                  ·
                    refine ⟨349723971567502829705249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14921556120213454067423957 349723971567502829705249)
                    ·
                      rfl

theorem cell23_2043255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_2043255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043255 prefixEnd_2043255 := by exact prefixLift 2043255
  have htrace : WordTrace (prefixWord ++ tailWord_2043255) baseStart_2043255 baseEnd_2043255 := by
    simpa [prefixWord, tailWord_2043255, baseEnd_2043255] using wordTrace_append hprefix tailTrace_2043255
  have hstable : (prefixWord ++ tailWord_2043255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043255).length < 2 ^ (prefixWord ++ tailWord_2043255).sum := by decide
  have hdescent : baseEnd_2043255 < baseStart_2043255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043309 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_2043309 : Nat := 118140960795 + 2043309 * 2 ^ 59
def prefixEnd_2043309 : Nat := 4983230072969 + 3 ^ 40 * 2043309 * 2
def baseEnd_2043309 : Nat := 1049199642657851277840499

theorem tailTrace_2043309 : CollatzResearch.WordTrace tailWord_2043309 prefixEnd_2043309 1049199642657851277840499 := by
  unfold tailWord_2043309
  simp only [CollatzResearch.WordTrace]
  refine ⟨74525601754447937239436981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49683734502965291492957987 74525601754447937239436981)
  ·
    refine ⟨6986775164479494116197217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74525601754447937239436981 6986775164479494116197217)
    ·
      refine ⟨5240081373359620587147913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6986775164479494116197217 5240081373359620587147913)
      ·
        refine ⟨3930061030019715440360935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5240081373359620587147913 3930061030019715440360935)
        ·
          refine ⟨5895091545029573160541403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930061030019715440360935 5895091545029573160541403)
          ·
            refine ⟨8842637317544359740812105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895091545029573160541403 8842637317544359740812105)
            ·
              refine ⟨6631977988158269805609079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8842637317544359740812105 6631977988158269805609079)
              ·
                refine ⟨9947966982237404708413619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631977988158269805609079 9947966982237404708413619)
                ·
                  refine ⟨14921950473356107062620429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947966982237404708413619 14921950473356107062620429)
                  ·
                    refine ⟨5595731427508540148482661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14921950473356107062620429 5595731427508540148482661)
                    ·
                      refine ⟨1049199642657851277840499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5595731427508540148482661 1049199642657851277840499)
                      ·
                        rfl

theorem cell23_2043309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_2043309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043309 prefixEnd_2043309 := by exact prefixLift 2043309
  have htrace : WordTrace (prefixWord ++ tailWord_2043309) baseStart_2043309 baseEnd_2043309 := by
    simpa [prefixWord, tailWord_2043309, baseEnd_2043309] using wordTrace_append hprefix tailTrace_2043309
  have hstable : (prefixWord ++ tailWord_2043309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043309).length < 2 ^ (prefixWord ++ tailWord_2043309).sum := by decide
  have hdescent : baseEnd_2043309 < baseStart_2043309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043345 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_2043345 : Nat := 118140960795 + 2043345 * 2 ^ 59
def prefixEnd_2043345 : Nat := 4983230072969 + 3 ^ 40 * 2043345 * 2
def baseEnd_2043345 : Nat := 349739375987137712330111

theorem tailTrace_2043345 : CollatzResearch.WordTrace tailWord_2043345 prefixEnd_2043345 349739375987137712330111 := by
  unfold tailWord_2043345
  simp only [CollatzResearch.WordTrace]
  refine ⟨74526914782317515387747489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49684609854878343591831659 74526914782317515387747489)
  ·
    refine ⟨55895186086738136540810617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74526914782317515387747489 55895186086738136540810617)
    ·
      refine ⟨41921389565053602405607963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55895186086738136540810617 41921389565053602405607963)
      ·
        refine ⟨62882084347580403608411945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41921389565053602405607963 62882084347580403608411945)
        ·
          refine ⟨47161563260685302706308959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62882084347580403608411945 47161563260685302706308959)
          ·
            refine ⟨70742344891027954059463439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47161563260685302706308959 70742344891027954059463439)
            ·
              refine ⟨106113517336541931089195159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70742344891027954059463439 106113517336541931089195159)
              ·
                refine ⟨159170276004812896633792739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106113517336541931089195159 159170276004812896633792739)
                ·
                  refine ⟨238755414007219344950689109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159170276004812896633792739 238755414007219344950689109)
                  ·
                    refine ⟨349739375987137712330111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 238755414007219344950689109 349739375987137712330111)
                    ·
                      rfl

theorem cell23_2043345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_2043345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043345 prefixEnd_2043345 := by exact prefixLift 2043345
  have htrace : WordTrace (prefixWord ++ tailWord_2043345) baseStart_2043345 baseEnd_2043345 := by
    simpa [prefixWord, tailWord_2043345, baseEnd_2043345] using wordTrace_append hprefix tailTrace_2043345
  have hstable : (prefixWord ++ tailWord_2043345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043345).length < 2 ^ (prefixWord ++ tailWord_2043345).sum := by decide
  have hdescent : baseEnd_2043345 < baseStart_2043345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043355 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7]
def baseStart_2043355 : Nat := 118140960795 + 2043355 * 2 ^ 59
def prefixEnd_2043355 : Nat := 4983230072969 + 3 ^ 40 * 2043355 * 2
def baseEnd_2043355 : Nat := 1049223262767958097865287

theorem tailTrace_2043355 : CollatzResearch.WordTrace tailWord_2043355 prefixEnd_2043355 1049223262767958097865287 := by
  unfold tailWord_2043355
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527279512281287095611519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49684853008187524730407679 74527279512281287095611519)
  ·
    refine ⟨111790919268421930643417279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74527279512281287095611519 111790919268421930643417279)
    ·
      refine ⟨167686378902632895965125919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111790919268421930643417279 167686378902632895965125919)
      ·
        refine ⟨251529568353949343947688879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167686378902632895965125919 251529568353949343947688879)
        ·
          refine ⟨377294352530924015921533319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251529568353949343947688879 377294352530924015921533319)
          ·
            refine ⟨565941528796386023882299979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377294352530924015921533319 565941528796386023882299979)
            ·
              refine ⟨848912293194579035823449969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565941528796386023882299979 848912293194579035823449969)
              ·
                refine ⟨636684219895934276867587477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848912293194579035823449969 636684219895934276867587477)
                ·
                  refine ⟨29844572807621919228168163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 636684219895934276867587477 29844572807621919228168163)
                  ·
                    refine ⟨44766859211432878842252245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29844572807621919228168163 44766859211432878842252245)
                    ·
                      refine ⟨1049223262767958097865287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44766859211432878842252245 1049223262767958097865287)
                      ·
                        rfl

theorem cell23_2043355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_2043355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043355 prefixEnd_2043355 := by exact prefixLift 2043355
  have htrace : WordTrace (prefixWord ++ tailWord_2043355) baseStart_2043355 baseEnd_2043355 := by
    simpa [prefixWord, tailWord_2043355, baseEnd_2043355] using wordTrace_append hprefix tailTrace_2043355
  have hstable : (prefixWord ++ tailWord_2043355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043355).length < 2 ^ (prefixWord ++ tailWord_2043355).sum := by decide
  have hdescent : baseEnd_2043355 < baseStart_2043355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043359 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 3]
def baseStart_2043359 : Nat := 118140960795 + 2043359 * 2 ^ 59
def prefixEnd_2043359 : Nat := 4983230072969 + 3 ^ 40 * 2043359 * 2
def baseEnd_2043359 : Nat := 1049225316690576082215269

theorem tailTrace_2043359 : CollatzResearch.WordTrace tailWord_2043359 prefixEnd_2043359 1049225316690576082215269 := by
  unfold tailWord_2043359
  simp only [CollatzResearch.WordTrace]
  refine ⟨74527425404266795778757131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49684950269511197185838087 74527425404266795778757131)
  ·
    refine ⟨111791138106400193668135697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74527425404266795778757131 111791138106400193668135697)
    ·
      refine ⟨83843353579800145251101773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111791138106400193668135697 83843353579800145251101773)
      ·
        refine ⟨31441257592425054469163165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83843353579800145251101773 31441257592425054469163165)
        ·
          refine ⟨11790471597159395425936187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31441257592425054469163165 11790471597159395425936187)
          ·
            refine ⟨17685707395739093138904281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11790471597159395425936187 17685707395739093138904281)
            ·
              refine ⟨13264280546804319854178211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17685707395739093138904281 13264280546804319854178211)
              ·
                refine ⟨19896420820206479781267317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13264280546804319854178211 19896420820206479781267317)
                ·
                  refine ⟨1865289451894357479493811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19896420820206479781267317 1865289451894357479493811)
                  ·
                    refine ⟨2797934177841536219240717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1865289451894357479493811 2797934177841536219240717)
                    ·
                      refine ⟨1049225316690576082215269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2797934177841536219240717 1049225316690576082215269)
                      ·
                        rfl

theorem cell23_2043359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_2043359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043359 prefixEnd_2043359 := by exact prefixLift 2043359
  have htrace : WordTrace (prefixWord ++ tailWord_2043359) baseStart_2043359 baseEnd_2043359 := by
    simpa [prefixWord, tailWord_2043359, baseEnd_2043359] using wordTrace_append hprefix tailTrace_2043359
  have hstable : (prefixWord ++ tailWord_2043359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043359).length < 2 ^ (prefixWord ++ tailWord_2043359).sum := by decide
  have hdescent : baseEnd_2043359 < baseStart_2043359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043399 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_2043399 : Nat := 118140960795 + 2043399 * 2 ^ 59
def prefixEnd_2043399 : Nat := 4983230072969 + 3 ^ 40 * 2043399 * 2
def baseEnd_2043399 : Nat := 1049245855916755925715085

theorem tailTrace_2043399 : CollatzResearch.WordTrace tailWord_2043399 prefixEnd_2043399 1049245855916755925715085 := by
  unfold tailWord_2043399
  simp only [CollatzResearch.WordTrace]
  refine ⟨74528884324121882610213251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49685922882747921740142167 74528884324121882610213251)
  ·
    refine ⟨111793326486182823915319877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74528884324121882610213251 111793326486182823915319877)
    ·
      refine ⟨20961248716159279484122477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111793326486182823915319877 20961248716159279484122477)
      ·
        refine ⟨7860468268559729806545929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20961248716159279484122477 7860468268559729806545929)
        ·
          refine ⟨5895351201419797354909447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7860468268559729806545929 5895351201419797354909447)
          ·
            refine ⟨8843026802129696032364171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895351201419797354909447 8843026802129696032364171)
            ·
              refine ⟨13264540203194544048546257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8843026802129696032364171 13264540203194544048546257)
              ·
                refine ⟨9948405152395908036409693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13264540203194544048546257 9948405152395908036409693)
                ·
                  refine ⟨3730651932148465513653635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9948405152395908036409693 3730651932148465513653635)
                  ·
                    refine ⟨5595977898222698270480453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730651932148465513653635 5595977898222698270480453)
                    ·
                      refine ⟨1049245855916755925715085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5595977898222698270480453 1049245855916755925715085)
                      ·
                        rfl

theorem cell23_2043399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_2043399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043399 prefixEnd_2043399 := by exact prefixLift 2043399
  have htrace : WordTrace (prefixWord ++ tailWord_2043399) baseStart_2043399 baseEnd_2043399 := by
    simpa [prefixWord, tailWord_2043399, baseEnd_2043399] using wordTrace_append hprefix tailTrace_2043399
  have hstable : (prefixWord ++ tailWord_2043399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043399).length < 2 ^ (prefixWord ++ tailWord_2043399).sum := by decide
  have hdescent : baseEnd_2043399 < baseStart_2043399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043409 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_2043409 : Nat := 118140960795 + 2043409 * 2 ^ 59
def prefixEnd_2043409 : Nat := 4983230072969 + 3 ^ 40 * 2043409 * 2
def baseEnd_2043409 : Nat := 349750330241100295530013

theorem tailTrace_2043409 : CollatzResearch.WordTrace tailWord_2043409 prefixEnd_2043409 349750330241100295530013 := by
  unfold tailWord_2043409
  simp only [CollatzResearch.WordTrace]
  refine ⟨74529249054085654318077281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49686166036057102878718187 74529249054085654318077281)
  ·
    refine ⟨55896936790564240738557961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74529249054085654318077281 55896936790564240738557961)
    ·
      refine ⟨41922702592923180553918471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55896936790564240738557961 41922702592923180553918471)
      ·
        refine ⟨62884053889384770830877707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41922702592923180553918471 62884053889384770830877707)
        ·
          refine ⟨94326080834077156246316561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62884053889384770830877707 94326080834077156246316561)
          ·
            refine ⟨70744560625557867184737421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94326080834077156246316561 70744560625557867184737421)
            ·
              refine ⟨26529210234584200194276533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70744560625557867184737421 26529210234584200194276533)
              ·
                refine ⟨2487113459492268768213425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26529210234584200194276533 2487113459492268768213425)
                ·
                  refine ⟨1865335094619201576160069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2487113459492268768213425 1865335094619201576160069)
                  ·
                    refine ⟨349750330241100295530013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1865335094619201576160069 349750330241100295530013)
                    ·
                      rfl

theorem cell23_2043409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_2043409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043409 prefixEnd_2043409 := by exact prefixLift 2043409
  have htrace : WordTrace (prefixWord ++ tailWord_2043409) baseStart_2043409 baseEnd_2043409 := by
    simpa [prefixWord, tailWord_2043409, baseEnd_2043409] using wordTrace_append hprefix tailTrace_2043409
  have hstable : (prefixWord ++ tailWord_2043409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043409).length < 2 ^ (prefixWord ++ tailWord_2043409).sum := by decide
  have hdescent : baseEnd_2043409 < baseStart_2043409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043442 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2043442 : Nat := 118140960795 + 2043442 * 2 ^ 59
def prefixEnd_2043442 : Nat := 4983230072969 + 3 ^ 40 * 2043442 * 2
def baseEnd_2043442 : Nat := 1049267935584899257477387

theorem tailTrace_2043442 : CollatzResearch.WordTrace tailWord_2043442 prefixEnd_2043442 1049267935584899257477387 := by
  unfold tailWord_2043442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632613165741525238507145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49686968441977400636019053 18632613165741525238507145)
  ·
    refine ⟨13974459874306143928880359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18632613165741525238507145 13974459874306143928880359)
    ·
      refine ⟨20961689811459215893320539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974459874306143928880359 20961689811459215893320539)
      ·
        refine ⟨31442534717188823839980809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20961689811459215893320539 31442534717188823839980809)
        ·
          refine ⟨23581901037891617879985607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31442534717188823839980809 23581901037891617879985607)
          ·
            refine ⟨35372851556837426819978411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23581901037891617879985607 35372851556837426819978411)
            ·
              refine ⟨53059277335256140229967617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35372851556837426819978411 53059277335256140229967617)
              ·
                refine ⟨39794458001442105172475713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53059277335256140229967617 39794458001442105172475713)
                ·
                  refine ⟨29845843501081578879356785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39794458001442105172475713 29845843501081578879356785)
                  ·
                    refine ⟨22384382625811184159517589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29845843501081578879356785 22384382625811184159517589)
                    ·
                      refine ⟨1049267935584899257477387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22384382625811184159517589 1049267935584899257477387)
                      ·
                        rfl

theorem cell23_2043442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2043442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043442 prefixEnd_2043442 := by exact prefixLift 2043442
  have htrace : WordTrace (prefixWord ++ tailWord_2043442) baseStart_2043442 baseEnd_2043442 := by
    simpa [prefixWord, tailWord_2043442, baseEnd_2043442] using wordTrace_append hprefix tailTrace_2043442
  have hstable : (prefixWord ++ tailWord_2043442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043442).length < 2 ^ (prefixWord ++ tailWord_2043442).sum := by decide
  have hdescent : baseEnd_2043442 < baseStart_2043442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043463 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_2043463 : Nat := 118140960795 + 2043463 * 2 ^ 59
def prefixEnd_2043463 : Nat := 4983230072969 + 3 ^ 40 * 2043463 * 2
def baseEnd_2043463 : Nat := 1049278718678643675314791

theorem tailTrace_2043463 : CollatzResearch.WordTrace tailWord_2043463 prefixEnd_2043463 1049278718678643675314791 := by
  unfold tailWord_2043463
  simp only [CollatzResearch.WordTrace]
  refine ⟨74531218595890021540543043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49687479063926681027028695 74531218595890021540543043)
  ·
    refine ⟨111796827893835032310814565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74531218595890021540543043 111796827893835032310814565)
    ·
      refine ⟨20961905230094068558277731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111796827893835032310814565 20961905230094068558277731)
      ·
        refine ⟨31442857845141102837416597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20961905230094068558277731 31442857845141102837416597)
        ·
          refine ⟨1473883961490989195503903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31442857845141102837416597 1473883961490989195503903)
          ·
            refine ⟨2210825942236483793255855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473883961490989195503903 2210825942236483793255855)
            ·
              refine ⟨3316238913354725689883783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2210825942236483793255855 3316238913354725689883783)
              ·
                refine ⟨4974358370032088534825675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316238913354725689883783 4974358370032088534825675)
                ·
                  refine ⟨7461537555048132802238513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974358370032088534825675 7461537555048132802238513)
                  ·
                    refine ⟨5596153166286099601678885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7461537555048132802238513 5596153166286099601678885)
                    ·
                      refine ⟨1049278718678643675314791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5596153166286099601678885 1049278718678643675314791)
                      ·
                        rfl

theorem cell23_2043463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_2043463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043463 prefixEnd_2043463 := by exact prefixLift 2043463
  have htrace : WordTrace (prefixWord ++ tailWord_2043463) baseStart_2043463 baseEnd_2043463 := by
    simpa [prefixWord, tailWord_2043463, baseEnd_2043463] using wordTrace_append hprefix tailTrace_2043463
  have hstable : (prefixWord ++ tailWord_2043463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043463).length < 2 ^ (prefixWord ++ tailWord_2043463).sum := by decide
  have hdescent : baseEnd_2043463 < baseStart_2043463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043482 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_2043482 : Nat := 118140960795 + 2043482 * 2 ^ 59
def prefixEnd_2043482 : Nat := 4983230072969 + 3 ^ 40 * 2043482 * 2
def baseEnd_2043482 : Nat := 349762824937026366992401

theorem tailTrace_2043482 : CollatzResearch.WordTrace tailWord_2043482 prefixEnd_2043482 349762824937026366992401 := by
  unfold tailWord_2043482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632977895705296946371175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49687941055214125190323133 18632977895705296946371175)
  ·
    refine ⟨27949466843557945419556763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18632977895705296946371175 27949466843557945419556763)
    ·
      refine ⟨41924200265336918129335145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27949466843557945419556763 41924200265336918129335145)
      ·
        refine ⟨31443150199002688597001359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41924200265336918129335145 31443150199002688597001359)
        ·
          refine ⟨47164725298504032895502039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31443150199002688597001359 47164725298504032895502039)
          ·
            refine ⟨70747087947756049343253059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47164725298504032895502039 70747087947756049343253059)
            ·
              refine ⟨106120631921634074014879589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70747087947756049343253059 106120631921634074014879589)
              ·
                refine ⟨19897618485306388877789923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106120631921634074014879589 19897618485306388877789923)
                ·
                  refine ⟨29846427727959583316684885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19897618485306388877789923 29846427727959583316684885)
                  ·
                    refine ⟨349762824937026366992401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29846427727959583316684885 349762824937026366992401)
                    ·
                      rfl

theorem cell23_2043482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_2043482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043482 prefixEnd_2043482 := by exact prefixLift 2043482
  have htrace : WordTrace (prefixWord ++ tailWord_2043482) baseStart_2043482 baseEnd_2043482 := by
    simpa [prefixWord, tailWord_2043482, baseEnd_2043482] using wordTrace_append hprefix tailTrace_2043482
  have hstable : (prefixWord ++ tailWord_2043482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043482).length < 2 ^ (prefixWord ++ tailWord_2043482).sum := by decide
  have hdescent : baseEnd_2043482 < baseStart_2043482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043493 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_2043493 : Nat := 118140960795 + 2043493 * 2 ^ 59
def prefixEnd_2043493 : Nat := 4983230072969 + 3 ^ 40 * 2043493 * 2
def baseEnd_2043493 : Nat := 1049294123098278557939653

theorem tailTrace_2043493 : CollatzResearch.WordTrace tailWord_2043493 prefixEnd_2043493 1049294123098278557939653 := by
  unfold tailWord_2043493
  simp only [CollatzResearch.WordTrace]
  refine ⟨74532312785781336664135133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49688208523854224442756755 74532312785781336664135133)
  ·
    refine ⟨27949617294668001249050675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74532312785781336664135133 27949617294668001249050675)
    ·
      refine ⟨41924425942002001873576013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27949617294668001249050675 41924425942002001873576013)
      ·
        refine ⟨15721659728250750702591005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41924425942002001873576013 15721659728250750702591005)
        ·
          refine ⟨5895622398094031513471627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15721659728250750702591005 5895622398094031513471627)
          ·
            refine ⟨8843433597141047270207441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895622398094031513471627 8843433597141047270207441)
            ·
              refine ⟨6632575197855785452655581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8843433597141047270207441 6632575197855785452655581)
              ·
                refine ⟨2487215699195919544745843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6632575197855785452655581 2487215699195919544745843)
                ·
                  refine ⟨3730823548793879317118765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487215699195919544745843 3730823548793879317118765)
                  ·
                    refine ⟨1399058830797704743919537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3730823548793879317118765 1399058830797704743919537)
                    ·
                      refine ⟨1049294123098278557939653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399058830797704743919537 1049294123098278557939653)
                      ·
                        rfl

theorem cell23_2043493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_2043493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043493 prefixEnd_2043493 := by exact prefixLift 2043493
  have htrace : WordTrace (prefixWord ++ tailWord_2043493) baseStart_2043493 baseEnd_2043493 := by
    simpa [prefixWord, tailWord_2043493, baseEnd_2043493] using wordTrace_append hprefix tailTrace_2043493
  have hstable : (prefixWord ++ tailWord_2043493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043493).length < 2 ^ (prefixWord ++ tailWord_2043493).sum := by decide
  have hdescent : baseEnd_2043493 < baseStart_2043493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043540 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_2043540 : Nat := 118140960795 + 2043540 * 2 ^ 59
def prefixEnd_2043540 : Nat := 4983230072969 + 3 ^ 40 * 2043540 * 2
def baseEnd_2043540 : Nat := 1049318256689039874051937

theorem tailTrace_2043540 : CollatzResearch.WordTrace tailWord_2043540 prefixEnd_2043540 1049318256689039874051937 := by
  unfold tailWord_2043540
  simp only [CollatzResearch.WordTrace]
  refine ⟨37267013508305531845548037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49689351344407375794064049 37267013508305531845548037)
  ·
    refine ⟨6987565032807287221040257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37267013508305531845548037 6987565032807287221040257)
    ·
      refine ⟨5240673774605465415780193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6987565032807287221040257 5240673774605465415780193)
      ·
        refine ⟨3930505330954099061835145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5240673774605465415780193 3930505330954099061835145)
        ·
          refine ⟨2947878998215574296376359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930505330954099061835145 2947878998215574296376359)
          ·
            refine ⟨4421818497323361444564539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947878998215574296376359 4421818497323361444564539)
            ·
              refine ⟨6632727745985042166846809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421818497323361444564539 6632727745985042166846809)
              ·
                refine ⟨4974545809488781625135107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6632727745985042166846809 4974545809488781625135107)
                ·
                  refine ⟨7461818714233172437702661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4974545809488781625135107 7461818714233172437702661)
                  ·
                    refine ⟨1399091008918719832069249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7461818714233172437702661 1399091008918719832069249)
                    ·
                      refine ⟨1049318256689039874051937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399091008918719832069249 1049318256689039874051937)
                      ·
                        rfl

theorem cell23_2043540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_2043540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043540 prefixEnd_2043540 := by exact prefixLift 2043540
  have htrace : WordTrace (prefixWord ++ tailWord_2043540) baseStart_2043540 baseEnd_2043540 := by
    simpa [prefixWord, tailWord_2043540, baseEnd_2043540] using wordTrace_append hprefix tailTrace_2043540
  have hstable : (prefixWord ++ tailWord_2043540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043540).length < 2 ^ (prefixWord ++ tailWord_2043540).sum := by decide
  have hdescent : baseEnd_2043540 < baseStart_2043540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043573 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_2043573 : Nat := 118140960795 + 2043573 * 2 ^ 59
def prefixEnd_2043573 : Nat := 4983230072969 + 3 ^ 40 * 2043573 * 2
def baseEnd_2043573 : Nat := 1049335201550638244939285

theorem tailTrace_2043573 : CollatzResearch.WordTrace tailWord_2043573 prefixEnd_2043573 1049335201550638244939285 := by
  unfold tailWord_2043573
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535230625491510327047373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49690153750327673551364915 74535230625491510327047373)
  ·
    refine ⟨27950711484559316372642765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74535230625491510327047373 27950711484559316372642765)
    ·
      refine ⟨10481516806709743639741037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27950711484559316372642765 10481516806709743639741037)
      ·
        refine ⟨3930568802516153864902889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10481516806709743639741037 3930568802516153864902889)
        ·
          refine ⟨2947926601887115398677167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3930568802516153864902889 2947926601887115398677167)
          ·
            refine ⟨4421889902830673098015751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947926601887115398677167 4421889902830673098015751)
            ·
              refine ⟨6632834854246009647023627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421889902830673098015751 6632834854246009647023627)
              ·
                refine ⟨9949252281369014470535441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6632834854246009647023627 9949252281369014470535441)
                ·
                  refine ⟨7461939211026760852901581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9949252281369014470535441 7461939211026760852901581)
                  ·
                    refine ⟨2798227204135035319838093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7461939211026760852901581 2798227204135035319838093)
                    ·
                      refine ⟨1049335201550638244939285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2798227204135035319838093 1049335201550638244939285)
                      ·
                        rfl

theorem cell23_2043573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_2043573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043573 prefixEnd_2043573 := by exact prefixLift 2043573
  have htrace : WordTrace (prefixWord ++ tailWord_2043573) baseStart_2043573 baseEnd_2043573 := by
    simpa [prefixWord, tailWord_2043573, baseEnd_2043573] using wordTrace_append hprefix tailTrace_2043573
  have hstable : (prefixWord ++ tailWord_2043573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043573).length < 2 ^ (prefixWord ++ tailWord_2043573).sum := by decide
  have hdescent : baseEnd_2043573 < baseStart_2043573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043579 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4]
def baseStart_2043579 : Nat := 118140960795 + 2043579 * 2 ^ 59
def prefixEnd_2043579 : Nat := 4983230072969 + 3 ^ 40 * 2043579 * 2
def baseEnd_2043579 : Nat := 1049338282434565221464257

theorem tailTrace_2043579 : CollatzResearch.WordTrace tailWord_2043579 prefixEnd_2043579 1049338282434565221464257 := by
  unfold tailWord_2043579
  simp only [CollatzResearch.WordTrace]
  refine ⟨74535449463469773351765791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49690299642313182234510527 74535449463469773351765791)
  ·
    refine ⟨111803174195204660027648687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74535449463469773351765791 111803174195204660027648687)
    ·
      refine ⟨167704761292806990041473031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111803174195204660027648687 167704761292806990041473031)
      ·
        refine ⟨251557141939210485062209547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167704761292806990041473031 251557141939210485062209547)
        ·
          refine ⟨377335712908815727593314321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251557141939210485062209547 377335712908815727593314321)
          ·
            refine ⟨283001784681611795694985741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377335712908815727593314321 283001784681611795694985741)
            ·
              refine ⟨106125669255604423385619653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 283001784681611795694985741 106125669255604423385619653)
              ·
                refine ⟨19898562985425829384803685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106125669255604423385619653 19898562985425829384803685)
                ·
                  refine ⟨3730980559767343009650691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19898562985425829384803685 3730980559767343009650691)
                  ·
                    refine ⟨5596470839651014514476037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3730980559767343009650691 5596470839651014514476037)
                    ·
                      refine ⟨1049338282434565221464257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5596470839651014514476037 1049338282434565221464257)
                      ·
                        rfl

theorem cell23_2043579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 1, 4].length) (baseStart_2043579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043579 prefixEnd_2043579 := by exact prefixLift 2043579
  have htrace : WordTrace (prefixWord ++ tailWord_2043579) baseStart_2043579 baseEnd_2043579 := by
    simpa [prefixWord, tailWord_2043579, baseEnd_2043579] using wordTrace_append hprefix tailTrace_2043579
  have hstable : (prefixWord ++ tailWord_2043579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043579).length < 2 ^ (prefixWord ++ tailWord_2043579).sum := by decide
  have hdescent : baseEnd_2043579 < baseStart_2043579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043609 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_2043609 : Nat := 118140960795 + 2043609 * 2 ^ 59
def prefixEnd_2043609 : Nat := 4983230072969 + 3 ^ 40 * 2043609 * 2
def baseEnd_2043609 : Nat := 1049353686854200104089119

theorem tailTrace_2043609 : CollatzResearch.WordTrace tailWord_2043609 prefixEnd_2043609 1049353686854200104089119 := by
  unfold tailWord_2043609
  simp only [CollatzResearch.WordTrace]
  refine ⟨74536543653361088475357881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49691029102240725650238587 74536543653361088475357881)
  ·
    refine ⟨55902407740020816356518411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74536543653361088475357881 55902407740020816356518411)
    ·
      refine ⟨83853611610031224534777617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55902407740020816356518411 83853611610031224534777617)
      ·
        refine ⟨62890208707523418401083213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83853611610031224534777617 62890208707523418401083213)
        ·
          refine ⟨23583828265321281900406205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62890208707523418401083213 23583828265321281900406205)
          ·
            refine ⟨8843935599495480712652327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23583828265321281900406205 8843935599495480712652327)
            ·
              refine ⟨13265903399243221068978491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8843935599495480712652327 13265903399243221068978491)
              ·
                refine ⟨19898855098864831603467737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13265903399243221068978491 19898855098864831603467737)
                ·
                  refine ⟨14924141324148623702600803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19898855098864831603467737 14924141324148623702600803)
                  ·
                    refine ⟨22386211986222935553901205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14924141324148623702600803 22386211986222935553901205)
                    ·
                      refine ⟨1049353686854200104089119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22386211986222935553901205 1049353686854200104089119)
                      ·
                        rfl

theorem cell23_2043609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_2043609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043609 prefixEnd_2043609 := by exact prefixLift 2043609
  have htrace : WordTrace (prefixWord ++ tailWord_2043609) baseStart_2043609 baseEnd_2043609 := by
    simpa [prefixWord, tailWord_2043609, baseEnd_2043609] using wordTrace_append hprefix tailTrace_2043609
  have hstable : (prefixWord ++ tailWord_2043609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043609).length < 2 ^ (prefixWord ++ tailWord_2043609).sum := by decide
  have hdescent : baseEnd_2043609 < baseStart_2043609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043616 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_2043616 : Nat := 118140960795 + 2043616 * 2 ^ 59
def prefixEnd_2043616 : Nat := 4983230072969 + 3 ^ 40 * 2043616 * 2
def baseEnd_2043616 : Nat := 1049357281218781576701587

theorem tailTrace_2043616 : CollatzResearch.WordTrace tailWord_2043616 prefixEnd_2043616 1049357281218781576701587 := by
  unfold tailWord_2043616
  simp only [CollatzResearch.WordTrace]
  refine ⟨37268399482167864335431351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49691199309557152447241801 37268399482167864335431351)
  ·
    refine ⟨55902599223251796503147027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37268399482167864335431351 55902599223251796503147027)
    ·
      refine ⟨83853898834877694754720541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55902599223251796503147027 83853898834877694754720541)
      ·
        refine ⟨31445212063079135533020203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83853898834877694754720541 31445212063079135533020203)
        ·
          refine ⟨47167818094618703299530305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31445212063079135533020203 47167818094618703299530305)
          ·
            refine ⟨35375863570964027474647729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47167818094618703299530305 35375863570964027474647729)
            ·
              refine ⟨26531897678223020605985797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35375863570964027474647729 26531897678223020605985797)
              ·
                refine ⟨4974730814666816363622337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26531897678223020605985797 4974730814666816363622337)
                ·
                  refine ⟨3731048111000112272716753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4974730814666816363622337 3731048111000112272716753)
                  ·
                    refine ⟨2798286083250084204537565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3731048111000112272716753 2798286083250084204537565)
                    ·
                      refine ⟨1049357281218781576701587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2798286083250084204537565 1049357281218781576701587)
                      ·
                        rfl

theorem cell23_2043616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_2043616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043616 prefixEnd_2043616 := by exact prefixLift 2043616
  have htrace : WordTrace (prefixWord ++ tailWord_2043616) baseStart_2043616 baseEnd_2043616 := by
    simpa [prefixWord, tailWord_2043616, baseEnd_2043616] using wordTrace_append hprefix tailTrace_2043616
  have hstable : (prefixWord ++ tailWord_2043616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043616).length < 2 ^ (prefixWord ++ tailWord_2043616).sum := by decide
  have hdescent : baseEnd_2043616 < baseStart_2043616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043700 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_2043700 : Nat := 118140960795 + 2043700 * 2 ^ 59
def prefixEnd_2043700 : Nat := 4983230072969 + 3 ^ 40 * 2043700 * 2
def baseEnd_2043700 : Nat := 349800137864586416017067

theorem tailTrace_2043700 : CollatzResearch.WordTrace tailWord_2043700 prefixEnd_2043700 349800137864586416017067 := by
  unfold tailWord_2043700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37269931348015705508460277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49693241797354274011280369 37269931348015705508460277)
  ·
    refine ⟨3494056063876472391418151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37269931348015705508460277 3494056063876472391418151)
    ·
      refine ⟨5241084095814708587127227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494056063876472391418151 5241084095814708587127227)
      ·
        refine ⟨7861626143722062880690841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241084095814708587127227 7861626143722062880690841)
        ·
          refine ⟨5896219607791547160518131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7861626143722062880690841 5896219607791547160518131)
          ·
            refine ⟨8844329411687320740777197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896219607791547160518131 8844329411687320740777197)
            ·
              refine ⟨3316623529382745277791449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8844329411687320740777197 3316623529382745277791449)
              ·
                refine ⟨2487467647037058958343587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316623529382745277791449 2487467647037058958343587)
                ·
                  refine ⟨3731201470555588437515381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487467647037058958343587 3731201470555588437515381)
                  ·
                    refine ⟨349800137864586416017067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3731201470555588437515381 349800137864586416017067)
                    ·
                      rfl

theorem cell23_2043700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_2043700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043700 prefixEnd_2043700 := by exact prefixLift 2043700
  have htrace : WordTrace (prefixWord ++ tailWord_2043700) baseStart_2043700 baseEnd_2043700 := by
    simpa [prefixWord, tailWord_2043700, baseEnd_2043700] using wordTrace_append hprefix tailTrace_2043700
  have hstable : (prefixWord ++ tailWord_2043700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043700).length < 2 ^ (prefixWord ++ tailWord_2043700).sum := by decide
  have hdescent : baseEnd_2043700 < baseStart_2043700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043720 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4]
def baseStart_2043720 : Nat := 118140960795 + 2043720 * 2 ^ 59
def prefixEnd_2043720 : Nat := 4983230072969 + 3 ^ 40 * 2043720 * 2
def baseEnd_2043720 : Nat := 1049410683206849169801109

theorem tailTrace_2043720 : CollatzResearch.WordTrace tailWord_2043720 prefixEnd_2043720 1049410683206849169801109 := by
  unfold tailWord_2043720
  simp only [CollatzResearch.WordTrace]
  refine ⟨37270296077979477216324307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49693728103972636288432409 37270296077979477216324307)
  ·
    refine ⟨55905444116969215824486461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37270296077979477216324307 55905444116969215824486461)
    ·
      refine ⟨20964541543863455934182423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55905444116969215824486461 20964541543863455934182423)
      ·
        refine ⟨31446812315795183901273635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20964541543863455934182423 31446812315795183901273635)
        ·
          refine ⟨47170218473692775851910453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31446812315795183901273635 47170218473692775851910453)
          ·
            refine ⟨4422207981908697736116605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47170218473692775851910453 4422207981908697736116605)
            ·
              refine ⟨1658327993215761651043727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4422207981908697736116605 1658327993215761651043727)
              ·
                refine ⟨2487491989823642476565591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658327993215761651043727 2487491989823642476565591)
                ·
                  refine ⟨3731237984735463714848387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487491989823642476565591 3731237984735463714848387)
                  ·
                    refine ⟨5596856977103195572272581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3731237984735463714848387 5596856977103195572272581)
                    ·
                      refine ⟨1049410683206849169801109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5596856977103195572272581 1049410683206849169801109)
                      ·
                        rfl

theorem cell23_2043720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_2043720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043720 prefixEnd_2043720 := by exact prefixLift 2043720
  have htrace : WordTrace (prefixWord ++ tailWord_2043720) baseStart_2043720 baseEnd_2043720 := by
    simpa [prefixWord, tailWord_2043720, baseEnd_2043720] using wordTrace_append hprefix tailTrace_2043720
  have hstable : (prefixWord ++ tailWord_2043720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043720).length < 2 ^ (prefixWord ++ tailWord_2043720).sum := by decide
  have hdescent : baseEnd_2043720 < baseStart_2043720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043730 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_2043730 : Nat := 118140960795 + 2043730 * 2 ^ 59
def prefixEnd_2043730 : Nat := 4983230072969 + 3 ^ 40 * 2043730 * 2
def baseEnd_2043730 : Nat := 349805272671131376892021

theorem tailTrace_2043730 : CollatzResearch.WordTrace tailWord_2043730 prefixEnd_2043730 349805272671131376892021 := by
  unfold tailWord_2043730
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635239221480681535128161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49693971257281817427008429 18635239221480681535128161)
  ·
    refine ⟨13976429416110511151346121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18635239221480681535128161 13976429416110511151346121)
    ·
      refine ⟨10482322062082883363509591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13976429416110511151346121 10482322062082883363509591)
      ·
        refine ⟨15723483093124325045264387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10482322062082883363509591 15723483093124325045264387)
        ·
          refine ⟨23585224639686487567896581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15723483093124325045264387 23585224639686487567896581)
          ·
            refine ⟨4422229619941216418980609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23585224639686487567896581 4422229619941216418980609)
            ·
              refine ⟨3316672214955912314235457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4422229619941216418980609 3316672214955912314235457)
              ·
                refine ⟨2487504161216934235676593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3316672214955912314235457 2487504161216934235676593)
                ·
                  refine ⟨1865628120912700676757445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2487504161216934235676593 1865628120912700676757445)
                  ·
                    refine ⟨349805272671131376892021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1865628120912700676757445 349805272671131376892021)
                    ·
                      rfl

theorem cell23_2043730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_2043730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043730 prefixEnd_2043730 := by exact prefixLift 2043730
  have htrace : WordTrace (prefixWord ++ tailWord_2043730) baseStart_2043730 baseEnd_2043730 := by
    simpa [prefixWord, tailWord_2043730, baseEnd_2043730] using wordTrace_append hprefix tailTrace_2043730
  have hstable : (prefixWord ++ tailWord_2043730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043730).length < 2 ^ (prefixWord ++ tailWord_2043730).sum := by decide
  have hdescent : baseEnd_2043730 < baseStart_2043730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043737 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 1, 2, 2]
def baseStart_2043737 : Nat := 118140960795 + 2043737 * 2 ^ 59
def prefixEnd_2043737 : Nat := 4983230072969 + 3 ^ 40 * 2043737 * 2
def baseEnd_2043737 : Nat := 1049419412377975603288531

theorem tailTrace_2043737 : CollatzResearch.WordTrace tailWord_2043737 prefixEnd_2043737 1049419412377975603288531 := by
  unfold tailWord_2043737
  simp only [CollatzResearch.WordTrace]
  refine ⟨74541212196897366336017465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49694141464598244224011643 74541212196897366336017465)
  ·
    refine ⟨55905909147673024752013099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74541212196897366336017465 55905909147673024752013099)
    ·
      refine ⟨83858863721509537128019649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55905909147673024752013099 83858863721509537128019649)
      ·
        refine ⟨62894147791132152846014737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83858863721509537128019649 62894147791132152846014737)
        ·
          refine ⟨47170610843349114634511053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62894147791132152846014737 47170610843349114634511053)
          ·
            refine ⟨17688979066255917987941645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47170610843349114634511053 17688979066255917987941645)
            ·
              refine ⟨6633367149845969245478117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17688979066255917987941645 6633367149845969245478117)
              ·
                refine ⟨1243756340596119233527147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6633367149845969245478117 1243756340596119233527147)
                ·
                  refine ⟨1865634510894178850290721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243756340596119233527147 1865634510894178850290721)
                  ·
                    refine ⟨1399225883170634137718041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865634510894178850290721 1399225883170634137718041)
                    ·
                      refine ⟨1049419412377975603288531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399225883170634137718041 1049419412377975603288531)
                      ·
                        rfl

theorem cell23_2043737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_2043737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043737 prefixEnd_2043737 := by exact prefixLift 2043737
  have htrace : WordTrace (prefixWord ++ tailWord_2043737) baseStart_2043737 baseEnd_2043737 := by
    simpa [prefixWord, tailWord_2043737, baseEnd_2043737] using wordTrace_append hprefix tailTrace_2043737
  have hstable : (prefixWord ++ tailWord_2043737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043737).length < 2 ^ (prefixWord ++ tailWord_2043737).sum := by decide
  have hdescent : baseEnd_2043737 < baseStart_2043737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043754 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_2043754 : Nat := 118140960795 + 2043754 * 2 ^ 59
def prefixEnd_2043754 : Nat := 4983230072969 + 3 ^ 40 * 2043754 * 2
def baseEnd_2043754 : Nat := 1049428141549102036775953

theorem tailTrace_2043754 : CollatzResearch.WordTrace tailWord_2043754 prefixEnd_2043754 1049428141549102036775953 := by
  unfold tailWord_2043754
  simp only [CollatzResearch.WordTrace]
  refine ⟨18635458059458944559846579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49694554825223852159590877 18635458059458944559846579)
  ·
    refine ⟨27953187089188416839769869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18635458059458944559846579 27953187089188416839769869)
    ·
      refine ⟨10482445158445656314913701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27953187089188416839769869 10482445158445656314913701)
      ·
        refine ⟨1965458467208560559046319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10482445158445656314913701 1965458467208560559046319)
        ·
          refine ⟨2948187700812840838569479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965458467208560559046319 2948187700812840838569479)
          ·
            refine ⟨4422281551219261257854219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948187700812840838569479 4422281551219261257854219)
            ·
              refine ⟨6633422326828891886781329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422281551219261257854219 6633422326828891886781329)
              ·
                refine ⟨4975066745121668915085997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6633422326828891886781329 4975066745121668915085997)
                ·
                  refine ⟨1865650029420625843157249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4975066745121668915085997 1865650029420625843157249)
                  ·
                    refine ⟨1399237522065469382367937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865650029420625843157249 1399237522065469382367937)
                    ·
                      refine ⟨1049428141549102036775953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399237522065469382367937 1049428141549102036775953)
                      ·
                        rfl

theorem cell23_2043754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_2043754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043754 prefixEnd_2043754 := by exact prefixLift 2043754
  have htrace : WordTrace (prefixWord ++ tailWord_2043754) baseStart_2043754 baseEnd_2043754 := by
    simpa [prefixWord, tailWord_2043754, baseEnd_2043754] using wordTrace_append hprefix tailTrace_2043754
  have hstable : (prefixWord ++ tailWord_2043754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043754).length < 2 ^ (prefixWord ++ tailWord_2043754).sum := by decide
  have hdescent : baseEnd_2043754 < baseStart_2043754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043774 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_2043774 : Nat := 118140960795 + 2043774 * 2 ^ 59
def prefixEnd_2043774 : Nat := 4983230072969 + 3 ^ 40 * 2043774 * 2
def baseEnd_2043774 : Nat := 1049438411162191958525861

theorem tailTrace_2043774 : CollatzResearch.WordTrace tailWord_2043774 prefixEnd_2043774 1049438411162191958525861 := by
  unfold tailWord_2043774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317820212220415206889297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49695041131842214436742917 9317820212220415206889297)
  ·
    refine ⟨6988365159165311405166973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9317820212220415206889297 6988365159165311405166973)
    ·
      refine ⟨2620636934686991776937615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6988365159165311405166973 2620636934686991776937615)
      ·
        refine ⟨3930955402030487665406423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2620636934686991776937615 3930955402030487665406423)
        ·
          refine ⟨5896433103045731498109635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930955402030487665406423 5896433103045731498109635)
          ·
            refine ⟨8844649654568597247164453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5896433103045731498109635 8844649654568597247164453)
            ·
              refine ⟨1658371810231611983843335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8844649654568597247164453 1658371810231611983843335)
              ·
                refine ⟨2487557715347417975765003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658371810231611983843335 2487557715347417975765003)
                ·
                  refine ⟨3731336573021126963647505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487557715347417975765003 3731336573021126963647505)
                  ·
                    refine ⟨2798502429765845222735629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3731336573021126963647505 2798502429765845222735629)
                    ·
                      refine ⟨1049438411162191958525861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2798502429765845222735629 1049438411162191958525861)
                      ·
                        rfl

theorem cell23_2043774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_2043774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043774 prefixEnd_2043774 := by exact prefixLift 2043774
  have htrace : WordTrace (prefixWord ++ tailWord_2043774) baseStart_2043774 baseEnd_2043774 := by
    simpa [prefixWord, tailWord_2043774, baseEnd_2043774] using wordTrace_append hprefix tailTrace_2043774
  have hstable : (prefixWord ++ tailWord_2043774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043774).length < 2 ^ (prefixWord ++ tailWord_2043774).sum := by decide
  have hdescent : baseEnd_2043774 < baseStart_2043774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043793 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_2043793 : Nat := 118140960795 + 2043793 * 2 ^ 59
def prefixEnd_2043793 : Nat := 4983230072969 + 3 ^ 40 * 2043793 * 2
def baseEnd_2043793 : Nat := 1049448167294627384188273

theorem tailTrace_2043793 : CollatzResearch.WordTrace tailWord_2043793 prefixEnd_2043793 1049448167294627384188273 := by
  unfold tailWord_2043793
  simp only [CollatzResearch.WordTrace]
  refine ⟨74543254684694487900056033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49695503123129658600037355 74543254684694487900056033)
  ·
    refine ⟨55907441013520865925042025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74543254684694487900056033 55907441013520865925042025)
    ·
      refine ⟨41930580760140649443781519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55907441013520865925042025 41930580760140649443781519)
      ·
        refine ⟨62895871140210974165672279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41930580760140649443781519 62895871140210974165672279)
        ·
          refine ⟨94343806710316461248508419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62895871140210974165672279 94343806710316461248508419)
          ·
            refine ⟨141515710065474691872762629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94343806710316461248508419 141515710065474691872762629)
            ·
              refine ⟨26534195637276504726142993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141515710065474691872762629 26534195637276504726142993)
              ·
                refine ⟨19900646727957378544607245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26534195637276504726142993 19900646727957378544607245)
                ·
                  refine ⟨7462742522984016954227717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19900646727957378544607245 7462742522984016954227717)
                  ·
                    refine ⟨1399264223059503178917697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7462742522984016954227717 1399264223059503178917697)
                    ·
                      refine ⟨1049448167294627384188273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399264223059503178917697 1049448167294627384188273)
                      ·
                        rfl

theorem cell23_2043793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_2043793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043793 prefixEnd_2043793 := by exact prefixLift 2043793
  have htrace : WordTrace (prefixWord ++ tailWord_2043793) baseStart_2043793 baseEnd_2043793 := by
    simpa [prefixWord, tailWord_2043793, baseEnd_2043793] using wordTrace_append hprefix tailTrace_2043793
  have hstable : (prefixWord ++ tailWord_2043793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043793).length < 2 ^ (prefixWord ++ tailWord_2043793).sum := by decide
  have hdescent : baseEnd_2043793 < baseStart_2043793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043804 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_2043804 : Nat := 118140960795 + 2043804 * 2 ^ 59
def prefixEnd_2043804 : Nat := 4983230072969 + 3 ^ 40 * 2043804 * 2
def baseEnd_2043804 : Nat := 1049453815581826841150723

theorem tailTrace_2043804 : CollatzResearch.WordTrace tailWord_2043804 prefixEnd_2043804 1049453815581826841150723 := by
  unfold tailWord_2043804
  simp only [CollatzResearch.WordTrace]
  refine ⟨37271827943827318389353233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49695770591769757852470977 37271827943827318389353233)
  ·
    refine ⟨27953870957870488792014925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37271827943827318389353233 27953870957870488792014925)
    ·
      refine ⟨10482701609201433297005597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27953870957870488792014925 10482701609201433297005597)
      ·
        refine ⟨3931013103450537486377099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10482701609201433297005597 3931013103450537486377099)
        ·
          refine ⟨5896519655175806229565649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931013103450537486377099 5896519655175806229565649)
          ·
            refine ⟨4422389741381854672174237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5896519655175806229565649 4422389741381854672174237)
            ·
              refine ⟨1658396153018195502065339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4422389741381854672174237 1658396153018195502065339)
              ·
                refine ⟨2487594229527293253098009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658396153018195502065339 2487594229527293253098009)
                ·
                  refine ⟨1865695672145469939823507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2487594229527293253098009 1865695672145469939823507)
                  ·
                    refine ⟨2798543508218204909735261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1865695672145469939823507 2798543508218204909735261)
                    ·
                      refine ⟨1049453815581826841150723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2798543508218204909735261 1049453815581826841150723)
                      ·
                        rfl

theorem cell23_2043804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_2043804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043804 prefixEnd_2043804 := by exact prefixLift 2043804
  have htrace : WordTrace (prefixWord ++ tailWord_2043804) baseStart_2043804 baseEnd_2043804 := by
    simpa [prefixWord, tailWord_2043804, baseEnd_2043804] using wordTrace_append hprefix tailTrace_2043804
  have hstable : (prefixWord ++ tailWord_2043804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043804).length < 2 ^ (prefixWord ++ tailWord_2043804).sum := by decide
  have hdescent : baseEnd_2043804 < baseStart_2043804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043822 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2043822 : Nat := 118140960795 + 2043822 * 2 ^ 59
def prefixEnd_2043822 : Nat := 4983230072969 + 3 ^ 40 * 2043822 * 2
def baseEnd_2043822 : Nat := 1049463058233607770725641

theorem tailTrace_2043822 : CollatzResearch.WordTrace tailWord_2043822 prefixEnd_2043822 1049463058233607770725641 := by
  unfold tailWord_2043822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318039050198678231607715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49696208267726283901907813 9318039050198678231607715)
  ·
    refine ⟨13977058575298017347411573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9318039050198678231607715 13977058575298017347411573)
    ·
      refine ⟨1310349241434189126319835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13977058575298017347411573 1310349241434189126319835)
      ·
        refine ⟨1965523862151283689479753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310349241434189126319835 1965523862151283689479753)
        ·
          refine ⟨1474142896613462767109815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1965523862151283689479753 1474142896613462767109815)
          ·
            refine ⟨2211214344920194150664723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474142896613462767109815 2211214344920194150664723)
            ·
              refine ⟨3316821517380291225997085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211214344920194150664723 3316821517380291225997085)
              ·
                refine ⟨1243808069017609209748907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3316821517380291225997085 1243808069017609209748907)
                ·
                  refine ⟨1865712103526413814623361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243808069017609209748907 1865712103526413814623361)
                  ·
                    refine ⟨1399284077644810360967521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865712103526413814623361 1399284077644810360967521)
                    ·
                      refine ⟨1049463058233607770725641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399284077644810360967521 1049463058233607770725641)
                      ·
                        rfl

theorem cell23_2043822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2043822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043822 prefixEnd_2043822 := by exact prefixLift 2043822
  have htrace : WordTrace (prefixWord ++ tailWord_2043822) baseStart_2043822 baseEnd_2043822 := by
    simpa [prefixWord, tailWord_2043822, baseEnd_2043822] using wordTrace_append hprefix tailTrace_2043822
  have hstable : (prefixWord ++ tailWord_2043822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043822).length < 2 ^ (prefixWord ++ tailWord_2043822).sum := by decide
  have hdescent : baseEnd_2043822 < baseStart_2043822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043856 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_2043856 : Nat := 118140960795 + 2043856 * 2 ^ 59
def prefixEnd_2043856 : Nat := 4983230072969 + 3 ^ 40 * 2043856 * 2
def baseEnd_2043856 : Nat := 1049480516575860637700483

theorem tailTrace_2043856 : CollatzResearch.WordTrace tailWord_2043856 prefixEnd_2043856 1049480516575860637700483 := by
  unfold tailWord_2043856
  simp only [CollatzResearch.WordTrace]
  refine ⟨37272776241733124829799711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49697034988977499773066281 37272776241733124829799711)
  ·
    refine ⟨55909164362599687244699567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37272776241733124829799711 55909164362599687244699567)
    ·
      refine ⟨83863746543899530867049351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55909164362599687244699567 83863746543899530867049351)
      ·
        refine ⟨125795619815849296300574027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83863746543899530867049351 125795619815849296300574027)
        ·
          refine ⟨188693429723773944450861041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125795619815849296300574027 188693429723773944450861041)
          ·
            refine ⟨141520072292830458338145781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188693429723773944450861041 141520072292830458338145781)
            ·
              refine ⟨13267506777452855469201167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141520072292830458338145781 13267506777452855469201167)
              ·
                refine ⟨19901260166179283203801751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13267506777452855469201167 19901260166179283203801751)
                ·
                  refine ⟨29851890249268924805702627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19901260166179283203801751 29851890249268924805702627)
                  ·
                    refine ⟨44777835373903387208553941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29851890249268924805702627 44777835373903387208553941)
                    ·
                      refine ⟨1049480516575860637700483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44777835373903387208553941 1049480516575860637700483)
                      ·
                        rfl

theorem cell23_2043856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_2043856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043856 prefixEnd_2043856 := by exact prefixLift 2043856
  have htrace : WordTrace (prefixWord ++ tailWord_2043856) baseStart_2043856 baseEnd_2043856 := by
    simpa [prefixWord, tailWord_2043856, baseEnd_2043856] using wordTrace_append hprefix tailTrace_2043856
  have hstable : (prefixWord ++ tailWord_2043856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043856).length < 2 ^ (prefixWord ++ tailWord_2043856).sum := by decide
  have hdescent : baseEnd_2043856 < baseStart_2043856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043861 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_2043861 : Nat := 118140960795 + 2043861 * 2 ^ 59
def prefixEnd_2043861 : Nat := 4983230072969 + 3 ^ 40 * 2043861 * 2
def baseEnd_2043861 : Nat := 1049483083979133118137961

theorem tailTrace_2043861 : CollatzResearch.WordTrace tailWord_2043861 prefixEnd_2043861 1049483083979133118137961 := by
  unfold tailWord_2043861
  simp only [CollatzResearch.WordTrace]
  refine ⟨74545734848448135513531437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49697156565632090342354291 74545734848448135513531437)
  ·
    refine ⟨27954650568168050817574289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74545734848448135513531437 27954650568168050817574289)
    ·
      refine ⟨20965987926126038113180717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27954650568168050817574289 20965987926126038113180717)
      ·
        refine ⟨7862245472297264292442769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20965987926126038113180717 7862245472297264292442769)
        ·
          refine ⟨5896684104222948219332077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7862245472297264292442769 5896684104222948219332077)
          ·
            refine ⟨2211256539083605582249529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5896684104222948219332077 2211256539083605582249529)
            ·
              refine ⟨1658442404312704186687147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211256539083605582249529 1658442404312704186687147)
              ·
                refine ⟨2487663606469056280030721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658442404312704186687147 2487663606469056280030721)
                ·
                  refine ⟨1865747704851792210023041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2487663606469056280030721 1865747704851792210023041)
                  ·
                    refine ⟨1399310778638844157517281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1865747704851792210023041 1399310778638844157517281)
                    ·
                      refine ⟨1049483083979133118137961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399310778638844157517281 1049483083979133118137961)
                      ·
                        rfl

theorem cell23_2043861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_2043861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043861 prefixEnd_2043861 := by exact prefixLift 2043861
  have htrace : WordTrace (prefixWord ++ tailWord_2043861) baseStart_2043861 baseEnd_2043861 := by
    simpa [prefixWord, tailWord_2043861, baseEnd_2043861] using wordTrace_append hprefix tailTrace_2043861
  have hstable : (prefixWord ++ tailWord_2043861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043861).length < 2 ^ (prefixWord ++ tailWord_2043861).sum := by decide
  have hdescent : baseEnd_2043861 < baseStart_2043861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043900 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_2043900 : Nat := 118140960795 + 2043900 * 2 ^ 59
def prefixEnd_2043900 : Nat := 4983230072969 + 3 ^ 40 * 2043900 * 2
def baseEnd_2043900 : Nat := 1049503109724658465550281

theorem tailTrace_2043900 : CollatzResearch.WordTrace tailWord_2043900 prefixEnd_2043900 1049503109724658465550281 := by
  unfold tailWord_2043900
  simp only [CollatzResearch.WordTrace]
  refine ⟨37273578647653422587100577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49698104863537896782800769 37273578647653422587100577)
  ·
    refine ⟨27955183985740066940325433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37273578647653422587100577 27955183985740066940325433)
    ·
      refine ⟨20966387989305050205244075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27955183985740066940325433 20966387989305050205244075)
      ·
        refine ⟨31449581983957575307866113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20966387989305050205244075 31449581983957575307866113)
        ·
          refine ⟨23587186487968181480899585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31449581983957575307866113 23587186487968181480899585)
          ·
            refine ⟨17690389865976136110674689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23587186487968181480899585 17690389865976136110674689)
            ·
              refine ⟨13267792399482102083006017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17690389865976136110674689 13267792399482102083006017)
              ·
                refine ⟨9950844299611576562254513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13267792399482102083006017 9950844299611576562254513)
                ·
                  refine ⟨7463133224708682421690885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9950844299611576562254513 7463133224708682421690885)
                  ·
                    refine ⟨1399337479632877954067041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463133224708682421690885 1399337479632877954067041)
                    ·
                      refine ⟨1049503109724658465550281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399337479632877954067041 1049503109724658465550281)
                      ·
                        rfl

theorem cell23_2043900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_2043900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043900 prefixEnd_2043900 := by exact prefixLift 2043900
  have htrace : WordTrace (prefixWord ++ tailWord_2043900) baseStart_2043900 baseEnd_2043900 := by
    simpa [prefixWord, tailWord_2043900, baseEnd_2043900] using wordTrace_append hprefix tailTrace_2043900
  have hstable : (prefixWord ++ tailWord_2043900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043900).length < 2 ^ (prefixWord ++ tailWord_2043900).sum := by decide
  have hdescent : baseEnd_2043900 < baseStart_2043900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043923 : List Nat := [1, 1, 1, 2, 1, 4, 4, 3, 6]
def baseStart_2043923 : Nat := 118140960795 + 2043923 * 2 ^ 59
def prefixEnd_2043923 : Nat := 4983230072969 + 3 ^ 40 * 2043923 * 2
def baseEnd_2043923 : Nat := 116612768864412430618075

theorem tailTrace_2043923 : CollatzResearch.WordTrace tailWord_2043923 prefixEnd_2043923 116612768864412430618075 := by
  unfold tailWord_2043923
  simp only [CollatzResearch.WordTrace]
  refine ⟨74547996174223520102288423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49698664116149013401525615 74547996174223520102288423)
  ·
    refine ⟨111821994261335280153432635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74547996174223520102288423 111821994261335280153432635)
    ·
      refine ⟨167732991392002920230148953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111821994261335280153432635 167732991392002920230148953)
      ·
        refine ⟨125799743544002190172611715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167732991392002920230148953 125799743544002190172611715)
        ·
          refine ⟨188699615316003285258917573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125799743544002190172611715 188699615316003285258917573)
          ·
            refine ⟨35381177871750615986047045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188699615316003285258917573 35381177871750615986047045)
            ·
              refine ⟨6633970850953240497383821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35381177871750615986047045 6633970850953240497383821)
              ·
                refine ⟨2487739069107465186518933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6633970850953240497383821 2487739069107465186518933)
                ·
                  refine ⟨116612768864412430618075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2487739069107465186518933 116612768864412430618075)
                  ·
                    rfl

theorem cell23_2043923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 3, 6].length) (baseStart_2043923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043923 prefixEnd_2043923 := by exact prefixLift 2043923
  have htrace : WordTrace (prefixWord ++ tailWord_2043923) baseStart_2043923 baseEnd_2043923 := by
    simpa [prefixWord, tailWord_2043923, baseEnd_2043923] using wordTrace_append hprefix tailTrace_2043923
  have hstable : (prefixWord ++ tailWord_2043923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043923).length < 2 ^ (prefixWord ++ tailWord_2043923).sum := by decide
  have hdescent : baseEnd_2043923 < baseStart_2043923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043927 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 3, 4]
def baseStart_2043927 : Nat := 118140960795 + 2043927 * 2 ^ 59
def prefixEnd_2043927 : Nat := 4983230072969 + 3 ^ 40 * 2043927 * 2
def baseEnd_2043927 : Nat := 349838991234109953304219

theorem tailTrace_2043927 : CollatzResearch.WordTrace tailWord_2043927 prefixEnd_2043927 349838991234109953304219 := by
  unfold tailWord_2043927
  simp only [CollatzResearch.WordTrace]
  refine ⟨74548142066209028785434035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49698761377472685856956023 74548142066209028785434035)
  ·
    refine ⟨111822213099313543178151053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74548142066209028785434035 111822213099313543178151053)
    ·
      refine ⟨41933329912242578691806645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111822213099313543178151053 41933329912242578691806645)
      ·
        refine ⟨3931249679272741752356873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41933329912242578691806645 3931249679272741752356873)
        ·
          refine ⟨2948437259454556314267655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931249679272741752356873 2948437259454556314267655)
          ·
            refine ⟨4422655889181834471401483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2948437259454556314267655 4422655889181834471401483)
            ·
              refine ⟨6633983833772751707102225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4422655889181834471401483 6633983833772751707102225)
              ·
                refine ⟨4975487875329563780326669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6633983833772751707102225 4975487875329563780326669)
                ·
                  refine ⟨1865807953248586417622501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4975487875329563780326669 1865807953248586417622501)
                  ·
                    refine ⟨349838991234109953304219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1865807953248586417622501 349838991234109953304219)
                    ·
                      rfl

theorem cell23_2043927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_2043927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043927 prefixEnd_2043927 := by exact prefixLift 2043927
  have htrace : WordTrace (prefixWord ++ tailWord_2043927) baseStart_2043927 baseEnd_2043927 := by
    simpa [prefixWord, tailWord_2043927, baseEnd_2043927] using wordTrace_append hprefix tailTrace_2043927
  have hstable : (prefixWord ++ tailWord_2043927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043927).length < 2 ^ (prefixWord ++ tailWord_2043927).sum := by decide
  have hdescent : baseEnd_2043927 < baseStart_2043927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043974 : List Nat := [6, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_2043974 : Nat := 118140960795 + 2043974 * 2 ^ 59
def prefixEnd_2043974 : Nat := 4983230072969 + 3 ^ 40 * 2043974 * 2
def baseEnd_2043974 : Nat := 116615678588121241780549

theorem tailTrace_2043974 : CollatzResearch.WordTrace tailWord_2043974 prefixEnd_2043974 116615678588121241780549 := by
  unfold tailWord_2043974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329683009282461119137343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49699904198025837208263317 2329683009282461119137343)
  ·
    refine ⟨3494524513923691678706015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329683009282461119137343 3494524513923691678706015)
    ·
      refine ⟨5241786770885537518059023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494524513923691678706015 5241786770885537518059023)
      ·
        refine ⟨7862680156328306277088535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241786770885537518059023 7862680156328306277088535)
        ·
          refine ⟨11794020234492459415632803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862680156328306277088535 11794020234492459415632803)
          ·
            refine ⟨17691030351738689123449205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11794020234492459415632803 17691030351738689123449205)
            ·
              refine ⟨1658534095475502105323363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17691030351738689123449205 1658534095475502105323363)
              ·
                refine ⟨2487801143213253157985045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658534095475502105323363 2487801143213253157985045)
                ·
                  refine ⟨116615678588121241780549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2487801143213253157985045 116615678588121241780549)
                  ·
                    rfl

theorem cell23_2043974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_2043974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043974 prefixEnd_2043974 := by exact prefixLift 2043974
  have htrace : WordTrace (prefixWord ++ tailWord_2043974) baseStart_2043974 baseEnd_2043974 := by
    simpa [prefixWord, tailWord_2043974, baseEnd_2043974] using wordTrace_append hprefix tailTrace_2043974
  have hstable : (prefixWord ++ tailWord_2043974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043974).length < 2 ^ (prefixWord ++ tailWord_2043974).sum := by decide
  have hdescent : baseEnd_2043974 < baseStart_2043974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2043993 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_2043993 : Nat := 118140960795 + 2043993 * 2 ^ 59
def prefixEnd_2043993 : Nat := 4983230072969 + 3 ^ 40 * 2043993 * 2
def baseEnd_2043993 : Nat := 1049550863425526601687353

theorem tailTrace_2043993 : CollatzResearch.WordTrace tailWord_2043993 prefixEnd_2043993 1049550863425526601687353 := by
  unfold tailWord_2043993
  simp only [CollatzResearch.WordTrace]
  refine ⟨74550549283969922057336633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49700366189313281371557755 74550549283969922057336633)
  ·
    refine ⟨55912911962977441543002475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74550549283969922057336633 55912911962977441543002475)
    ·
      refine ⟨83869367944466162314503713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55912911962977441543002475 83869367944466162314503713)
      ·
        refine ⟨62902025958349621735877785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83869367944466162314503713 62902025958349621735877785)
        ·
          refine ⟨47176519468762216301908339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62902025958349621735877785 47176519468762216301908339)
          ·
            refine ⟨70764779203143324452862509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47176519468762216301908339 70764779203143324452862509)
            ·
              refine ⟨26536792201178746669823441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70764779203143324452862509 26536792201178746669823441)
              ·
                refine ⟨19902594150884060002367581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26536792201178746669823441 19902594150884060002367581)
                ·
                  refine ⟨7463472806581522500887843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19902594150884060002367581 7463472806581522500887843)
                  ·
                    refine ⟨11195209209872283751331765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7463472806581522500887843 11195209209872283751331765)
                    ·
                      refine ⟨1049550863425526601687353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11195209209872283751331765 1049550863425526601687353)
                      ·
                        rfl

theorem cell23_2043993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_2043993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2043993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2043993 prefixEnd_2043993 := by exact prefixLift 2043993
  have htrace : WordTrace (prefixWord ++ tailWord_2043993) baseStart_2043993 baseEnd_2043993 := by
    simpa [prefixWord, tailWord_2043993, baseEnd_2043993] using wordTrace_append hprefix tailTrace_2043993
  have hstable : (prefixWord ++ tailWord_2043993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2043993).length < 2 ^ (prefixWord ++ tailWord_2043993).sum := by decide
  have hdescent : baseEnd_2043993 < baseStart_2043993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2043993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044000 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 4, 4]
def baseStart_2044000 : Nat := 118140960795 + 2044000 * 2 ^ 59
def prefixEnd_2044000 : Nat := 4983230072969 + 3 ^ 40 * 2044000 * 2
def baseEnd_2044000 : Nat := 349851485930036024766607

theorem tailTrace_2044000 : CollatzResearch.WordTrace tailWord_2044000 prefixEnd_2044000 349851485930036024766607 := by
  unfold tailWord_2044000
  simp only [CollatzResearch.WordTrace]
  refine ⟨37275402297472281126420727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49700536396629708168560969 37275402297472281126420727)
  ·
    refine ⟨55913103446208421689631091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37275402297472281126420727 55913103446208421689631091)
    ·
      refine ⟨83869655169312632534446637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55913103446208421689631091 83869655169312632534446637)
      ·
        refine ⟨31451120688492237200417489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83869655169312632534446637 31451120688492237200417489)
        ·
          refine ⟨23588340516369177900313117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31451120688492237200417489 23588340516369177900313117)
          ·
            refine ⟨8845627693638441712617419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23588340516369177900313117 8845627693638441712617419)
            ·
              refine ⟨13268441540457662568926129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845627693638441712617419 13268441540457662568926129)
              ·
                refine ⟨9951331155343246926694597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13268441540457662568926129 9951331155343246926694597)
                ·
                  refine ⟨1865874591626858798755237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9951331155343246926694597 1865874591626858798755237)
                  ·
                    refine ⟨349851485930036024766607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1865874591626858798755237 349851485930036024766607)
                    ·
                      rfl

theorem cell23_2044000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 4, 4].length) (baseStart_2044000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044000 prefixEnd_2044000 := by exact prefixLift 2044000
  have htrace : WordTrace (prefixWord ++ tailWord_2044000) baseStart_2044000 baseEnd_2044000 := by
    simpa [prefixWord, tailWord_2044000, baseEnd_2044000] using wordTrace_append hprefix tailTrace_2044000
  have hstable : (prefixWord ++ tailWord_2044000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044000).length < 2 ^ (prefixWord ++ tailWord_2044000).sum := by decide
  have hdescent : baseEnd_2044000 < baseStart_2044000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044114 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_2044114 : Nat := 118140960795 + 2044114 * 2 ^ 59
def prefixEnd_2044114 : Nat := 4983230072969 + 3 ^ 40 * 2044114 * 2
def baseEnd_2044114 : Nat := 1049612994584720628274297

theorem tailTrace_2044114 : CollatzResearch.WordTrace tailWord_2044114 prefixEnd_2044114 1049612994584720628274297 := by
  unfold tailWord_2044114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18638740629132889930622849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49703308344354373148327597 18638740629132889930622849)
  ·
    refine ⟨13979055471849667447967137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18638740629132889930622849 13979055471849667447967137)
    ·
      refine ⟨10484291603887250585975353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13979055471849667447967137 10484291603887250585975353)
      ·
        refine ⟨7863218702915437939481515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10484291603887250585975353 7863218702915437939481515)
        ·
          refine ⟨11794828054373156909222273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863218702915437939481515 11794828054373156909222273)
          ·
            refine ⟨8846121040779867681916705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11794828054373156909222273 8846121040779867681916705)
            ·
              refine ⟨6634590780584900761437529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8846121040779867681916705 6634590780584900761437529)
              ·
                refine ⟨4975943085438675571078147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6634590780584900761437529 4975943085438675571078147)
                ·
                  refine ⟨7463914628158013356617221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4975943085438675571078147 7463914628158013356617221)
                  ·
                    refine ⟨1399483992779627504365729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7463914628158013356617221 1399483992779627504365729)
                    ·
                      refine ⟨1049612994584720628274297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399483992779627504365729 1049612994584720628274297)
                      ·
                        rfl

theorem cell23_2044114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_2044114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044114 prefixEnd_2044114 := by exact prefixLift 2044114
  have htrace : WordTrace (prefixWord ++ tailWord_2044114) baseStart_2044114 baseEnd_2044114 := by
    simpa [prefixWord, tailWord_2044114, baseEnd_2044114] using wordTrace_append hprefix tailTrace_2044114
  have hstable : (prefixWord ++ tailWord_2044114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044114).length < 2 ^ (prefixWord ++ tailWord_2044114).sum := by decide
  have hdescent : baseEnd_2044114 < baseStart_2044114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044118 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_2044118 : Nat := 118140960795 + 2044118 * 2 ^ 59
def prefixEnd_2044118 : Nat := 4983230072969 + 3 ^ 40 * 2044118 * 2
def baseEnd_2044118 : Nat := 1049615048507338612624279

theorem tailTrace_2044118 : CollatzResearch.WordTrace tailWord_2044118 prefixEnd_2044118 1049615048507338612624279 := by
  unfold tailWord_2044118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659694275532316775352313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49703405605678045603758005 4659694275532316775352313)
  ·
    refine ⟨3494770706649237581514235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4659694275532316775352313 3494770706649237581514235)
    ·
      refine ⟨5242156059973856372271353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494770706649237581514235 5242156059973856372271353)
      ·
        refine ⟨3931617044980392279203515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5242156059973856372271353 3931617044980392279203515)
        ·
          refine ⟨5897425567470588418805273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3931617044980392279203515 5897425567470588418805273)
          ·
            refine ⟨4423069175602941314103955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5897425567470588418805273 4423069175602941314103955)
            ·
              refine ⟨6634603763404411971155933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423069175602941314103955 6634603763404411971155933)
              ·
                refine ⟨2487976411276654489183475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6634603763404411971155933 2487976411276654489183475)
                ·
                  refine ⟨3731964616914981733775213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2487976411276654489183475 3731964616914981733775213)
                  ·
                    refine ⟨1399486731343118150165705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3731964616914981733775213 1399486731343118150165705)
                    ·
                      refine ⟨1049615048507338612624279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399486731343118150165705 1049615048507338612624279)
                      ·
                        rfl

theorem cell23_2044118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_2044118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044118 prefixEnd_2044118 := by exact prefixLift 2044118
  have htrace : WordTrace (prefixWord ++ tailWord_2044118) baseStart_2044118 baseEnd_2044118 := by
    simpa [prefixWord, tailWord_2044118, baseEnd_2044118] using wordTrace_append hprefix tailTrace_2044118
  have hstable : (prefixWord ++ tailWord_2044118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044118).length < 2 ^ (prefixWord ++ tailWord_2044118).sum := by decide
  have hdescent : baseEnd_2044118 < baseStart_2044118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044157 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_2044157 : Nat := 118140960795 + 2044157 * 2 ^ 59
def prefixEnd_2044157 : Nat := 4983230072969 + 3 ^ 40 * 2044157 * 2
def baseEnd_2044157 : Nat := 1049635074252863960036599

theorem tailTrace_2044157 : CollatzResearch.WordTrace tailWord_2044157 prefixEnd_2044157 1049635074252863960036599 := by
  unfold tailWord_2044157
  simp only [CollatzResearch.WordTrace]
  refine ⟨74556530855375778066306725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49704353903583852044204483 74556530855375778066306725)
  ·
    refine ⟨13979349535382958387432511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74556530855375778066306725 13979349535382958387432511)
    ·
      refine ⟨20969024303074437581148767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13979349535382958387432511 20969024303074437581148767)
      ·
        refine ⟨31453536454611656371723151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20969024303074437581148767 31453536454611656371723151)
        ·
          refine ⟨47180304681917484557584727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31453536454611656371723151 47180304681917484557584727)
          ·
            refine ⟨70770457022876226836377091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47180304681917484557584727 70770457022876226836377091)
            ·
              refine ⟨106155685534314340254565637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70770457022876226836377091 106155685534314340254565637)
              ·
                refine ⟨19904191037683938797731057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106155685534314340254565637 19904191037683938797731057)
                ·
                  refine ⟨14928143278262954098298293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19904191037683938797731057 14928143278262954098298293)
                  ·
                    refine ⟨1399513432337151946715465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14928143278262954098298293 1399513432337151946715465)
                    ·
                      refine ⟨1049635074252863960036599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399513432337151946715465 1049635074252863960036599)
                      ·
                        rfl

theorem cell23_2044157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_2044157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044157 prefixEnd_2044157 := by exact prefixLift 2044157
  have htrace : WordTrace (prefixWord ++ tailWord_2044157) baseStart_2044157 baseEnd_2044157 := by
    simpa [prefixWord, tailWord_2044157, baseEnd_2044157] using wordTrace_append hprefix tailTrace_2044157
  have hstable : (prefixWord ++ tailWord_2044157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044157).length < 2 ^ (prefixWord ++ tailWord_2044157).sum := by decide
  have hdescent : baseEnd_2044157 < baseStart_2044157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044187 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 4, 4, 2]
def baseStart_2044187 : Nat := 118140960795 + 2044187 * 2 ^ 59
def prefixEnd_2044187 : Nat := 4983230072969 + 3 ^ 40 * 2044187 * 2
def baseEnd_2044187 : Nat := 1049650478672498842661461

theorem tailTrace_2044187 : CollatzResearch.WordTrace tailWord_2044187 prefixEnd_2044187 1049650478672498842661461 := by
  unfold tailWord_2044187
  simp only [CollatzResearch.WordTrace]
  refine ⟨74557625045267093189898815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49705083363511395459932543 74557625045267093189898815)
  ·
    refine ⟨111836437567900639784848223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74557625045267093189898815 111836437567900639784848223)
    ·
      refine ⟨167754656351850959677272335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111836437567900639784848223 167754656351850959677272335)
      ·
        refine ⟨251631984527776439515908503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167754656351850959677272335 251631984527776439515908503)
        ·
          refine ⟨377447976791664659273862755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251631984527776439515908503 377447976791664659273862755)
          ·
            refine ⟨566171965187496988910794133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377447976791664659273862755 566171965187496988910794133)
            ·
              refine ⟨26539310868163921355193475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 566171965187496988910794133 26539310868163921355193475)
              ·
                refine ⟨39808966302245882032790213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26539310868163921355193475 39808966302245882032790213)
                ·
                  refine ⟨7464181181671102881148165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39808966302245882032790213 7464181181671102881148165)
                  ·
                    refine ⟨1399533971563331790215281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464181181671102881148165 1399533971563331790215281)
                    ·
                      refine ⟨1049650478672498842661461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399533971563331790215281 1049650478672498842661461)
                      ·
                        rfl

theorem cell23_2044187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 4, 2].length) (baseStart_2044187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044187 prefixEnd_2044187 := by exact prefixLift 2044187
  have htrace : WordTrace (prefixWord ++ tailWord_2044187) baseStart_2044187 baseEnd_2044187 := by
    simpa [prefixWord, tailWord_2044187, baseEnd_2044187] using wordTrace_append hprefix tailTrace_2044187
  have hstable : (prefixWord ++ tailWord_2044187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044187).length < 2 ^ (prefixWord ++ tailWord_2044187).sum := by decide
  have hdescent : baseEnd_2044187 < baseStart_2044187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044199 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_2044199 : Nat := 118140960795 + 2044199 * 2 ^ 59
def prefixEnd_2044199 : Nat := 4983230072969 + 3 ^ 40 * 2044199 * 2
def baseEnd_2044199 : Nat := 1049656640440352795711407

theorem tailTrace_2044199 : CollatzResearch.WordTrace tailWord_2044199 prefixEnd_2044199 1049656640440352795711407 := by
  unfold tailWord_2044199
  simp only [CollatzResearch.WordTrace]
  refine ⟨74558062721223619239335651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49705375147482412826223767 74558062721223619239335651)
  ·
    refine ⟨111837094081835428859003477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74558062721223619239335651 111837094081835428859003477)
    ·
      refine ⟨1310590946271508931941447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 111837094081835428859003477 1310590946271508931941447)
      ·
        refine ⟨1965886419407263397912171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310590946271508931941447 1965886419407263397912171)
        ·
          refine ⟨2948829629110895096868257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1965886419407263397912171 2948829629110895096868257)
          ·
            refine ⟨2211622221833171322651193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2948829629110895096868257 2211622221833171322651193)
            ·
              refine ⟨1658716666374878491988395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2211622221833171322651193 1658716666374878491988395)
              ·
                refine ⟨2488074999562317737982593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658716666374878491988395 2488074999562317737982593)
                ·
                  refine ⟨1866056249671738303486945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488074999562317737982593 1866056249671738303486945)
                  ·
                    refine ⟨1399542187253803727615209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866056249671738303486945 1399542187253803727615209)
                    ·
                      refine ⟨1049656640440352795711407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399542187253803727615209 1049656640440352795711407)
                      ·
                        rfl

theorem cell23_2044199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_2044199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044199 prefixEnd_2044199 := by exact prefixLift 2044199
  have htrace : WordTrace (prefixWord ++ tailWord_2044199) baseStart_2044199 baseEnd_2044199 := by
    simpa [prefixWord, tailWord_2044199, baseEnd_2044199] using wordTrace_append hprefix tailTrace_2044199
  have hstable : (prefixWord ++ tailWord_2044199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044199).length < 2 ^ (prefixWord ++ tailWord_2044199).sum := by decide
  have hdescent : baseEnd_2044199 < baseStart_2044199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044244 : List Nat := [2, 4, 1, 1, 2, 3, 2, 2, 6]
def baseStart_2044244 : Nat := 118140960795 + 2044244 * 2 ^ 59
def prefixEnd_2044244 : Nat := 4983230072969 + 3 ^ 40 * 2044244 * 2
def baseEnd_2044244 : Nat := 116631083007756124405411

theorem tailTrace_2044244 : CollatzResearch.WordTrace tailWord_2044244 prefixEnd_2044244 116631083007756124405411 := by
  unfold tailWord_2044244
  simp only [CollatzResearch.WordTrace]
  refine ⟨37279852003030295962361893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49706469337373727949815857 37279852003030295962361893)
  ·
    refine ⟨6989972250568180492942855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37279852003030295962361893 6989972250568180492942855)
    ·
      refine ⟨10484958375852270739414283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6989972250568180492942855 10484958375852270739414283)
      ·
        refine ⟨15727437563778406109121425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10484958375852270739414283 15727437563778406109121425)
        ·
          refine ⟨11795578172833804581841069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15727437563778406109121425 11795578172833804581841069)
          ·
            refine ⟨4423341814812676718190401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11795578172833804581841069 4423341814812676718190401)
            ·
              refine ⟨3317506361109507538642801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423341814812676718190401 3317506361109507538642801)
              ·
                refine ⟨2488129770832130653982101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317506361109507538642801 2488129770832130653982101)
                ·
                  refine ⟨116631083007756124405411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2488129770832130653982101 116631083007756124405411)
                  ·
                    rfl

theorem cell23_2044244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_2044244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044244 prefixEnd_2044244 := by exact prefixLift 2044244
  have htrace : WordTrace (prefixWord ++ tailWord_2044244) baseStart_2044244 baseEnd_2044244 := by
    simpa [prefixWord, tailWord_2044244, baseEnd_2044244] using wordTrace_append hprefix tailTrace_2044244
  have hstable : (prefixWord ++ tailWord_2044244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044244).length < 2 ^ (prefixWord ++ tailWord_2044244).sum := by decide
  have hdescent : baseEnd_2044244 < baseStart_2044244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044287 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 6, 4]
def baseStart_2044287 : Nat := 118140960795 + 2044287 * 2 ^ 59
def prefixEnd_2044287 : Nat := 4983230072969 + 3 ^ 40 * 2044287 * 2
def baseEnd_2044287 : Nat := 349900608912649483803667

theorem tailTrace_2044287 : CollatzResearch.WordTrace tailWord_2044287 prefixEnd_2044287 349900608912649483803667 := by
  unfold tailWord_2044287
  simp only [CollatzResearch.WordTrace]
  refine ⟨74561272344904810268539115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49707514896603206845692743 74561272344904810268539115)
  ·
    refine ⟨111841908517357215402808673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74561272344904810268539115 111841908517357215402808673)
    ·
      refine ⟨83881431388017911552106505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111841908517357215402808673 83881431388017911552106505)
      ·
        refine ⟨62911073541013433664079879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83881431388017911552106505 62911073541013433664079879)
        ·
          refine ⟨94366610311520150496119819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62911073541013433664079879 94366610311520150496119819)
          ·
            refine ⟨141549915467280225744179729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94366610311520150496119819 141549915467280225744179729)
            ·
              refine ⟨106162436600460169308134797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141549915467280225744179729 106162436600460169308134797)
              ·
                refine ⟨39810913725172563490550549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106162436600460169308134797 39810913725172563490550549)
                ·
                  refine ⟨1866136580867463913619557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39810913725172563490550549 1866136580867463913619557)
                  ·
                    refine ⟨349900608912649483803667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1866136580867463913619557 349900608912649483803667)
                    ·
                      rfl

theorem cell23_2044287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 6, 4].length) (baseStart_2044287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044287 prefixEnd_2044287 := by exact prefixLift 2044287
  have htrace : WordTrace (prefixWord ++ tailWord_2044287) baseStart_2044287 baseEnd_2044287 := by
    simpa [prefixWord, tailWord_2044287, baseEnd_2044287] using wordTrace_append hprefix tailTrace_2044287
  have hstable : (prefixWord ++ tailWord_2044287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044287).length < 2 ^ (prefixWord ++ tailWord_2044287).sum := by decide
  have hdescent : baseEnd_2044287 < baseStart_2044287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044311 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_2044311 : Nat := 118140960795 + 2044311 * 2 ^ 59
def prefixEnd_2044311 : Nat := 4983230072969 + 3 ^ 40 * 2044311 * 2
def baseEnd_2044311 : Nat := 1049714150273656357510891

theorem tailTrace_2044311 : CollatzResearch.WordTrace tailWord_2044311 prefixEnd_2044311 1049714150273656357510891 := by
  unfold tailWord_2044311
  simp only [CollatzResearch.WordTrace]
  refine ⟨74562147696817862367412787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49708098464545241578275191 74562147696817862367412787)
  ·
    refine ⟨111843221545226793551119181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74562147696817862367412787 111843221545226793551119181)
    ·
      refine ⟨41941208079460047581669693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111843221545226793551119181 41941208079460047581669693)
      ·
        refine ⟨15727953029797517843126135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41941208079460047581669693 15727953029797517843126135)
        ·
          refine ⟨23591929544696276764689203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15727953029797517843126135 23591929544696276764689203)
          ·
            refine ⟨35387894317044415147033805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23591929544696276764689203 35387894317044415147033805)
            ·
              refine ⟨13270460368891655680137677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35387894317044415147033805 13270460368891655680137677)
              ·
                refine ⟨4976422638334370880051629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13270460368891655680137677 4976422638334370880051629)
                ·
                  refine ⟨1866158489375389080019361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4976422638334370880051629 1866158489375389080019361)
                  ·
                    refine ⟨1399618867031541810014521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866158489375389080019361 1399618867031541810014521)
                    ·
                      refine ⟨1049714150273656357510891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399618867031541810014521 1049714150273656357510891)
                      ·
                        rfl

theorem cell23_2044311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_2044311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044311 prefixEnd_2044311 := by exact prefixLift 2044311
  have htrace : WordTrace (prefixWord ++ tailWord_2044311) baseStart_2044311 baseEnd_2044311 := by
    simpa [prefixWord, tailWord_2044311, baseEnd_2044311] using wordTrace_append hprefix tailTrace_2044311
  have hstable : (prefixWord ++ tailWord_2044311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044311).length < 2 ^ (prefixWord ++ tailWord_2044311).sum := by decide
  have hdescent : baseEnd_2044311 < baseStart_2044311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044314 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_2044314 : Nat := 118140960795 + 2044314 * 2 ^ 59
def prefixEnd_2044314 : Nat := 4983230072969 + 3 ^ 40 * 2044314 * 2
def baseEnd_2044314 : Nat := 1049715690715619845773377

theorem tailTrace_2044314 : CollatzResearch.WordTrace tailWord_2044314 prefixEnd_2044314 1049715690715619845773377 := by
  unfold tailWord_2044314
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640564278951748469942999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49708171410537995919847997 18640564278951748469942999)
  ·
    refine ⟨27960846418427622704914499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18640564278951748469942999 27960846418427622704914499)
    ·
      refine ⟨41941269627641434057371749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27960846418427622704914499 41941269627641434057371749)
      ·
        refine ⟨7863988055182768885757203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41941269627641434057371749 7863988055182768885757203)
        ·
          refine ⟨11795982082774153328635805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7863988055182768885757203 11795982082774153328635805)
          ·
            refine ⟨4423493281040307498238427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11795982082774153328635805 4423493281040307498238427)
            ·
              refine ⟨6635239921560461247357641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423493281040307498238427 6635239921560461247357641)
              ·
                refine ⟨4976429941170345935518231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6635239921560461247357641 4976429941170345935518231)
                ·
                  refine ⟨7464644911755518903277347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976429941170345935518231 7464644911755518903277347)
                  ·
                    refine ⟨11196967367633278354916021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7464644911755518903277347 11196967367633278354916021)
                    ·
                      refine ⟨1049715690715619845773377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11196967367633278354916021 1049715690715619845773377)
                      ·
                        rfl

theorem cell23_2044314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_2044314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044314 prefixEnd_2044314 := by exact prefixLift 2044314
  have htrace : WordTrace (prefixWord ++ tailWord_2044314) baseStart_2044314 baseEnd_2044314 := by
    simpa [prefixWord, tailWord_2044314, baseEnd_2044314] using wordTrace_append hprefix tailTrace_2044314
  have hstable : (prefixWord ++ tailWord_2044314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044314).length < 2 ^ (prefixWord ++ tailWord_2044314).sum := by decide
  have hdescent : baseEnd_2044314 < baseStart_2044314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044324 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_2044324 : Nat := 118140960795 + 2044324 * 2 ^ 59
def prefixEnd_2044324 : Nat := 4983230072969 + 3 ^ 40 * 2044324 * 2
def baseEnd_2044324 : Nat := 1049720825522164806648331

theorem tailTrace_2044324 : CollatzResearch.WordTrace tailWord_2044324 prefixEnd_2044324 1049720825522164806648331 := by
  unfold tailWord_2044324
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281310922885382793818013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49708414563847177058424017 37281310922885382793818013)
  ·
    refine ⟨13980491596082018547681755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37281310922885382793818013 13980491596082018547681755)
    ·
      refine ⟨20970737394123027821522633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13980491596082018547681755 20970737394123027821522633)
      ·
        refine ⟨15728053045592270866141975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20970737394123027821522633 15728053045592270866141975)
        ·
          refine ⟨23592079568388406299212963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15728053045592270866141975 23592079568388406299212963)
          ·
            refine ⟨35388119352582609448819445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23592079568388406299212963 35388119352582609448819445)
            ·
              refine ⟨3317636189304619635826823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35388119352582609448819445 3317636189304619635826823)
              ·
                refine ⟨4976454283956929453740235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3317636189304619635826823 4976454283956929453740235)
                ·
                  refine ⟨7464681425935394180610353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976454283956929453740235 7464681425935394180610353)
                  ·
                    refine ⟨5598511069451545635457765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7464681425935394180610353 5598511069451545635457765)
                    ·
                      refine ⟨1049720825522164806648331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5598511069451545635457765 1049720825522164806648331)
                      ·
                        rfl

theorem cell23_2044324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_2044324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044324 prefixEnd_2044324 := by exact prefixLift 2044324
  have htrace : WordTrace (prefixWord ++ tailWord_2044324) baseStart_2044324 baseEnd_2044324 := by
    simpa [prefixWord, tailWord_2044324, baseEnd_2044324] using wordTrace_append hprefix tailTrace_2044324
  have hstable : (prefixWord ++ tailWord_2044324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044324).length < 2 ^ (prefixWord ++ tailWord_2044324).sum := by decide
  have hdescent : baseEnd_2044324 < baseStart_2044324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044328 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_2044328 : Nat := 118140960795 + 2044328 * 2 ^ 59
def prefixEnd_2044328 : Nat := 4983230072969 + 3 ^ 40 * 2044328 * 2
def baseEnd_2044328 : Nat := 1049722879444782790998313

theorem tailTrace_2044328 : CollatzResearch.WordTrace tailWord_2044328 prefixEnd_2044328 1049722879444782790998313 := by
  unfold tailWord_2044328
  simp only [CollatzResearch.WordTrace]
  refine ⟨37281383868878137135390819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49708511825170849513854425 37281383868878137135390819)
  ·
    refine ⟨55922075803317205703086229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37281383868878137135390819 55922075803317205703086229)
    ·
      refine ⟨2621347303280494017332167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55922075803317205703086229 2621347303280494017332167)
      ·
        refine ⟨3932020954920741025998251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621347303280494017332167 3932020954920741025998251)
        ·
          refine ⟨5898031432381111538997377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932020954920741025998251 5898031432381111538997377)
          ·
            refine ⟨4423523574285833654248033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5898031432381111538997377 4423523574285833654248033)
            ·
              refine ⟨3317642680714375240686025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423523574285833654248033 3317642680714375240686025)
              ·
                refine ⟨2488232010535781430514519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3317642680714375240686025 2488232010535781430514519)
                ·
                  refine ⟨3732348015803672145771779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488232010535781430514519 3732348015803672145771779)
                  ·
                    refine ⟨5598522023705508218657669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3732348015803672145771779 5598522023705508218657669)
                    ·
                      refine ⟨1049722879444782790998313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5598522023705508218657669 1049722879444782790998313)
                      ·
                        rfl

theorem cell23_2044328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_2044328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044328 prefixEnd_2044328 := by exact prefixLift 2044328
  have htrace : WordTrace (prefixWord ++ tailWord_2044328) baseStart_2044328 baseEnd_2044328 := by
    simpa [prefixWord, tailWord_2044328, baseEnd_2044328] using wordTrace_append hprefix tailTrace_2044328
  have hstable : (prefixWord ++ tailWord_2044328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044328).length < 2 ^ (prefixWord ++ tailWord_2044328).sum := by decide
  have hdescent : baseEnd_2044328 < baseStart_2044328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044345 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 1, 2, 2]
def baseStart_2044345 : Nat := 118140960795 + 2044345 * 2 ^ 59
def prefixEnd_2044345 : Nat := 4983230072969 + 3 ^ 40 * 2044345 * 2
def baseEnd_2044345 : Nat := 1049731608615909224485735

theorem tailTrace_2044345 : CollatzResearch.WordTrace tailWord_2044345 prefixEnd_2044345 1049731608615909224485735 := by
  unfold tailWord_2044345
  simp only [CollatzResearch.WordTrace]
  refine ⟨74563387778694686174150489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49708925185796457449433659 74563387778694686174150489)
  ·
    refine ⟨55922540834021014630612867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74563387778694686174150489 55922540834021014630612867)
    ·
      refine ⟨83883811251031521945919301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55922540834021014630612867 83883811251031521945919301)
      ·
        refine ⟨15728214609568410364859869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83883811251031521945919301 15728214609568410364859869)
        ·
          refine ⟨5898080478588153886822451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15728214609568410364859869 5898080478588153886822451)
          ·
            refine ⟨8847120717882230830233677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898080478588153886822451 8847120717882230830233677)
            ·
              refine ⟨3317670269205836561337629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8847120717882230830233677 3317670269205836561337629)
              ·
                refine ⟨1244126350952188710501611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3317670269205836561337629 1244126350952188710501611)
                ·
                  refine ⟨1866189526428283065752417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244126350952188710501611 1866189526428283065752417)
                  ·
                    refine ⟨1399642144821212299314313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866189526428283065752417 1399642144821212299314313)
                    ·
                      refine ⟨1049731608615909224485735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399642144821212299314313 1049731608615909224485735)
                      ·
                        rfl

theorem cell23_2044345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_2044345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044345 prefixEnd_2044345 := by exact prefixLift 2044345
  have htrace : WordTrace (prefixWord ++ tailWord_2044345) baseStart_2044345 baseEnd_2044345 := by
    simpa [prefixWord, tailWord_2044345, baseEnd_2044345] using wordTrace_append hprefix tailTrace_2044345
  have hstable : (prefixWord ++ tailWord_2044345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044345).length < 2 ^ (prefixWord ++ tailWord_2044345).sum := by decide
  have hdescent : baseEnd_2044345 < baseStart_2044345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044367 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4]
def baseStart_2044367 : Nat := 118140960795 + 2044367 * 2 ^ 59
def prefixEnd_2044367 : Nat := 4983230072969 + 3 ^ 40 * 2044367 * 2
def baseEnd_2044367 : Nat := 1049742905190308138410633

theorem tailTrace_2044367 : CollatzResearch.WordTrace tailWord_2044367 prefixEnd_2044367 1049742905190308138410633 := by
  unfold tailWord_2044367
  simp only [CollatzResearch.WordTrace]
  refine ⟨74564190184614983931451355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49709460123076655954300903 74564190184614983931451355)
  ·
    refine ⟨111846285276922475897177033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74564190184614983931451355 111846285276922475897177033)
    ·
      refine ⟨83884713957691856922882775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111846285276922475897177033 83884713957691856922882775)
      ·
        refine ⟨125827070936537785384324163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83884713957691856922882775 125827070936537785384324163)
        ·
          refine ⟨188740606404806678076486245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125827070936537785384324163 188740606404806678076486245)
          ·
            refine ⟨35388863700901252139341171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188740606404806678076486245 35388863700901252139341171)
            ·
              refine ⟨53083295551351878209011757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35388863700901252139341171 53083295551351878209011757)
              ·
                refine ⟨19906235831756954328379409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53083295551351878209011757 19906235831756954328379409)
                ·
                  refine ⟨14929676873817715746284557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19906235831756954328379409 14929676873817715746284557)
                  ·
                    refine ⟨5598628827681643404856709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14929676873817715746284557 5598628827681643404856709)
                    ·
                      refine ⟨1049742905190308138410633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5598628827681643404856709 1049742905190308138410633)
                      ·
                        rfl

theorem cell23_2044367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_2044367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044367 prefixEnd_2044367 := by exact prefixLift 2044367
  have htrace : WordTrace (prefixWord ++ tailWord_2044367) baseStart_2044367 baseEnd_2044367 := by
    simpa [prefixWord, tailWord_2044367, baseEnd_2044367] using wordTrace_append hprefix tailTrace_2044367
  have hstable : (prefixWord ++ tailWord_2044367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044367).length < 2 ^ (prefixWord ++ tailWord_2044367).sum := by decide
  have hdescent : baseEnd_2044367 < baseStart_2044367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044377 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_2044377 : Nat := 118140960795 + 2044377 * 2 ^ 59
def prefixEnd_2044377 : Nat := 4983230072969 + 3 ^ 40 * 2044377 * 2
def baseEnd_2044377 : Nat := 349916013332284366428529

theorem tailTrace_2044377 : CollatzResearch.WordTrace tailWord_2044377 prefixEnd_2044377 349916013332284366428529 := by
  unfold tailWord_2044377
  simp only [CollatzResearch.WordTrace]
  refine ⟨74564554914578755639315385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49709703276385837092876923 74564554914578755639315385)
  ·
    refine ⟨55923416185934066729486539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74564554914578755639315385 55923416185934066729486539)
    ·
      refine ⟨83885124278901100094229809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55923416185934066729486539 83885124278901100094229809)
      ·
        refine ⟨62913843209175825070672357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83885124278901100094229809 62913843209175825070672357)
        ·
          refine ⟨11796345601720467200751067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62913843209175825070672357 11796345601720467200751067)
          ·
            refine ⟨17694518402580700801126601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796345601720467200751067 17694518402580700801126601)
            ·
              refine ⟨13270888801935525600844951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17694518402580700801126601 13270888801935525600844951)
              ·
                refine ⟨19906333202903288401267427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13270888801935525600844951 19906333202903288401267427)
                ·
                  refine ⟨29859499804354932601901141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19906333202903288401267427 29859499804354932601901141)
                  ·
                    refine ⟨349916013332284366428529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29859499804354932601901141 349916013332284366428529)
                    ·
                      rfl

theorem cell23_2044377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_2044377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044377 prefixEnd_2044377 := by exact prefixLift 2044377
  have htrace : WordTrace (prefixWord ++ tailWord_2044377) baseStart_2044377 baseEnd_2044377 := by
    simpa [prefixWord, tailWord_2044377, baseEnd_2044377] using wordTrace_append hprefix tailTrace_2044377
  have hstable : (prefixWord ++ tailWord_2044377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044377).length < 2 ^ (prefixWord ++ tailWord_2044377).sum := by decide
  have hdescent : baseEnd_2044377 < baseStart_2044377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044401 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_2044401 : Nat := 118140960795 + 2044401 * 2 ^ 59
def prefixEnd_2044401 : Nat := 4983230072969 + 3 ^ 40 * 2044401 * 2
def baseEnd_2044401 : Nat := 1049760363532561005385477

theorem tailTrace_2044401 : CollatzResearch.WordTrace tailWord_2044401 prefixEnd_2044401 1049760363532561005385477 := by
  unfold tailWord_2044401
  simp only [CollatzResearch.WordTrace]
  refine ⟨74565430266491807738189057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49710286844327871825459371 74565430266491807738189057)
  ·
    refine ⟨55924072699868855803641793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74565430266491807738189057 55924072699868855803641793)
    ·
      refine ⟨41943054524901641852731345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55924072699868855803641793 41943054524901641852731345)
      ·
        refine ⟨31457290893676231389548509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41943054524901641852731345 31457290893676231389548509)
        ·
          refine ⟨11796484085128586771080691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31457290893676231389548509 11796484085128586771080691)
          ·
            refine ⟨17694726127692880156621037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11796484085128586771080691 17694726127692880156621037)
            ·
              refine ⟨6635522297884830058732889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17694726127692880156621037 6635522297884830058732889)
              ·
                refine ⟨4976641723413622544049667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6635522297884830058732889 4976641723413622544049667)
                ·
                  refine ⟨7464962585120433816074501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4976641723413622544049667 7464962585120433816074501)
                  ·
                    refine ⟨1399680484710081340513969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7464962585120433816074501 1399680484710081340513969)
                    ·
                      refine ⟨1049760363532561005385477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399680484710081340513969 1049760363532561005385477)
                      ·
                        rfl

theorem cell23_2044401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_2044401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044401 prefixEnd_2044401 := by exact prefixLift 2044401
  have htrace : WordTrace (prefixWord ++ tailWord_2044401) baseStart_2044401 baseEnd_2044401 := by
    simpa [prefixWord, tailWord_2044401, baseEnd_2044401] using wordTrace_append hprefix tailTrace_2044401
  have hstable : (prefixWord ++ tailWord_2044401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044401).length < 2 ^ (prefixWord ++ tailWord_2044401).sum := by decide
  have hdescent : baseEnd_2044401 < baseStart_2044401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044422 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_2044422 : Nat := 118140960795 + 2044422 * 2 ^ 59
def prefixEnd_2044422 : Nat := 4983230072969 + 3 ^ 40 * 2044422 * 2
def baseEnd_2044422 : Nat := 1049771146626305423222881

theorem tailTrace_2044422 : CollatzResearch.WordTrace tailWord_2044422 prefixEnd_2044422 1049771146626305423222881 := by
  unfold tailWord_2044422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2330193631231741510146985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49710797466277152216469013 2330193631231741510146985)
  ·
    refine ⟨1747645223423806132610239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2330193631231741510146985 1747645223423806132610239)
    ·
      refine ⟨2621467835135709198915359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1747645223423806132610239 2621467835135709198915359)
      ·
        refine ⟨3932201752703563798373039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2621467835135709198915359 3932201752703563798373039)
        ·
          refine ⟨5898302629055345697559559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3932201752703563798373039 5898302629055345697559559)
          ·
            refine ⟨8847453943583018546339339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898302629055345697559559 8847453943583018546339339)
            ·
              refine ⟨13271180915374527819509009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8847453943583018546339339 13271180915374527819509009)
              ·
                refine ⟨9953385686530895864631757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13271180915374527819509009 9953385686530895864631757)
                ·
                  refine ⟨3732519632449085949236909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9953385686530895864631757 3732519632449085949236909)
                  ·
                    refine ⟨1399694862168407230963841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3732519632449085949236909 1399694862168407230963841)
                    ·
                      refine ⟨1049771146626305423222881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399694862168407230963841 1049771146626305423222881)
                      ·
                        rfl

theorem cell23_2044422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_2044422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044422 prefixEnd_2044422 := by exact prefixLift 2044422
  have htrace : WordTrace (prefixWord ++ tailWord_2044422) baseStart_2044422 baseEnd_2044422 := by
    simpa [prefixWord, tailWord_2044422, baseEnd_2044422] using wordTrace_append hprefix tailTrace_2044422
  have hstable : (prefixWord ++ tailWord_2044422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044422).length < 2 ^ (prefixWord ++ tailWord_2044422).sum := by decide
  have hdescent : baseEnd_2044422 < baseStart_2044422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044458 : List Nat := [3, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_2044458 : Nat := 118140960795 + 2044458 * 2 ^ 59
def prefixEnd_2044458 : Nat := 4983230072969 + 3 ^ 40 * 2044458 * 2
def baseEnd_2044458 : Nat := 116643292436651920263635

theorem tailTrace_2044458 : CollatzResearch.WordTrace tailWord_2044458 prefixEnd_2044458 116643292436651920263635 := by
  unfold tailWord_2044458
  simp only [CollatzResearch.WordTrace]
  refine ⟨18641877306821326618253507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49711672818190204315342685 18641877306821326618253507)
  ·
    refine ⟨27962815960231989927380261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18641877306821326618253507 27962815960231989927380261)
    ·
      refine ⟨5243027992543498111383799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27962815960231989927380261 5243027992543498111383799)
      ·
        refine ⟨7864541988815247167075699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5243027992543498111383799 7864541988815247167075699)
        ·
          refine ⟨11796812983222870750613549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7864541988815247167075699 11796812983222870750613549)
          ·
            refine ⟨4423804868708576531480081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11796812983222870750613549 4423804868708576531480081)
            ·
              refine ⟨3317853651531432398610061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4423804868708576531480081 3317853651531432398610061)
              ·
                refine ⟨1244195119324287149478773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3317853651531432398610061 1244195119324287149478773)
                ·
                  refine ⟨116643292436651920263635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1244195119324287149478773 116643292436651920263635)
                  ·
                    rfl

theorem cell23_2044458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_2044458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044458 prefixEnd_2044458 := by exact prefixLift 2044458
  have htrace : WordTrace (prefixWord ++ tailWord_2044458) baseStart_2044458 baseEnd_2044458 := by
    simpa [prefixWord, tailWord_2044458, baseEnd_2044458] using wordTrace_append hprefix tailTrace_2044458
  have hstable : (prefixWord ++ tailWord_2044458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044458).length < 2 ^ (prefixWord ++ tailWord_2044458).sum := by decide
  have hdescent : baseEnd_2044458 < baseStart_2044458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044491 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 2, 4, 2]
def baseStart_2044491 : Nat := 118140960795 + 2044491 * 2 ^ 59
def prefixEnd_2044491 : Nat := 4983230072969 + 3 ^ 40 * 2044491 * 2
def baseEnd_2044491 : Nat := 1049806576791465653260063

theorem tailTrace_2044491 : CollatzResearch.WordTrace tailWord_2044491 prefixEnd_2044491 1049806576791465653260063 := by
  unfold tailWord_2044491
  simp only [CollatzResearch.WordTrace]
  refine ⟨74568712836165753108965327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49712475224110502072643551 74568712836165753108965327)
  ·
    refine ⟨111853069254248629663447991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74568712836165753108965327 111853069254248629663447991)
    ·
      refine ⟨167779603881372944495171987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111853069254248629663447991 167779603881372944495171987)
      ·
        refine ⟨251669405822059416742757981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167779603881372944495171987 251669405822059416742757981)
        ·
          refine ⟨94376027183272281278534243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251669405822059416742757981 94376027183272281278534243)
          ·
            refine ⟨141564040774908421917801365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94376027183272281278534243 141564040774908421917801365)
            ·
              refine ⟨6635814411323832277396939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141564040774908421917801365 6635814411323832277396939)
              ·
                refine ⟨9953721616985748416095409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6635814411323832277396939 9953721616985748416095409)
                ·
                  refine ⟨7465291212739311312071557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9953721616985748416095409 7465291212739311312071557)
                  ·
                    refine ⟨1399742102388620871013417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7465291212739311312071557 1399742102388620871013417)
                    ·
                      refine ⟨1049806576791465653260063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399742102388620871013417 1049806576791465653260063)
                      ·
                        rfl

theorem cell23_2044491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 4, 2].length) (baseStart_2044491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044491 prefixEnd_2044491 := by exact prefixLift 2044491
  have htrace : WordTrace (prefixWord ++ tailWord_2044491) baseStart_2044491 baseEnd_2044491 := by
    simpa [prefixWord, tailWord_2044491, baseEnd_2044491] using wordTrace_append hprefix tailTrace_2044491
  have hstable : (prefixWord ++ tailWord_2044491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044491).length < 2 ^ (prefixWord ++ tailWord_2044491).sum := by decide
  have hdescent : baseEnd_2044491 < baseStart_2044491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044501 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_2044501 : Nat := 118140960795 + 2044501 * 2 ^ 59
def prefixEnd_2044501 : Nat := 4983230072969 + 3 ^ 40 * 2044501 * 2
def baseEnd_2044501 : Nat := 349937237199336871378339

theorem tailTrace_2044501 : CollatzResearch.WordTrace tailWord_2044501 prefixEnd_2044501 349937237199336871378339 := by
  unfold tailWord_2044501
  simp only [CollatzResearch.WordTrace]
  refine ⟨74569077566129524816829357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49712718377419683211219571 74569077566129524816829357)
  ·
    refine ⟨27963404087298571806311009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74569077566129524816829357 27963404087298571806311009)
    ·
      refine ⟨20972553065473928854733257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27963404087298571806311009 20972553065473928854733257)
      ·
        refine ⟨15729414799105446641049943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20972553065473928854733257 15729414799105446641049943)
        ·
          refine ⟨23594122198658169961574915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15729414799105446641049943 23594122198658169961574915)
          ·
            refine ⟨35391183297987254942362373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23594122198658169961574915 35391183297987254942362373)
            ·
              refine ⟨6635846868372610301692945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35391183297987254942362373 6635846868372610301692945)
              ·
                refine ⟨4976885151279457726269709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6635846868372610301692945 4976885151279457726269709)
                ·
                  refine ⟨1866331931729796647351141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4976885151279457726269709 1866331931729796647351141)
                  ·
                    refine ⟨349937237199336871378339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1866331931729796647351141 349937237199336871378339)
                    ·
                      rfl

theorem cell23_2044501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_2044501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044501 prefixEnd_2044501 := by exact prefixLift 2044501
  have htrace : WordTrace (prefixWord ++ tailWord_2044501) baseStart_2044501 baseEnd_2044501 := by
    simpa [prefixWord, tailWord_2044501, baseEnd_2044501] using wordTrace_append hprefix tailTrace_2044501
  have hstable : (prefixWord ++ tailWord_2044501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044501).length < 2 ^ (prefixWord ++ tailWord_2044501).sum := by decide
  have hdescent : baseEnd_2044501 < baseStart_2044501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044528 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_2044528 : Nat := 118140960795 + 2044528 * 2 ^ 59
def prefixEnd_2044528 : Nat := 4983230072969 + 3 ^ 40 * 2044528 * 2
def baseEnd_2044528 : Nat := 1049825575575682008497393

theorem tailTrace_2044528 : CollatzResearch.WordTrace tailWord_2044528 prefixEnd_2044528 1049825575575682008497393 := by
  unfold tailWord_2044528
  simp only [CollatzResearch.WordTrace]
  refine ⟨37285031168515854214031119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49713374891354472285374825 37285031168515854214031119)
  ·
    refine ⟨55927546752773781321046679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37285031168515854214031119 55927546752773781321046679)
    ·
      refine ⟨83891320129160671981570019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55927546752773781321046679 83891320129160671981570019)
      ·
        refine ⟨125836980193741007972355029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83891320129160671981570019 125836980193741007972355029)
        ·
          refine ⟨2949304223290804874352071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125836980193741007972355029 2949304223290804874352071)
          ·
            refine ⟨4423956334936207311528107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949304223290804874352071 4423956334936207311528107)
            ·
              refine ⟨6635934502404310967292161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4423956334936207311528107 6635934502404310967292161)
              ·
                refine ⟨4976950876803233225469121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6635934502404310967292161 4976950876803233225469121)
                ·
                  refine ⟨3732713157602424919101841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4976950876803233225469121 3732713157602424919101841)
                  ·
                    refine ⟨2799534868201818689326381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732713157602424919101841 2799534868201818689326381)
                    ·
                      refine ⟨1049825575575682008497393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2799534868201818689326381 1049825575575682008497393)
                      ·
                        rfl

theorem cell23_2044528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_2044528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044528 prefixEnd_2044528 := by exact prefixLift 2044528
  have htrace : WordTrace (prefixWord ++ tailWord_2044528) baseStart_2044528 baseEnd_2044528 := by
    simpa [prefixWord, tailWord_2044528, baseEnd_2044528] using wordTrace_append hprefix tailTrace_2044528
  have hstable : (prefixWord ++ tailWord_2044528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044528).length < 2 ^ (prefixWord ++ tailWord_2044528).sum := by decide
  have hdescent : baseEnd_2044528 < baseStart_2044528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044548 : List Nat := [2, 3, 2, 1, 3, 1, 4, 1, 6]
def baseStart_2044548 : Nat := 118140960795 + 2044548 * 2 ^ 59
def prefixEnd_2044548 : Nat := 4983230072969 + 3 ^ 40 * 2044548 * 2
def baseEnd_2044548 : Nat := 116648427243196881138589

theorem tailTrace_2044548 : CollatzResearch.WordTrace tailWord_2044548 prefixEnd_2044548 116648427243196881138589 := by
  unfold tailWord_2044548
  simp only [CollatzResearch.WordTrace]
  refine ⟨37285395898479625921895149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49713861197972834562526865 37285395898479625921895149)
  ·
    refine ⟨13982023461929859720710681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37285395898479625921895149 13982023461929859720710681)
    ·
      refine ⟨10486517596447394790533011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13982023461929859720710681 10486517596447394790533011)
      ·
        refine ⟨15729776394671092185799517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10486517596447394790533011 15729776394671092185799517)
        ·
          refine ⟨5898666148001659569674819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15729776394671092185799517 5898666148001659569674819)
          ·
            refine ⟨8847999222002489354512229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898666148001659569674819 8847999222002489354512229)
            ·
              refine ⟨1658999854125466753971043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8847999222002489354512229 1658999854125466753971043)
              ·
                refine ⟨2488499781188200130956565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1658999854125466753971043 2488499781188200130956565)
                ·
                  refine ⟨116648427243196881138589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2488499781188200130956565 116648427243196881138589)
                  ·
                    rfl

theorem cell23_2044548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_2044548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044548 prefixEnd_2044548 := by exact prefixLift 2044548
  have htrace : WordTrace (prefixWord ++ tailWord_2044548) baseStart_2044548 baseEnd_2044548 := by
    simpa [prefixWord, tailWord_2044548, baseEnd_2044548] using wordTrace_append hprefix tailTrace_2044548
  have hstable : (prefixWord ++ tailWord_2044548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044548).length < 2 ^ (prefixWord ++ tailWord_2044548).sum := by decide
  have hdescent : baseEnd_2044548 < baseStart_2044548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044558 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_2044558 : Nat := 118140960795 + 2044558 * 2 ^ 59
def prefixEnd_2044558 : Nat := 4983230072969 + 3 ^ 40 * 2044558 * 2
def baseEnd_2044558 : Nat := 1049840979995316891122255

theorem tailTrace_2044558 : CollatzResearch.WordTrace tailWord_2044558 prefixEnd_2044558 1049840979995316891122255 := by
  unfold tailWord_2044558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9321394565865377943956791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49714104351282015701102885 9321394565865377943956791)
  ·
    refine ⟨13982091848798066915935187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9321394565865377943956791 13982091848798066915935187)
    ·
      refine ⟨20973137773197100373902781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13982091848798066915935187 20973137773197100373902781)
      ·
        refine ⟨7864926664948912640213543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20973137773197100373902781 7864926664948912640213543)
        ·
          refine ⟨11797389997423368960320315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7864926664948912640213543 11797389997423368960320315)
          ·
            refine ⟨17696084996135053440480473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11797389997423368960320315 17696084996135053440480473)
            ·
              refine ⟨13272063747101290080360355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17696084996135053440480473 13272063747101290080360355)
              ·
                refine ⟨19908095620651935120540533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13272063747101290080360355 19908095620651935120540533)
                ·
                  refine ⟨1866383964436118917550675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19908095620651935120540533 1866383964436118917550675)
                  ·
                    refine ⟨2799575946654178376326013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1866383964436118917550675 2799575946654178376326013)
                    ·
                      refine ⟨1049840979995316891122255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2799575946654178376326013 1049840979995316891122255)
                      ·
                        rfl

theorem cell23_2044558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_2044558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044558 prefixEnd_2044558 := by exact prefixLift 2044558
  have htrace : WordTrace (prefixWord ++ tailWord_2044558) baseStart_2044558 baseEnd_2044558 := by
    simpa [prefixWord, tailWord_2044558, baseEnd_2044558] using wordTrace_append hprefix tailTrace_2044558
  have hstable : (prefixWord ++ tailWord_2044558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044558).length < 2 ^ (prefixWord ++ tailWord_2044558).sum := by decide
  have hdescent : baseEnd_2044558 < baseStart_2044558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044586 : List Nat := [3, 1, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_2044586 : Nat := 118140960795 + 2044586 * 2 ^ 59
def prefixEnd_2044586 : Nat := 4983230072969 + 3 ^ 40 * 2044586 * 2
def baseEnd_2044586 : Nat := 349951785817880927190709

theorem tailTrace_2044586 : CollatzResearch.WordTrace tailWord_2044586 prefixEnd_2044586 349951785817880927190709 := by
  unfold tailWord_2044586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643044442705396083418403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49714785180547722889115741 18643044442705396083418403)
  ·
    refine ⟨27964566664058094125127605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18643044442705396083418403 27964566664058094125127605)
    ·
      refine ⟨2621678124755446324230713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27964566664058094125127605 2621678124755446324230713)
      ·
        refine ⟨1966258593566584743173035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2621678124755446324230713 1966258593566584743173035)
        ·
          refine ⟨2949387890349877114759553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966258593566584743173035 2949387890349877114759553)
          ·
            refine ⟨2212040917762407836069665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949387890349877114759553 2212040917762407836069665)
            ·
              refine ⟨1659030688321805877052249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212040917762407836069665 1659030688321805877052249)
              ·
                refine ⟨1244273016241354407789187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659030688321805877052249 1244273016241354407789187)
                ·
                  refine ⟨1866409524362031611683781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244273016241354407789187 1866409524362031611683781)
                  ·
                    refine ⟨349951785817880927190709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1866409524362031611683781 349951785817880927190709)
                    ·
                      rfl

theorem cell23_2044586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_2044586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044586 prefixEnd_2044586 := by exact prefixLift 2044586
  have htrace : WordTrace (prefixWord ++ tailWord_2044586) baseStart_2044586 baseEnd_2044586 := by
    simpa [prefixWord, tailWord_2044586, baseEnd_2044586] using wordTrace_append hprefix tailTrace_2044586
  have hstable : (prefixWord ++ tailWord_2044586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044586).length < 2 ^ (prefixWord ++ tailWord_2044586).sum := by decide
  have hdescent : baseEnd_2044586 < baseStart_2044586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044608 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 2, 4]
def baseStart_2044608 : Nat := 118140960795 + 2044608 * 2 ^ 59
def prefixEnd_2044608 : Nat := 4983230072969 + 3 ^ 40 * 2044608 * 2
def baseEnd_2044608 : Nat := 349955551342680565165675

theorem tailTrace_2044608 : CollatzResearch.WordTrace tailWord_2044608 prefixEnd_2044608 349955551342680565165675 := by
  unfold tailWord_2044608
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286490088370941045487239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49715320117827921393982985 37286490088370941045487239)
  ·
    refine ⟨55929735132556411568230859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37286490088370941045487239 55929735132556411568230859)
    ·
      refine ⟨83894602698834617352346289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55929735132556411568230859 83894602698834617352346289)
      ·
        refine ⟨62920952024125963014259717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83894602698834617352346289 62920952024125963014259717)
        ·
          refine ⟨11797678504523618065173697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62920952024125963014259717 11797678504523618065173697)
          ·
            refine ⟨8848258878392713548880273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797678504523618065173697 8848258878392713548880273)
            ·
              refine ⟨6636194158794535161660205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8848258878392713548880273 6636194158794535161660205)
              ·
                refine ⟨2488572809547950685622577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6636194158794535161660205 2488572809547950685622577)
                ·
                  refine ⟨1866429607160963014216933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488572809547950685622577 1866429607160963014216933)
                  ·
                    refine ⟨349955551342680565165675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1866429607160963014216933 349955551342680565165675)
                    ·
                      rfl

theorem cell23_2044608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 2, 4].length) (baseStart_2044608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044608 prefixEnd_2044608 := by exact prefixLift 2044608
  have htrace : WordTrace (prefixWord ++ tailWord_2044608) baseStart_2044608 baseEnd_2044608 := by
    simpa [prefixWord, tailWord_2044608, baseEnd_2044608] using wordTrace_append hprefix tailTrace_2044608
  have hstable : (prefixWord ++ tailWord_2044608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044608).length < 2 ^ (prefixWord ++ tailWord_2044608).sum := by decide
  have hdescent : baseEnd_2044608 < baseStart_2044608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044618 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_2044618 : Nat := 118140960795 + 2044618 * 2 ^ 59
def prefixEnd_2044618 : Nat := 4983230072969 + 3 ^ 40 * 2044618 * 2
def baseEnd_2044618 : Nat := 1049871788834586656371979

theorem tailTrace_2044618 : CollatzResearch.WordTrace tailWord_2044618 prefixEnd_2044618 1049871788834586656371979 := by
  unfold tailWord_2044618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18643336226676413449709627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49715563271137102532559005 18643336226676413449709627)
  ·
    refine ⟨27965004340014620174564441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18643336226676413449709627 27965004340014620174564441)
    ·
      refine ⟨20973753255010965130923331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27965004340014620174564441 20973753255010965130923331)
      ·
        refine ⟨31460629882516447696384997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20973753255010965130923331 31460629882516447696384997)
        ·
          refine ⟨5898868102971833943072187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31460629882516447696384997 5898868102971833943072187)
          ·
            refine ⟨8848302154457750914608281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5898868102971833943072187 8848302154457750914608281)
            ·
              refine ⟨6636226615843313185956211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8848302154457750914608281 6636226615843313185956211)
              ·
                refine ⟨9954339923764969778934317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636226615843313185956211 9954339923764969778934317)
                ·
                  refine ⟨3732877471411863667100369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9954339923764969778934317 3732877471411863667100369)
                  ·
                    refine ⟨2799658103558897750325277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3732877471411863667100369 2799658103558897750325277)
                    ·
                      refine ⟨1049871788834586656371979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2799658103558897750325277 1049871788834586656371979)
                      ·
                        rfl

theorem cell23_2044618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_2044618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044618 prefixEnd_2044618 := by exact prefixLift 2044618
  have htrace : WordTrace (prefixWord ++ tailWord_2044618) baseStart_2044618 baseEnd_2044618 := by
    simpa [prefixWord, tailWord_2044618, baseEnd_2044618] using wordTrace_append hprefix tailTrace_2044618
  have hstable : (prefixWord ++ tailWord_2044618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044618).length < 2 ^ (prefixWord ++ tailWord_2044618).sum := by decide
  have hdescent : baseEnd_2044618 < baseStart_2044618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044624 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_2044624 : Nat := 118140960795 + 2044624 * 2 ^ 59
def prefixEnd_2044624 : Nat := 4983230072969 + 3 ^ 40 * 2044624 * 2
def baseEnd_2044624 : Nat := 1049874869718513632896951

theorem tailTrace_2044624 : CollatzResearch.WordTrace tailWord_2044624 prefixEnd_2044624 1049874869718513632896951 := by
  unfold tailWord_2044624
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286781872341958411778463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49715709163122611215704617 37286781872341958411778463)
  ·
    refine ⟨55930172808512937617667695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37286781872341958411778463 55930172808512937617667695)
    ·
      refine ⟨83895259212769406426501543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55930172808512937617667695 83895259212769406426501543)
      ·
        refine ⟨125842888819154109639752315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83895259212769406426501543 125842888819154109639752315)
        ·
          refine ⟨188764333228731164459628473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125842888819154109639752315 188764333228731164459628473)
          ·
            refine ⟨141573249921548373344721355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188764333228731164459628473 141573249921548373344721355)
            ·
              refine ⟨212359874882322560017082033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141573249921548373344721355 212359874882322560017082033)
              ·
                refine ⟨159269906161741920012811525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212359874882322560017082033 159269906161741920012811525)
                ·
                  refine ⟨29863107405326610002402161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159269906161741920012811525 29863107405326610002402161)
                  ·
                    refine ⟨22397330553994957501801621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29863107405326610002402161 22397330553994957501801621)
                    ·
                      refine ⟨1049874869718513632896951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22397330553994957501801621 1049874869718513632896951)
                      ·
                        rfl

theorem cell23_2044624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_2044624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044624 prefixEnd_2044624 := by exact prefixLift 2044624
  have htrace : WordTrace (prefixWord ++ tailWord_2044624) baseStart_2044624 baseEnd_2044624 := by
    simpa [prefixWord, tailWord_2044624, baseEnd_2044624] using wordTrace_append hprefix tailTrace_2044624
  have hstable : (prefixWord ++ tailWord_2044624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044624).length < 2 ^ (prefixWord ++ tailWord_2044624).sum := by decide
  have hdescent : baseEnd_2044624 < baseStart_2044624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044629 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2044629 : Nat := 118140960795 + 2044629 * 2 ^ 59
def prefixEnd_2044629 : Nat := 4983230072969 + 3 ^ 40 * 2044629 * 2
def baseEnd_2044629 : Nat := 349959145707262037778143

theorem tailTrace_2044629 : CollatzResearch.WordTrace tailWord_2044629 prefixEnd_2044629 349959145707262037778143 := by
  unfold tailWord_2044629
  simp only [CollatzResearch.WordTrace]
  refine ⟨74573746109665802677488941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49715830739777201784992627 74573746109665802677488941)
  ·
    refine ⟨27965154791124676004058353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74573746109665802677488941 27965154791124676004058353)
    ·
      refine ⟨20973866093343507003043765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27965154791124676004058353 20973866093343507003043765)
      ·
        refine ⟨1966299946250953781535353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20973866093343507003043765 1966299946250953781535353)
        ·
          refine ⟨1474724959688215336151515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966299946250953781535353 1474724959688215336151515)
          ·
            refine ⟨2212087439532323004227273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474724959688215336151515 2212087439532323004227273)
            ·
              refine ⟨1659065579649242253170455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212087439532323004227273 1659065579649242253170455)
              ·
                refine ⟨2488598369473863379755683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659065579649242253170455 2488598369473863379755683)
                ·
                  refine ⟨3732897554210795069633525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488598369473863379755683 3732897554210795069633525)
                  ·
                    refine ⟨349959145707262037778143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3732897554210795069633525 349959145707262037778143)
                    ·
                      rfl

theorem cell23_2044629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2044629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044629 prefixEnd_2044629 := by exact prefixLift 2044629
  have htrace : WordTrace (prefixWord ++ tailWord_2044629) baseStart_2044629 baseEnd_2044629 := by
    simpa [prefixWord, tailWord_2044629, baseEnd_2044629] using wordTrace_append hprefix tailTrace_2044629
  have hstable : (prefixWord ++ tailWord_2044629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044629).length < 2 ^ (prefixWord ++ tailWord_2044629).sum := by decide
  have hdescent : baseEnd_2044629 < baseStart_2044629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044632 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 1, 2, 2]
def baseStart_2044632 : Nat := 118140960795 + 2044632 * 2 ^ 59
def prefixEnd_2044632 : Nat := 4983230072969 + 3 ^ 40 * 2044632 * 2
def baseEnd_2044632 : Nat := 1049878977563749601596915

theorem tailTrace_2044632 : CollatzResearch.WordTrace tailWord_2044632 prefixEnd_2044632 1049878977563749601596915 := by
  unfold tailWord_2044632
  simp only [CollatzResearch.WordTrace]
  refine ⟨37286927764327467094924075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49715903685769956126565433 37286927764327467094924075)
  ·
    refine ⟨55930391646491200642386113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37286927764327467094924075 55930391646491200642386113)
    ·
      refine ⟨41947793734868400481789585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55930391646491200642386113 41947793734868400481789585)
      ·
        refine ⟨31460845301151300361342189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41947793734868400481789585 31460845301151300361342189)
        ·
          refine ⟨11797816987931737635503321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31460845301151300361342189 11797816987931737635503321)
          ·
            refine ⟨8848362740948803226627491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11797816987931737635503321 8848362740948803226627491)
            ·
              refine ⟨13272544111423204839941237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8848362740948803226627491 13272544111423204839941237)
              ·
                refine ⟨1244301010445925453744491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13272544111423204839941237 1244301010445925453744491)
                ·
                  refine ⟨1866451515668888180616737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244301010445925453744491 1866451515668888180616737)
                  ·
                    refine ⟨1399838636751666135462553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866451515668888180616737 1399838636751666135462553)
                    ·
                      refine ⟨1049878977563749601596915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399838636751666135462553 1049878977563749601596915)
                      ·
                        rfl

theorem cell23_2044632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_2044632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044632 prefixEnd_2044632 := by exact prefixLift 2044632
  have htrace : WordTrace (prefixWord ++ tailWord_2044632) baseStart_2044632 baseEnd_2044632 := by
    simpa [prefixWord, tailWord_2044632, baseEnd_2044632] using wordTrace_append hprefix tailTrace_2044632
  have hstable : (prefixWord ++ tailWord_2044632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044632).length < 2 ^ (prefixWord ++ tailWord_2044632).sum := by decide
  have hdescent : baseEnd_2044632 < baseStart_2044632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044691 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5]
def baseStart_2044691 : Nat := 118140960795 + 2044691 * 2 ^ 59
def prefixEnd_2044691 : Nat := 4983230072969 + 3 ^ 40 * 2044691 * 2
def baseEnd_2044691 : Nat := 1049909272922364870759143

theorem tailTrace_2044691 : CollatzResearch.WordTrace tailWord_2044691 prefixEnd_2044691 1049909272922364870759143 := by
  unfold tailWord_2044691
  simp only [CollatzResearch.WordTrace]
  refine ⟨74576007435441187266245927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49717338290294124844163951 74576007435441187266245927)
  ·
    refine ⟨111864011153161780899368891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74576007435441187266245927 111864011153161780899368891)
    ·
      refine ⟨167796016729742671349053337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111864011153161780899368891 167796016729742671349053337)
      ·
        refine ⟨125847012547307003511790003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167796016729742671349053337 125847012547307003511790003)
        ·
          refine ⟨188770518820960505267685005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125847012547307003511790003 188770518820960505267685005)
          ·
            refine ⟨70788944557860189475381877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188770518820960505267685005 70788944557860189475381877)
            ·
              refine ⟨6636463552299392763317051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70788944557860189475381877 6636463552299392763317051)
              ·
                refine ⟨9954695328449089144975577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636463552299392763317051 9954695328449089144975577)
                ·
                  refine ⟨7466021496336816858731683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9954695328449089144975577 7466021496336816858731683)
                  ·
                    refine ⟨11199032244505225288097525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7466021496336816858731683 11199032244505225288097525)
                    ·
                      refine ⟨1049909272922364870759143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11199032244505225288097525 1049909272922364870759143)
                      ·
                        rfl

theorem cell23_2044691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 5].length) (baseStart_2044691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044691 prefixEnd_2044691 := by exact prefixLift 2044691
  have htrace : WordTrace (prefixWord ++ tailWord_2044691) baseStart_2044691 baseEnd_2044691 := by
    simpa [prefixWord, tailWord_2044691, baseEnd_2044691] using wordTrace_append hprefix tailTrace_2044691
  have hstable : (prefixWord ++ tailWord_2044691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044691).length < 2 ^ (prefixWord ++ tailWord_2044691).sum := by decide
  have hdescent : baseEnd_2044691 < baseStart_2044691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044705 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_2044705 : Nat := 118140960795 + 2044705 * 2 ^ 59
def prefixEnd_2044705 : Nat := 4983230072969 + 3 ^ 40 * 2044705 * 2
def baseEnd_2044705 : Nat := 1049916461651527815984079

theorem tailTrace_2044705 : CollatzResearch.WordTrace tailWord_2044705 prefixEnd_2044705 1049916461651527815984079 := by
  unfold tailWord_2044705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74576518057390467657255569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49717678704926978438170379 74576518057390467657255569)
  ·
    refine ⟨55932388543042850742941677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74576518057390467657255569 55932388543042850742941677)
    ·
      refine ⟨20974645703641069028603129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55932388543042850742941677 20974645703641069028603129)
      ·
        refine ⟨15730984277730801771452347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20974645703641069028603129 15730984277730801771452347)
        ·
          refine ⟨23596476416596202657178521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15730984277730801771452347 23596476416596202657178521)
          ·
            refine ⟨17697357312447151992883891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23596476416596202657178521 17697357312447151992883891)
            ·
              refine ⟨26546035968670727989325837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17697357312447151992883891 26546035968670727989325837)
              ·
                refine ⟨9954763488251522995997189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26546035968670727989325837 9954763488251522995997189)
                ·
                  refine ⟨1866518154047160561749473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9954763488251522995997189 1866518154047160561749473)
                  ·
                    refine ⟨1399888615535370421312105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866518154047160561749473 1399888615535370421312105)
                    ·
                      refine ⟨1049916461651527815984079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399888615535370421312105 1049916461651527815984079)
                      ·
                        rfl

theorem cell23_2044705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_2044705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044705 prefixEnd_2044705 := by exact prefixLift 2044705
  have htrace : WordTrace (prefixWord ++ tailWord_2044705) baseStart_2044705 baseEnd_2044705 := by
    simpa [prefixWord, tailWord_2044705, baseEnd_2044705] using wordTrace_append hprefix tailTrace_2044705
  have hstable : (prefixWord ++ tailWord_2044705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044705).length < 2 ^ (prefixWord ++ tailWord_2044705).sum := by decide
  have hdescent : baseEnd_2044705 < baseStart_2044705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044722 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_2044722 : Nat := 118140960795 + 2044722 * 2 ^ 59
def prefixEnd_2044722 : Nat := 4983230072969 + 3 ^ 40 * 2044722 * 2
def baseEnd_2044722 : Nat := 1049925190822654249471501

theorem tailTrace_2044722 : CollatzResearch.WordTrace tailWord_2044722 prefixEnd_2044722 1049925190822654249471501 := by
  unfold tailWord_2044722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18644284524582219890156105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49718092065552586373749613 18644284524582219890156105)
  ·
    refine ⟨13983213393436664917617079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18644284524582219890156105 13983213393436664917617079)
    ·
      refine ⟨20974820090154997376425619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13983213393436664917617079 20974820090154997376425619)
      ·
        refine ⟨31462230135232496064638429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20974820090154997376425619 31462230135232496064638429)
        ·
          refine ⟨11798336300712186024239411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31462230135232496064638429 11798336300712186024239411)
          ·
            refine ⟨17697504451068279036359117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11798336300712186024239411 17697504451068279036359117)
            ·
              refine ⟨6636564169150604638634669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17697504451068279036359117 6636564169150604638634669)
              ·
                refine ⟨2488711563431476739488001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6636564169150604638634669 2488711563431476739488001)
                ·
                  refine ⟨1866533672573607554616001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2488711563431476739488001 1866533672573607554616001)
                  ·
                    refine ⟨1399900254430205665962001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866533672573607554616001 1399900254430205665962001)
                    ·
                      refine ⟨1049925190822654249471501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399900254430205665962001 1049925190822654249471501)
                      ·
                        rfl

theorem cell23_2044722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_2044722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044722 prefixEnd_2044722 := by exact prefixLift 2044722
  have htrace : WordTrace (prefixWord ++ tailWord_2044722) baseStart_2044722 baseEnd_2044722 := by
    simpa [prefixWord, tailWord_2044722, baseEnd_2044722] using wordTrace_append hprefix tailTrace_2044722
  have hstable : (prefixWord ++ tailWord_2044722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044722).length < 2 ^ (prefixWord ++ tailWord_2044722).sum := by decide
  have hdescent : baseEnd_2044722 < baseStart_2044722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044726 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_2044726 : Nat := 118140960795 + 2044726 * 2 ^ 59
def prefixEnd_2044726 : Nat := 4983230072969 + 3 ^ 40 * 2044726 * 2
def baseEnd_2044726 : Nat := 1049927244745272233821483

theorem tailTrace_2044726 : CollatzResearch.WordTrace tailWord_2044726 prefixEnd_2044726 1049927244745272233821483 := by
  unfold tailWord_2044726
  simp only [CollatzResearch.WordTrace]
  refine ⟨4661080249394649265235627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49718189326876258829180021 4661080249394649265235627)
  ·
    refine ⟨6991620374091973897853441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4661080249394649265235627 6991620374091973897853441)
    ·
      refine ⟨5243715280568980423390081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6991620374091973897853441 5243715280568980423390081)
      ·
        refine ⟨3932786460426735317542561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5243715280568980423390081 3932786460426735317542561)
        ·
          refine ⟨2949589845320051488156921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3932786460426735317542561 2949589845320051488156921)
          ·
            refine ⟨2212192383990038616117691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2949589845320051488156921 2212192383990038616117691)
            ·
              refine ⟨3318288575985057924176537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212192383990038616117691 3318288575985057924176537)
              ·
                refine ⟨2488716431988793443132403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3318288575985057924176537 2488716431988793443132403)
                ·
                  refine ⟨3733074647983190164698605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2488716431988793443132403 3733074647983190164698605)
                  ·
                    refine ⟨1399902992993696311761977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3733074647983190164698605 1399902992993696311761977)
                    ·
                      refine ⟨1049927244745272233821483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399902992993696311761977 1049927244745272233821483)
                      ·
                        rfl

theorem cell23_2044726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_2044726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044726 prefixEnd_2044726 := by exact prefixLift 2044726
  have htrace : WordTrace (prefixWord ++ tailWord_2044726) baseStart_2044726 baseEnd_2044726 := by
    simpa [prefixWord, tailWord_2044726, baseEnd_2044726] using wordTrace_append hprefix tailTrace_2044726
  have hstable : (prefixWord ++ tailWord_2044726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044726).length < 2 ^ (prefixWord ++ tailWord_2044726).sum := by decide
  have hdescent : baseEnd_2044726 < baseStart_2044726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044762 : List Nat := [3, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_2044762 : Nat := 118140960795 + 2044762 * 2 ^ 59
def prefixEnd_2044762 : Nat := 4983230072969 + 3 ^ 40 * 2044762 * 2
def baseEnd_2044762 : Nat := 116660636672092676996813

theorem tailTrace_2044762 : CollatzResearch.WordTrace tailWord_2044762 prefixEnd_2044762 116660636672092676996813 := by
  unfold tailWord_2044762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18644649254545991598020135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49719064678789310928053693 18644649254545991598020135)
  ·
    refine ⟨27966973881818987397030203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18644649254545991598020135 27966973881818987397030203)
    ·
      refine ⟨41950460822728481095545305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27966973881818987397030203 41950460822728481095545305)
      ·
        refine ⟨31462845617046360821658979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41950460822728481095545305 31462845617046360821658979)
        ·
          refine ⟨47194268425569541232488469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31462845617046360821658979 47194268425569541232488469)
          ·
            refine ⟨2212231332448572245272897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47194268425569541232488469 2212231332448572245272897)
            ·
              refine ⟨1659173499336429183954673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212231332448572245272897 1659173499336429183954673)
              ·
                refine ⟨1244380124502321887966005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659173499336429183954673 1244380124502321887966005)
                ·
                  refine ⟨116660636672092676996813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1244380124502321887966005 116660636672092676996813)
                  ·
                    rfl

theorem cell23_2044762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_2044762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044762 prefixEnd_2044762 := by exact prefixLift 2044762
  have htrace : WordTrace (prefixWord ++ tailWord_2044762) baseStart_2044762 baseEnd_2044762 := by
    simpa [prefixWord, tailWord_2044762, baseEnd_2044762] using wordTrace_append hprefix tailTrace_2044762
  have hstable : (prefixWord ++ tailWord_2044762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044762).length < 2 ^ (prefixWord ++ tailWord_2044762).sum := by decide
  have hdescent : baseEnd_2044762 < baseStart_2044762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044791 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_2044791 : Nat := 118140960795 + 2044791 * 2 ^ 59
def prefixEnd_2044791 : Nat := 4983230072969 + 3 ^ 40 * 2044791 * 2
def baseEnd_2044791 : Nat := 1049960620987814479508683

theorem tailTrace_2044791 : CollatzResearch.WordTrace tailWord_2044791 prefixEnd_2044791 1049960620987814479508683 := by
  unfold tailWord_2044791
  simp only [CollatzResearch.WordTrace]
  refine ⟨74579654735078904344886227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49719769823385936229924151 74579654735078904344886227)
  ·
    refine ⟨111869482102618356517329341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74579654735078904344886227 111869482102618356517329341)
    ·
      refine ⟨41951055788481883693998503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111869482102618356517329341 41951055788481883693998503)
      ·
        refine ⟨62926583682722825540997755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41951055788481883693998503 62926583682722825540997755)
        ·
          refine ⟨94389875524084238311496633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62926583682722825540997755 94389875524084238311496633)
          ·
            refine ⟨70792406643063178733622475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94389875524084238311496633 70792406643063178733622475)
            ·
              refine ⟨106188609964594768100433713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70792406643063178733622475 106188609964594768100433713)
              ·
                refine ⟨79641457473446076075325285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106188609964594768100433713 79641457473446076075325285)
                ·
                  refine ⟨14932773276271139264123491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79641457473446076075325285 14932773276271139264123491)
                  ·
                    refine ⟨22399159914406708896185237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14932773276271139264123491 22399159914406708896185237)
                    ·
                      refine ⟨1049960620987814479508683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22399159914406708896185237 1049960620987814479508683)
                      ·
                        rfl

theorem cell23_2044791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_2044791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044791 prefixEnd_2044791 := by exact prefixLift 2044791
  have htrace : WordTrace (prefixWord ++ tailWord_2044791) baseStart_2044791 baseEnd_2044791 := by
    simpa [prefixWord, tailWord_2044791, baseEnd_2044791] using wordTrace_append hprefix tailTrace_2044791
  have hstable : (prefixWord ++ tailWord_2044791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044791).length < 2 ^ (prefixWord ++ tailWord_2044791).sum := by decide
  have hdescent : baseEnd_2044791 < baseStart_2044791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044808 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_2044808 : Nat := 118140960795 + 2044808 * 2 ^ 59
def prefixEnd_2044808 : Nat := 4983230072969 + 3 ^ 40 * 2044808 * 2
def baseEnd_2044808 : Nat := 1049969350158940912996105

theorem tailTrace_2044808 : CollatzResearch.WordTrace tailWord_2044808 prefixEnd_2044808 1049969350158940912996105 := by
  unfold tailWord_2044808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37290137388008658124127539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49720183184011544165503385 37290137388008658124127539)
  ·
    refine ⟨55935206082012987186191309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37290137388008658124127539 55935206082012987186191309)
    ·
      refine ⟨20975702280754870194821741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55935206082012987186191309 20975702280754870194821741)
      ·
        refine ⟨7865888355283076323058153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20975702280754870194821741 7865888355283076323058153)
        ·
          refine ⟨5899416266462307242293615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7865888355283076323058153 5899416266462307242293615)
          ·
            refine ⟨8849124399693460863440423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899416266462307242293615 8849124399693460863440423)
            ·
              refine ⟨13273686599540191295160635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849124399693460863440423 13273686599540191295160635)
              ·
                refine ⟨19910529899310286942740953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13273686599540191295160635 19910529899310286942740953)
                ·
                  refine ⟨14932897424482715207055715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19910529899310286942740953 14932897424482715207055715)
                  ·
                    refine ⟨22399346136724072810583573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14932897424482715207055715 22399346136724072810583573)
                    ·
                      refine ⟨1049969350158940912996105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22399346136724072810583573 1049969350158940912996105)
                      ·
                        rfl

theorem cell23_2044808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_2044808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044808 prefixEnd_2044808 := by exact prefixLift 2044808
  have htrace : WordTrace (prefixWord ++ tailWord_2044808) baseStart_2044808 baseEnd_2044808 := by
    simpa [prefixWord, tailWord_2044808, baseEnd_2044808] using wordTrace_append hprefix tailTrace_2044808
  have hstable : (prefixWord ++ tailWord_2044808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044808).length < 2 ^ (prefixWord ++ tailWord_2044808).sum := by decide
  have hdescent : baseEnd_2044808 < baseStart_2044808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044855 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_2044855 : Nat := 118140960795 + 2044855 * 2 ^ 59
def prefixEnd_2044855 : Nat := 4983230072969 + 3 ^ 40 * 2044855 * 2
def baseEnd_2044855 : Nat := 1049993483749702229108389

theorem tailTrace_2044855 : CollatzResearch.WordTrace tailWord_2044855 prefixEnd_2044855 1049993483749702229108389 := by
  unfold tailWord_2044855
  simp only [CollatzResearch.WordTrace]
  refine ⟨74581989006847043275216019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49721326004564695516810679 74581989006847043275216019)
  ·
    refine ⟨111872983510270564912824029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74581989006847043275216019 111872983510270564912824029)
    ·
      refine ⟨41952368816351461842309011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111872983510270564912824029 41952368816351461842309011)
      ·
        refine ⟨62928553224527192763463517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41952368816351461842309011 62928553224527192763463517)
        ·
          refine ⟨23598207459197697286298819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62928553224527192763463517 23598207459197697286298819)
          ·
            refine ⟨35397311188796545929448229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23598207459197697286298819 35397311188796545929448229)
            ·
              refine ⟨6636995847899352361771543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35397311188796545929448229 6636995847899352361771543)
              ·
                refine ⟨9955493771849028542657315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6636995847899352361771543 9955493771849028542657315)
                ·
                  refine ⟨14933240657773542813985973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9955493771849028542657315 14933240657773542813985973)
                  ·
                    refine ⟨1399991311666269638811185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14933240657773542813985973 1399991311666269638811185)
                    ·
                      refine ⟨1049993483749702229108389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1399991311666269638811185 1049993483749702229108389)
                      ·
                        rfl

theorem cell23_2044855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_2044855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044855 prefixEnd_2044855 := by exact prefixLift 2044855
  have htrace : WordTrace (prefixWord ++ tailWord_2044855) baseStart_2044855 baseEnd_2044855 := by
    simpa [prefixWord, tailWord_2044855, baseEnd_2044855] using wordTrace_append hprefix tailTrace_2044855
  have hstable : (prefixWord ++ tailWord_2044855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044855).length < 2 ^ (prefixWord ++ tailWord_2044855).sum := by decide
  have hdescent : baseEnd_2044855 < baseStart_2044855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044935 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_2044935 : Nat := 118140960795 + 2044935 * 2 ^ 59
def prefixEnd_2044935 : Nat := 4983230072969 + 3 ^ 40 * 2044935 * 2
def baseEnd_2044935 : Nat := 1050034562202061916108021

theorem tailTrace_2044935 : CollatzResearch.WordTrace tailWord_2044935 prefixEnd_2044935 1050034562202061916108021 := by
  unfold tailWord_2044935
  simp only [CollatzResearch.WordTrace]
  refine ⟨74584906846557216938128259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49723271231038144625418839 74584906846557216938128259)
  ·
    refine ⟨111877360269835825407192389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74584906846557216938128259 111877360269835825407192389)
    ·
      refine ⟨20977005050594217263848573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111877360269835825407192389 20977005050594217263848573)
      ·
        refine ⟨7866376893972831473943215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20977005050594217263848573 7866376893972831473943215)
        ·
          refine ⟨11799565340959247210914823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7866376893972831473943215 11799565340959247210914823)
          ·
            refine ⟨17699348011438870816372235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11799565340959247210914823 17699348011438870816372235)
            ·
              refine ⟨26549022017158306224558353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17699348011438870816372235 26549022017158306224558353)
              ·
                refine ⟨19911766512868729668418765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26549022017158306224558353 19911766512868729668418765)
                ·
                  refine ⟨7466912442325773625657037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19911766512868729668418765 7466912442325773625657037)
                  ·
                    refine ⟨2800092165872165109621389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7466912442325773625657037 2800092165872165109621389)
                    ·
                      refine ⟨1050034562202061916108021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2800092165872165109621389 1050034562202061916108021)
                      ·
                        rfl

theorem cell23_2044935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_2044935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044935 prefixEnd_2044935 := by exact prefixLift 2044935
  have htrace : WordTrace (prefixWord ++ tailWord_2044935) baseStart_2044935 baseEnd_2044935 := by
    simpa [prefixWord, tailWord_2044935, baseEnd_2044935] using wordTrace_append hprefix tailTrace_2044935
  have hstable : (prefixWord ++ tailWord_2044935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044935).length < 2 ^ (prefixWord ++ tailWord_2044935).sum := by decide
  have hdescent : baseEnd_2044935 < baseStart_2044935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044936 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 1, 2, 2]
def baseStart_2044936 : Nat := 118140960795 + 2044936 * 2 ^ 59
def prefixEnd_2044936 : Nat := 4983230072969 + 3 ^ 40 * 2044936 * 2
def baseEnd_2044936 : Nat := 1050035075682716412195517

theorem tailTrace_2044936 : CollatzResearch.WordTrace tailWord_2044936 prefixEnd_2044936 1050035075682716412195517 := by
  unfold tailWord_2044936
  simp only [CollatzResearch.WordTrace]
  refine ⟨37292471659776797054457331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49723295546369062739276441 37292471659776797054457331)
  ·
    refine ⟨55938707489665195581685997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37292471659776797054457331 55938707489665195581685997)
    ·
      refine ⟨20977015308624448343132249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55938707489665195581685997 20977015308624448343132249)
      ·
        refine ⟨15732761481468336257349187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20977015308624448343132249 15732761481468336257349187)
        ·
          refine ⟨23599142222202504386023781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15732761481468336257349187 23599142222202504386023781)
          ·
            refine ⟨4424839166662969572379459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23599142222202504386023781 4424839166662969572379459)
            ·
              refine ⟨6637258749994454358569189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4424839166662969572379459 6637258749994454358569189)
              ·
                refine ⟨1244486015623960192231723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6637258749994454358569189 1244486015623960192231723)
                ·
                  refine ⟨1866729023435940288347585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244486015623960192231723 1866729023435940288347585)
                  ·
                    refine ⟨1400046767576955216260689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866729023435940288347585 1400046767576955216260689)
                    ·
                      refine ⟨1050035075682716412195517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400046767576955216260689 1050035075682716412195517)
                      ·
                        rfl

theorem cell23_2044936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_2044936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044936 prefixEnd_2044936 := by exact prefixLift 2044936
  have htrace : WordTrace (prefixWord ++ tailWord_2044936) baseStart_2044936 baseEnd_2044936 := by
    simpa [prefixWord, tailWord_2044936, baseEnd_2044936] using wordTrace_append hprefix tailTrace_2044936
  have hstable : (prefixWord ++ tailWord_2044936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044936).length < 2 ^ (prefixWord ++ tailWord_2044936).sum := by decide
  have hdescent : baseEnd_2044936 < baseStart_2044936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044946 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2044946 : Nat := 118140960795 + 2044946 * 2 ^ 59
def prefixEnd_2044946 : Nat := 4983230072969 + 3 ^ 40 * 2044946 * 2
def baseEnd_2044946 : Nat := 350013403496420457690157

theorem tailTrace_2044946 : CollatzResearch.WordTrace tailWord_2044946 prefixEnd_2044946 350013403496420457690157 := by
  unfold tailWord_2044946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18646327012379341454194673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49723538699678243877852461 18646327012379341454194673)
  ·
    refine ⟨13984745259284506090646005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18646327012379341454194673 13984745259284506090646005)
    ·
      refine ⟨1311069868057922445998063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13984745259284506090646005 1311069868057922445998063)
      ·
        refine ⟨1966604802086883668997095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311069868057922445998063 1966604802086883668997095)
        ·
          refine ⟨2949907203130325503495643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966604802086883668997095 2949907203130325503495643)
          ·
            refine ⟨4424860804695488255243465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2949907203130325503495643 4424860804695488255243465)
            ·
              refine ⟨3318645603521616191432599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424860804695488255243465 3318645603521616191432599)
              ·
                refine ⟨4977968405282424287148899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318645603521616191432599 4977968405282424287148899)
                ·
                  refine ⟨7466952607923636430723349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977968405282424287148899 7466952607923636430723349)
                  ·
                    refine ⟨350013403496420457690157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7466952607923636430723349 350013403496420457690157)
                    ·
                      rfl

theorem cell23_2044946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2044946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044946 prefixEnd_2044946 := by exact prefixLift 2044946
  have htrace : WordTrace (prefixWord ++ tailWord_2044946) baseStart_2044946 baseEnd_2044946 := by
    simpa [prefixWord, tailWord_2044946, baseEnd_2044946] using wordTrace_append hprefix tailTrace_2044946
  have hstable : (prefixWord ++ tailWord_2044946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044946).length < 2 ^ (prefixWord ++ tailWord_2044946).sum := by decide
  have hdescent : baseEnd_2044946 < baseStart_2044946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044952 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_2044952 : Nat := 118140960795 + 2044952 * 2 ^ 59
def prefixEnd_2044952 : Nat := 4983230072969 + 3 ^ 40 * 2044952 * 2
def baseEnd_2044952 : Nat := 1050043291373188349595443

theorem tailTrace_2044952 : CollatzResearch.WordTrace tailWord_2044952 prefixEnd_2044952 1050043291373188349595443 := by
  unfold tailWord_2044952
  simp only [CollatzResearch.WordTrace]
  refine ⟨37292763443747814420748555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49723684591663752560998073 37292763443747814420748555)
  ·
    refine ⟨55939145165621721631122833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37292763443747814420748555 55939145165621721631122833)
    ·
      refine ⟨41954358874216291223342125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55939145165621721631122833 41954358874216291223342125)
      ·
        refine ⟨15732884577831109208753297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41954358874216291223342125 15732884577831109208753297)
        ·
          refine ⟨11799663433373331906564973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15732884577831109208753297 11799663433373331906564973)
          ·
            refine ⟨4424873787514999464961865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11799663433373331906564973 4424873787514999464961865)
            ·
              refine ⟨3318655340636249598721399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4424873787514999464961865 3318655340636249598721399)
              ·
                refine ⟨4977983010954374398082099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318655340636249598721399 4977983010954374398082099)
                ·
                  refine ⟨7466974516431561597123149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4977983010954374398082099 7466974516431561597123149)
                  ·
                    refine ⟨2800115443661835598921181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7466974516431561597123149 2800115443661835598921181)
                    ·
                      refine ⟨1050043291373188349595443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2800115443661835598921181 1050043291373188349595443)
                      ·
                        rfl

theorem cell23_2044952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_2044952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044952 prefixEnd_2044952 := by exact prefixLift 2044952
  have htrace : WordTrace (prefixWord ++ tailWord_2044952) baseStart_2044952 baseEnd_2044952 := by
    simpa [prefixWord, tailWord_2044952, baseEnd_2044952] using wordTrace_append hprefix tailTrace_2044952
  have hstable : (prefixWord ++ tailWord_2044952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044952).length < 2 ^ (prefixWord ++ tailWord_2044952).sum := by decide
  have hdescent : baseEnd_2044952 < baseStart_2044952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044975 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 2, 8, 2]
def baseStart_2044975 : Nat := 118140960795 + 2044975 * 2 ^ 59
def prefixEnd_2044975 : Nat := 4983230072969 + 3 ^ 40 * 2044975 * 2
def baseEnd_2044975 : Nat := 1050055101428241759607837

theorem tailTrace_2044975 : CollatzResearch.WordTrace tailWord_2044975 prefixEnd_2044975 1050055101428241759607837 := by
  unfold tailWord_2044975
  simp only [CollatzResearch.WordTrace]
  refine ⟨74586365766412303769584379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49724243844274869179722919 74586365766412303769584379)
  ·
    refine ⟨111879548649618455654376569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74586365766412303769584379 111879548649618455654376569)
    ·
      refine ⟨83909661487213841740782427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111879548649618455654376569 83909661487213841740782427)
      ·
        refine ⟨125864492230820762611173641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83909661487213841740782427 125864492230820762611173641)
        ·
          refine ⟨94398369173115571958380231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125864492230820762611173641 94398369173115571958380231)
          ·
            refine ⟨141597553759673357937570347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94398369173115571958380231 141597553759673357937570347)
            ·
              refine ⟨212396330639510036906355521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141597553759673357937570347 212396330639510036906355521)
              ·
                refine ⟨159297247979632527679766641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212396330639510036906355521 159297247979632527679766641)
                ·
                  refine ⟨119472935984724395759824981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159297247979632527679766641 119472935984724395759824981)
                  ·
                    refine ⟨1400073468570989012810449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 119472935984724395759824981 1400073468570989012810449)
                    ·
                      refine ⟨1050055101428241759607837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400073468570989012810449 1050055101428241759607837)
                      ·
                        rfl

theorem cell23_2044975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 8, 2].length) (baseStart_2044975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044975 prefixEnd_2044975 := by exact prefixLift 2044975
  have htrace : WordTrace (prefixWord ++ tailWord_2044975) baseStart_2044975 baseEnd_2044975 := by
    simpa [prefixWord, tailWord_2044975, baseEnd_2044975] using wordTrace_append hprefix tailTrace_2044975
  have hstable : (prefixWord ++ tailWord_2044975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044975).length < 2 ^ (prefixWord ++ tailWord_2044975).sum := by decide
  have hdescent : baseEnd_2044975 < baseStart_2044975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2044985 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_2044985 : Nat := 118140960795 + 2044985 * 2 ^ 59
def prefixEnd_2044985 : Nat := 4983230072969 + 3 ^ 40 * 2044985 * 2
def baseEnd_2044985 : Nat := 350020078744928906827597

theorem tailTrace_2044985 : CollatzResearch.WordTrace tailWord_2044985 prefixEnd_2044985 350020078744928906827597 := by
  unfold tailWord_2044985
  simp only [CollatzResearch.WordTrace]
  refine ⟨74586730496376075477448409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49724486997584050318298939 74586730496376075477448409)
  ·
    refine ⟨55940047872282056608086307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74586730496376075477448409 55940047872282056608086307)
    ·
      refine ⟨83910071808423084912129461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55940047872282056608086307 83910071808423084912129461)
      ·
        refine ⟨7866569232039664210512137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83910071808423084912129461 7866569232039664210512137)
        ·
          refine ⟨5899926924029748157884103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7866569232039664210512137 5899926924029748157884103)
          ·
            refine ⟨8849890386044622236826155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5899926924029748157884103 8849890386044622236826155)
            ·
              refine ⟨13274835579066933355239233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8849890386044622236826155 13274835579066933355239233)
              ·
                refine ⟨9956126684300200016429425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13274835579066933355239233 9956126684300200016429425)
                ·
                  refine ⟨7467095013225150012322069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9956126684300200016429425 7467095013225150012322069)
                  ·
                    refine ⟨350020078744928906827597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7467095013225150012322069 350020078744928906827597)
                    ·
                      rfl

theorem cell23_2044985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_2044985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2044985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2044985 prefixEnd_2044985 := by exact prefixLift 2044985
  have htrace : WordTrace (prefixWord ++ tailWord_2044985) baseStart_2044985 baseEnd_2044985 := by
    simpa [prefixWord, tailWord_2044985, baseEnd_2044985] using wordTrace_append hprefix tailTrace_2044985
  have hstable : (prefixWord ++ tailWord_2044985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2044985).length < 2 ^ (prefixWord ++ tailWord_2044985).sum := by decide
  have hdescent : baseEnd_2044985 < baseStart_2044985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2044985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045008 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_2045008 : Nat := 118140960795 + 2045008 * 2 ^ 59
def prefixEnd_2045008 : Nat := 4983230072969 + 3 ^ 40 * 2045008 * 2
def baseEnd_2045008 : Nat := 1050072046289840130495185

theorem tailTrace_2045008 : CollatzResearch.WordTrace tailWord_2045008 prefixEnd_2045008 1050072046289840130495185 := by
  unfold tailWord_2045008
  simp only [CollatzResearch.WordTrace]
  refine ⟨37293784687646375202767839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49725046250195166937023785 37293784687646375202767839)
  ·
    refine ⟨55940677031469562804151759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37293784687646375202767839 55940677031469562804151759)
    ·
      refine ⟨83911015547204344206227639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55940677031469562804151759 83911015547204344206227639)
      ·
        refine ⟨125866523320806516309341459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83911015547204344206227639 125866523320806516309341459)
        ·
          refine ⟨188799784981209774464012189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125866523320806516309341459 188799784981209774464012189)
          ·
            refine ⟨70799919367953665424004571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188799784981209774464012189 70799919367953665424004571)
            ·
              refine ⟨106199879051930498136006857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70799919367953665424004571 106199879051930498136006857)
              ·
                refine ⟨79649909288947873602005143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106199879051930498136006857 79649909288947873602005143)
                ·
                  refine ⟨119474863933421810403007715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79649909288947873602005143 119474863933421810403007715)
                  ·
                    refine ⟨179212295900132715604511573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119474863933421810403007715 179212295900132715604511573)
                    ·
                      refine ⟨1050072046289840130495185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 179212295900132715604511573 1050072046289840130495185)
                      ·
                        rfl

theorem cell23_2045008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_2045008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045008 prefixEnd_2045008 := by exact prefixLift 2045008
  have htrace : WordTrace (prefixWord ++ tailWord_2045008) baseStart_2045008 baseEnd_2045008 := by
    simpa [prefixWord, tailWord_2045008, baseEnd_2045008] using wordTrace_append hprefix tailTrace_2045008
  have hstable : (prefixWord ++ tailWord_2045008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045008).length < 2 ^ (prefixWord ++ tailWord_2045008).sum := by decide
  have hdescent : baseEnd_2045008 < baseStart_2045008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045009 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_2045009 : Nat := 118140960795 + 2045009 * 2 ^ 59
def prefixEnd_2045009 : Nat := 4983230072969 + 3 ^ 40 * 2045009 * 2
def baseEnd_2045009 : Nat := 1050072559770494626582681

theorem tailTrace_2045009 : CollatzResearch.WordTrace tailWord_2045009 prefixEnd_2045009 1050072559770494626582681 := by
  unfold tailWord_2045009
  simp only [CollatzResearch.WordTrace]
  refine ⟨74587605848289127576322081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49725070565526085050881387 74587605848289127576322081)
  ·
    refine ⟨55940704386216845682241561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74587605848289127576322081 55940704386216845682241561)
    ·
      refine ⟨41955528289662634261681171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55940704386216845682241561 41955528289662634261681171)
      ·
        refine ⟨62933292434493951392521757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41955528289662634261681171 62933292434493951392521757)
        ·
          refine ⟨23599984662935231772195659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62933292434493951392521757 23599984662935231772195659)
          ·
            refine ⟨35399976994402847658293489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23599984662935231772195659 35399976994402847658293489)
            ·
              refine ⟨26549982745802135743720117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35399976994402847658293489 26549982745802135743720117)
              ·
                refine ⟨2489060882418950225973761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26549982745802135743720117 2489060882418950225973761)
                ·
                  refine ⟨1866795661814212669480321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489060882418950225973761 1866795661814212669480321)
                  ·
                    refine ⟨1400096746360659502110241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866795661814212669480321 1400096746360659502110241)
                    ·
                      refine ⟨1050072559770494626582681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400096746360659502110241 1050072559770494626582681)
                      ·
                        rfl

theorem cell23_2045009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_2045009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045009 prefixEnd_2045009 := by exact prefixLift 2045009
  have htrace : WordTrace (prefixWord ++ tailWord_2045009) baseStart_2045009 baseEnd_2045009 := by
    simpa [prefixWord, tailWord_2045009, baseEnd_2045009] using wordTrace_append hprefix tailTrace_2045009
  have hstable : (prefixWord ++ tailWord_2045009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045009).length < 2 ^ (prefixWord ++ tailWord_2045009).sum := by decide
  have hdescent : baseEnd_2045009 < baseStart_2045009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045025 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_2045025 : Nat := 118140960795 + 2045025 * 2 ^ 59
def prefixEnd_2045025 : Nat := 4983230072969 + 3 ^ 40 * 2045025 * 2
def baseEnd_2045025 : Nat := 1050080775460966563982607

theorem tailTrace_2045025 : CollatzResearch.WordTrace tailWord_2045025 prefixEnd_2045025 1050080775460966563982607 := by
  unfold tailWord_2045025
  simp only [CollatzResearch.WordTrace]
  refine ⟨74588189416231162308904529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49725459610820774872603019 74588189416231162308904529)
  ·
    refine ⟨55941142062173371731678397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74588189416231162308904529 55941142062173371731678397)
    ·
      refine ⟨20977928273315014399379399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55941142062173371731678397 20977928273315014399379399)
      ·
        refine ⟨31466892409972521599069099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20977928273315014399379399 31466892409972521599069099)
        ·
          refine ⟨47200338614958782398603649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31466892409972521599069099 47200338614958782398603649)
          ·
            refine ⟨35400253961219086798952737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47200338614958782398603649 35400253961219086798952737)
            ·
              refine ⟨26550190470914315099214553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35400253961219086798952737 26550190470914315099214553)
              ·
                refine ⟨19912642853185736324410915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26550190470914315099214553 19912642853185736324410915)
                ·
                  refine ⟨29868964279778604486616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19912642853185736324410915 29868964279778604486616373)
                  ·
                    refine ⟨2800215401229244170620285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29868964279778604486616373 2800215401229244170620285)
                    ·
                      refine ⟨1050080775460966563982607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2800215401229244170620285 1050080775460966563982607)
                      ·
                        rfl

theorem cell23_2045025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_2045025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045025 prefixEnd_2045025 := by exact prefixLift 2045025
  have htrace : WordTrace (prefixWord ++ tailWord_2045025) baseStart_2045025 baseEnd_2045025 := by
    simpa [prefixWord, tailWord_2045025, baseEnd_2045025] using wordTrace_append hprefix tailTrace_2045025
  have hstable : (prefixWord ++ tailWord_2045025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045025).length < 2 ^ (prefixWord ++ tailWord_2045025).sum := by decide
  have hdescent : baseEnd_2045025 < baseStart_2045025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045026 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2045026 : Nat := 118140960795 + 2045026 * 2 ^ 59
def prefixEnd_2045026 : Nat := 4983230072969 + 3 ^ 40 * 2045026 * 2
def baseEnd_2045026 : Nat := 1050081288941621060070103

theorem tailTrace_2045026 : CollatzResearch.WordTrace tailWord_2045026 prefixEnd_2045026 1050081288941621060070103 := by
  unfold tailWord_2045026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18647056472306884869922733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49725483926151692986460621 18647056472306884869922733)
  ·
    refine ⟨6992646177115081826221025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18647056472306884869922733 6992646177115081826221025)
    ·
      refine ⟨5244484632836311369665769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6992646177115081826221025 5244484632836311369665769)
      ·
        refine ⟨3933363474627233527249327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5244484632836311369665769 3933363474627233527249327)
        ·
          refine ⟨5900045211940850290873991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933363474627233527249327 5900045211940850290873991)
          ·
            refine ⟨8850067817911275436310987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900045211940850290873991 8850067817911275436310987)
            ·
              refine ⟨13275101726866913154466481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850067817911275436310987 13275101726866913154466481)
              ·
                refine ⟨9956326295150184865849861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13275101726866913154466481 9956326295150184865849861)
                ·
                  refine ⟨1866811180340659662346849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9956326295150184865849861 1866811180340659662346849)
                  ·
                    refine ⟨1400108385255494746760137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1866811180340659662346849 1400108385255494746760137)
                    ·
                      refine ⟨1050081288941621060070103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400108385255494746760137 1050081288941621060070103)
                      ·
                        rfl

theorem cell23_2045026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2045026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045026 prefixEnd_2045026 := by exact prefixLift 2045026
  have htrace : WordTrace (prefixWord ++ tailWord_2045026) baseStart_2045026 baseEnd_2045026 := by
    simpa [prefixWord, tailWord_2045026, baseEnd_2045026] using wordTrace_append hprefix tailTrace_2045026
  have hstable : (prefixWord ++ tailWord_2045026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045026).length < 2 ^ (prefixWord ++ tailWord_2045026).sum := by decide
  have hdescent : baseEnd_2045026 < baseStart_2045026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045049 : List Nat := [1, 2, 1, 3, 6, 1, 1, 1, 7]
def baseStart_2045049 : Nat := 118140960795 + 2045049 * 2 ^ 59
def prefixEnd_2045049 : Nat := 4983230072969 + 3 ^ 40 * 2045049 * 2
def baseEnd_2045049 : Nat := 116677010999630496675833

theorem tailTrace_2045049 : CollatzResearch.WordTrace tailWord_2045049 prefixEnd_2045049 116677010999630496675833 := by
  unfold tailWord_2045049
  simp only [CollatzResearch.WordTrace]
  refine ⟨74589064768144214407778201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49726043178762809605185467 74589064768144214407778201)
  ·
    refine ⟨55941798576108160805833651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74589064768144214407778201 55941798576108160805833651)
    ·
      refine ⟨83912697864162241208750477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55941798576108160805833651 83912697864162241208750477)
      ·
        refine ⟨31467261699060840453281429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83912697864162241208750477 31467261699060840453281429)
        ·
          refine ⟨1475027892143476896247567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31467261699060840453281429 1475027892143476896247567)
          ·
            refine ⟨2212541838215215344371351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475027892143476896247567 2212541838215215344371351)
            ·
              refine ⟨3318812757322823016557027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2212541838215215344371351 3318812757322823016557027)
              ·
                refine ⟨4978219135984234524835541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3318812757322823016557027 4978219135984234524835541)
                ·
                  refine ⟨116677010999630496675833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4978219135984234524835541 116677010999630496675833)
                  ·
                    rfl

theorem cell23_2045049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 7].length) (baseStart_2045049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045049 prefixEnd_2045049 := by exact prefixLift 2045049
  have htrace : WordTrace (prefixWord ++ tailWord_2045049) baseStart_2045049 baseEnd_2045049 := by
    simpa [prefixWord, tailWord_2045049, baseEnd_2045049] using wordTrace_append hprefix tailTrace_2045049
  have hstable : (prefixWord ++ tailWord_2045049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045049).length < 2 ^ (prefixWord ++ tailWord_2045049).sum := by decide
  have hdescent : baseEnd_2045049 < baseStart_2045049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045052 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_2045052 : Nat := 118140960795 + 2045052 * 2 ^ 59
def prefixEnd_2045052 : Nat := 4983230072969 + 3 ^ 40 * 2045052 * 2
def baseEnd_2045052 : Nat := 1050094639438637958344983

theorem tailTrace_2045052 : CollatzResearch.WordTrace tailWord_2045052 prefixEnd_2045052 1050094639438637958344983 := by
  unfold tailWord_2045052
  simp only [CollatzResearch.WordTrace]
  refine ⟨37294587093566672960068705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49726116124755563946758273 37294587093566672960068705)
  ·
    refine ⟨27970940320175004720051529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37294587093566672960068705 27970940320175004720051529)
    ·
      refine ⟨20978205240131253540038647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27970940320175004720051529 20978205240131253540038647)
      ·
        refine ⟨31467307860196880310057971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20978205240131253540038647 31467307860196880310057971)
        ·
          refine ⟨47200961790295320465086957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31467307860196880310057971 47200961790295320465086957)
          ·
            refine ⟨17700360671360745174407609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47200961790295320465086957 17700360671360745174407609)
            ·
              refine ⟨13275270503520558880805707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17700360671360745174407609 13275270503520558880805707)
              ·
                refine ⟨19912905755280838321208561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13275270503520558880805707 19912905755280838321208561)
                ·
                  refine ⟨14934679316460628740906421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19912905755280838321208561 14934679316460628740906421)
                  ·
                    refine ⟨1400126185918183944459977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14934679316460628740906421 1400126185918183944459977)
                    ·
                      refine ⟨1050094639438637958344983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400126185918183944459977 1050094639438637958344983)
                      ·
                        rfl

theorem cell23_2045052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_2045052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045052 prefixEnd_2045052 := by exact prefixLift 2045052
  have htrace : WordTrace (prefixWord ++ tailWord_2045052) baseStart_2045052 baseEnd_2045052 := by
    simpa [prefixWord, tailWord_2045052, baseEnd_2045052] using wordTrace_append hprefix tailTrace_2045052
  have hstable : (prefixWord ++ tailWord_2045052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045052).length < 2 ^ (prefixWord ++ tailWord_2045052).sum := by decide
  have hdescent : baseEnd_2045052 < baseStart_2045052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045054 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_2045054 : Nat := 118140960795 + 2045054 * 2 ^ 59
def prefixEnd_2045054 : Nat := 4983230072969 + 3 ^ 40 * 2045054 * 2
def baseEnd_2045054 : Nat := 1050095666399946950519975

theorem tailTrace_2045054 : CollatzResearch.WordTrace tailWord_2045054 prefixEnd_2045054 1050095666399946950519975 := by
  unfold tailWord_2045054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9323655891640762532713777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49726164755417400174473477 9323655891640762532713777)
  ·
    refine ⟨6992741918730571899535333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9323655891640762532713777 6992741918730571899535333)
    ·
      refine ⟨1311139109761982231162875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6992741918730571899535333 1311139109761982231162875)
      ·
        refine ⟨1966708664642973346744313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311139109761982231162875 1966708664642973346744313)
        ·
          refine ⟨1475031498482230010058235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1966708664642973346744313 1475031498482230010058235)
          ·
            refine ⟨2212547247723345015087353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475031498482230010058235 2212547247723345015087353)
            ·
              refine ⟨1659410435792508761315515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212547247723345015087353 1659410435792508761315515)
              ·
                refine ⟨2489115653688763141973273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659410435792508761315515 2489115653688763141973273)
                ·
                  refine ⟨1866836740266572356479955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489115653688763141973273 1866836740266572356479955)
                  ·
                    refine ⟨2800255110399858534719933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1866836740266572356479955 2800255110399858534719933)
                    ·
                      refine ⟨1050095666399946950519975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2800255110399858534719933 1050095666399946950519975)
                      ·
                        rfl

theorem cell23_2045054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_2045054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045054 prefixEnd_2045054 := by exact prefixLift 2045054
  have htrace : WordTrace (prefixWord ++ tailWord_2045054) baseStart_2045054 baseEnd_2045054 := by
    simpa [prefixWord, tailWord_2045054, baseEnd_2045054] using wordTrace_append hprefix tailTrace_2045054
  have hstable : (prefixWord ++ tailWord_2045054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045054).length < 2 ^ (prefixWord ++ tailWord_2045054).sum := by decide
  have hdescent : baseEnd_2045054 < baseStart_2045054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045145 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_2045145 : Nat := 118140960795 + 2045145 * 2 ^ 59
def prefixEnd_2045145 : Nat := 4983230072969 + 3 ^ 40 * 2045145 * 2
def baseEnd_2045145 : Nat := 1050142393139506094482055

theorem tailTrace_2045145 : CollatzResearch.WordTrace tailWord_2045145 prefixEnd_2045145 1050142393139506094482055 := by
  unfold tailWord_2045145
  simp only [CollatzResearch.WordTrace]
  refine ⟨74592566175796422803272889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49728377450530948535515259 74592566175796422803272889)
  ·
    refine ⟨55944424631847317102454667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74592566175796422803272889 55944424631847317102454667)
    ·
      refine ⟨83916636947770975653682001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55944424631847317102454667 83916636947770975653682001)
      ·
        refine ⟨62937477710828231740261501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83916636947770975653682001 62937477710828231740261501)
        ·
          refine ⟨23601554141560586902598063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62937477710828231740261501 23601554141560586902598063)
          ·
            refine ⟨35402331212340880353897095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23601554141560586902598063 35402331212340880353897095)
            ·
              refine ⟨53103496818511320530845643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35402331212340880353897095 53103496818511320530845643)
              ·
                refine ⟨79655245227766980796268465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53103496818511320530845643 79655245227766980796268465)
                ·
                  refine ⟨59741433920825235597201349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79655245227766980796268465 59741433920825235597201349)
                  ·
                    refine ⟨11201518860154731674475253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59741433920825235597201349 11201518860154731674475253)
                    ·
                      refine ⟨1050142393139506094482055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11201518860154731674475253 1050142393139506094482055)
                      ·
                        rfl

theorem cell23_2045145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_2045145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045145 prefixEnd_2045145 := by exact prefixLift 2045145
  have htrace : WordTrace (prefixWord ++ tailWord_2045145) baseStart_2045145 baseEnd_2045145 := by
    simpa [prefixWord, tailWord_2045145, baseEnd_2045145] using wordTrace_append hprefix tailTrace_2045145
  have hstable : (prefixWord ++ tailWord_2045145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045145).length < 2 ^ (prefixWord ++ tailWord_2045145).sum := by decide
  have hdescent : baseEnd_2045145 < baseStart_2045145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045189 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_2045189 : Nat := 118140960795 + 2045189 * 2 ^ 59
def prefixEnd_2045189 : Nat := 4983230072969 + 3 ^ 40 * 2045189 * 2
def baseEnd_2045189 : Nat := 1050164986288303922331853

theorem tailTrace_2045189 : CollatzResearch.WordTrace tailWord_2045189 prefixEnd_2045189 1050164986288303922331853 := by
  unfold tailWord_2045189
  simp only [CollatzResearch.WordTrace]
  refine ⟨74594170987637018317874621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49729447325091345545249747 74594170987637018317874621)
  ·
    refine ⟨27972814120363881869202983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74594170987637018317874621 27972814120363881869202983)
    ·
      refine ⟨41959221180545822803804475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27972814120363881869202983 41959221180545822803804475)
      ·
        refine ⟨62938831770818734205706713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41959221180545822803804475 62938831770818734205706713)
        ·
          refine ⟨47204123828114050654280035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62938831770818734205706713 47204123828114050654280035)
          ·
            refine ⟨70806185742171075981420053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47204123828114050654280035 70806185742171075981420053)
            ·
              refine ⟨3319039956664269186629065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70806185742171075981420053 3319039956664269186629065)
              ·
                refine ⟨2489279967498201889971799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319039956664269186629065 2489279967498201889971799)
                ·
                  refine ⟨3733919951247302834957699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489279967498201889971799 3733919951247302834957699)
                  ·
                    refine ⟨5600879926870954252436549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3733919951247302834957699 5600879926870954252436549)
                    ·
                      refine ⟨1050164986288303922331853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5600879926870954252436549 1050164986288303922331853)
                      ·
                        rfl

theorem cell23_2045189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_2045189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045189 prefixEnd_2045189 := by exact prefixLift 2045189
  have htrace : WordTrace (prefixWord ++ tailWord_2045189) baseStart_2045189 baseEnd_2045189 := by
    simpa [prefixWord, tailWord_2045189, baseEnd_2045189] using wordTrace_append hprefix tailTrace_2045189
  have hstable : (prefixWord ++ tailWord_2045189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045189).length < 2 ^ (prefixWord ++ tailWord_2045189).sum := by decide
  have hdescent : baseEnd_2045189 < baseStart_2045189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045229 : List Nat := [1, 5, 3, 1, 1, 1, 1, 10]
def baseStart_2045229 : Nat := 118140960795 + 2045229 * 2 ^ 59
def prefixEnd_2045229 : Nat := 4983230072969 + 3 ^ 40 * 2045229 * 2
def baseEnd_2045229 : Nat := 38895760204240139475247

theorem tailTrace_2045229 : CollatzResearch.WordTrace tailWord_2045229 prefixEnd_2045229 38895760204240139475247 := by
  unfold tailWord_2045229
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595629907492105149330741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49730419938328070099553827 74595629907492105149330741)
  ·
    refine ⟨6993340303827384857749757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74595629907492105149330741 6993340303827384857749757)
    ·
      refine ⟨2622502613935269321656159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6993340303827384857749757 2622502613935269321656159)
      ·
        refine ⟨3933753920902903982484239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2622502613935269321656159 3933753920902903982484239)
        ·
          refine ⟨5900630881354355973726359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3933753920902903982484239 5900630881354355973726359)
          ·
            refine ⟨8850946322031533960589539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5900630881354355973726359 8850946322031533960589539)
            ·
              refine ⟨13276419483047300940884309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8850946322031533960589539 13276419483047300940884309)
              ·
                refine ⟨38895760204240139475247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13276419483047300940884309 38895760204240139475247)
                ·
                  rfl

theorem cell23_2045229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 10].length) (baseStart_2045229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045229 prefixEnd_2045229 := by exact prefixLift 2045229
  have htrace : WordTrace (prefixWord ++ tailWord_2045229) baseStart_2045229 baseEnd_2045229 := by
    simpa [prefixWord, tailWord_2045229, baseEnd_2045229] using wordTrace_append hprefix tailTrace_2045229
  have hstable : (prefixWord ++ tailWord_2045229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045229).length < 2 ^ (prefixWord ++ tailWord_2045229).sum := by decide
  have hdescent : baseEnd_2045229 < baseStart_2045229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045233 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 2, 4]
def baseStart_2045233 : Nat := 118140960795 + 2045233 * 2 ^ 59
def prefixEnd_2045233 : Nat := 4983230072969 + 3 ^ 40 * 2045233 * 2
def baseEnd_2045233 : Nat := 350062526479033916727217

theorem tailTrace_2045233 : CollatzResearch.WordTrace tailWord_2045233 prefixEnd_2045233 350062526479033916727217 := by
  unfold tailWord_2045233
  simp only [CollatzResearch.WordTrace]
  refine ⟨74595775799477613832476353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49730517199651742554984235 74595775799477613832476353)
  ·
    refine ⟨55946831849608210374357265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74595775799477613832476353 55946831849608210374357265)
    ·
      refine ⟨41960123887206157780767949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55946831849608210374357265 41960123887206157780767949)
      ·
        refine ⟨15735046457702309167787981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41960123887206157780767949 15735046457702309167787981)
        ·
          refine ⟨5900642421638365937920493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15735046457702309167787981 5900642421638365937920493)
          ·
            refine ⟨2212740908114387226720185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5900642421638365937920493 2212740908114387226720185)
            ·
              refine ⟨1659555681085790420040139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212740908114387226720185 1659555681085790420040139)
              ·
                refine ⟨2489333521628685630060209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659555681085790420040139 2489333521628685630060209)
                ·
                  refine ⟨1867000141221514222545157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489333521628685630060209 1867000141221514222545157)
                  ·
                    refine ⟨350062526479033916727217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867000141221514222545157 350062526479033916727217)
                    ·
                      rfl

theorem cell23_2045233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_2045233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045233 prefixEnd_2045233 := by exact prefixLift 2045233
  have htrace : WordTrace (prefixWord ++ tailWord_2045233) baseStart_2045233 baseEnd_2045233 := by
    simpa [prefixWord, tailWord_2045233, baseEnd_2045233] using wordTrace_append hprefix tailTrace_2045233
  have hstable : (prefixWord ++ tailWord_2045233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045233).length < 2 ^ (prefixWord ++ tailWord_2045233).sum := by decide
  have hdescent : baseEnd_2045233 < baseStart_2045233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045272 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 2, 6]
def baseStart_2045272 : Nat := 118140960795 + 2045272 * 2 ^ 59
def prefixEnd_2045272 : Nat := 4983230072969 + 3 ^ 40 * 2045272 * 2
def baseEnd_2045272 : Nat := 350069201727542365864657

theorem tailTrace_2045272 : CollatzResearch.WordTrace tailWord_2045272 prefixEnd_2045272 350069201727542365864657 := by
  unfold tailWord_2045272
  simp only [CollatzResearch.WordTrace]
  refine ⟨37298599123168161746573035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49731465497557548995430713 37298599123168161746573035)
  ·
    refine ⟨55947898684752242619859553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37298599123168161746573035 55947898684752242619859553)
    ·
      refine ⟨41960924013564181964894665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55947898684752242619859553 41960924013564181964894665)
      ·
        refine ⟨31470693010173136473670999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41960924013564181964894665 31470693010173136473670999)
        ·
          refine ⟨47206039515259704710506499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31470693010173136473670999 47206039515259704710506499)
          ·
            refine ⟨70809059272889557065759749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47206039515259704710506499 70809059272889557065759749)
            ·
              refine ⟨13276698613666791949829953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70809059272889557065759749 13276698613666791949829953)
              ·
                refine ⟨9957523960250093962372465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13276698613666791949829953 9957523960250093962372465)
                ·
                  refine ⟨7468142970187570471779349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957523960250093962372465 7468142970187570471779349)
                  ·
                    refine ⟨350069201727542365864657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7468142970187570471779349 350069201727542365864657)
                    ·
                      rfl

theorem cell23_2045272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_2045272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045272 prefixEnd_2045272 := by exact prefixLift 2045272
  have htrace : WordTrace (prefixWord ++ tailWord_2045272) baseStart_2045272 baseEnd_2045272 := by
    simpa [prefixWord, tailWord_2045272, baseEnd_2045272] using wordTrace_append hprefix tailTrace_2045272
  have hstable : (prefixWord ++ tailWord_2045272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045272).length < 2 ^ (prefixWord ++ tailWord_2045272).sum := by decide
  have hdescent : baseEnd_2045272 < baseStart_2045272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045279 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 5, 4, 2]
def baseStart_2045279 : Nat := 118140960795 + 2045279 * 2 ^ 59
def prefixEnd_2045279 : Nat := 4983230072969 + 3 ^ 40 * 2045279 * 2
def baseEnd_2045279 : Nat := 1050211199547208570206439

theorem tailTrace_2045279 : CollatzResearch.WordTrace tailWord_2045279 prefixEnd_2045279 1050211199547208570206439 := by
  unfold tailWord_2045279
  simp only [CollatzResearch.WordTrace]
  refine ⟨74597453557310963688650891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49731635704873975792433927 74597453557310963688650891)
  ·
    refine ⟨111896180335966445532976337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74597453557310963688650891 111896180335966445532976337)
    ·
      refine ⟨83922135251974834149732253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111896180335966445532976337 83922135251974834149732253)
      ·
        refine ⟨31470800719490562806149595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83922135251974834149732253 31470800719490562806149595)
        ·
          refine ⟨47206201079235844209224393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31470800719490562806149595 47206201079235844209224393)
          ·
            refine ⟨35404650809426883156918295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47206201079235844209224393 35404650809426883156918295)
            ·
              refine ⟨53106976214140324735377443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35404650809426883156918295 53106976214140324735377443)
              ·
                refine ⟨79660464321210487103066165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53106976214140324735377443 79660464321210487103066165)
                ·
                  refine ⟨7468168530113483165912453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79660464321210487103066165 7468168530113483165912453)
                  ·
                    refine ⟨1400281599396278093608585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468168530113483165912453 1400281599396278093608585)
                    ·
                      refine ⟨1050211199547208570206439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400281599396278093608585 1050211199547208570206439)
                      ·
                        rfl

theorem cell23_2045279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 4, 2].length) (baseStart_2045279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045279 prefixEnd_2045279 := by exact prefixLift 2045279
  have htrace : WordTrace (prefixWord ++ tailWord_2045279) baseStart_2045279 baseEnd_2045279 := by
    simpa [prefixWord, tailWord_2045279, baseEnd_2045279] using wordTrace_append hprefix tailTrace_2045279
  have hstable : (prefixWord ++ tailWord_2045279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045279).length < 2 ^ (prefixWord ++ tailWord_2045279).sum := by decide
  have hdescent : baseEnd_2045279 < baseStart_2045279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045296 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2]
def baseStart_2045296 : Nat := 118140960795 + 2045296 * 2 ^ 59
def prefixEnd_2045296 : Nat := 4983230072969 + 3 ^ 40 * 2045296 * 2
def baseEnd_2045296 : Nat := 1050219928718335003693861

theorem tailTrace_2045296 : CollatzResearch.WordTrace tailWord_2045296 prefixEnd_2045296 1050219928718335003693861 := by
  unfold tailWord_2045296
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299036799124687796009871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49732049065499583728013161 37299036799124687796009871)
  ·
    refine ⟨55948555198687031694014807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37299036799124687796009871 55948555198687031694014807)
    ·
      refine ⟨83922832798030547541022211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55948555198687031694014807 83922832798030547541022211)
      ·
        refine ⟨125884249197045821311533317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83922832798030547541022211 125884249197045821311533317)
        ·
          refine ⟨23603296724446091495912497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125884249197045821311533317 23603296724446091495912497)
          ·
            refine ⟨17702472543334568621934373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23603296724446091495912497 17702472543334568621934373)
            ·
              refine ⟨3319213601875231616612695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17702472543334568621934373 3319213601875231616612695)
              ·
                refine ⟨4978820402812847424919043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319213601875231616612695 4978820402812847424919043)
                ·
                  refine ⟨7468230604219271137378565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4978820402812847424919043 7468230604219271137378565)
                  ·
                    refine ⟨1400293238291113338258481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7468230604219271137378565 1400293238291113338258481)
                    ·
                      refine ⟨1050219928718335003693861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400293238291113338258481 1050219928718335003693861)
                      ·
                        rfl

theorem cell23_2045296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 4, 2].length) (baseStart_2045296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045296 prefixEnd_2045296 := by exact prefixLift 2045296
  have htrace : WordTrace (prefixWord ++ tailWord_2045296) baseStart_2045296 baseEnd_2045296 := by
    simpa [prefixWord, tailWord_2045296, baseEnd_2045296] using wordTrace_append hprefix tailTrace_2045296
  have hstable : (prefixWord ++ tailWord_2045296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045296).length < 2 ^ (prefixWord ++ tailWord_2045296).sum := by decide
  have hdescent : baseEnd_2045296 < baseStart_2045296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045336 : List Nat := [2, 1, 2, 5, 2, 1, 2, 1, 7]
def baseStart_2045336 : Nat := 118140960795 + 2045336 * 2 ^ 59
def prefixEnd_2045336 : Nat := 4983230072969 + 3 ^ 40 * 2045336 * 2
def baseEnd_2045336 : Nat := 116693385327168316354853

theorem tailTrace_2045336 : CollatzResearch.WordTrace tailWord_2045336 prefixEnd_2045336 116693385327168316354853 := by
  unfold tailWord_2045336
  simp only [CollatzResearch.WordTrace]
  refine ⟨37299766259052231211737931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49733021678736308282317241 37299766259052231211737931)
  ·
    refine ⟨55949649388578346817606897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37299766259052231211737931 55949649388578346817606897)
    ·
      refine ⟨41962237041433760113205173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55949649388578346817606897 41962237041433760113205173)
      ·
        refine ⟨3933959722634415010612985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41962237041433760113205173 3933959722634415010612985)
        ·
          refine ⟨2950469791975811257959739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3933959722634415010612985 2950469791975811257959739)
          ·
            refine ⟨4425704687963716886939609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950469791975811257959739 4425704687963716886939609)
            ·
              refine ⟨3319278515972787665204707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4425704687963716886939609 3319278515972787665204707)
              ·
                refine ⟨4978917773959181497807061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3319278515972787665204707 4978917773959181497807061)
                ·
                  refine ⟨116693385327168316354853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4978917773959181497807061 116693385327168316354853)
                  ·
                    rfl

theorem cell23_2045336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 1, 7].length) (baseStart_2045336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045336 prefixEnd_2045336 := by exact prefixLift 2045336
  have htrace : WordTrace (prefixWord ++ tailWord_2045336) baseStart_2045336 baseEnd_2045336 := by
    simpa [prefixWord, tailWord_2045336, baseEnd_2045336] using wordTrace_append hprefix tailTrace_2045336
  have hstable : (prefixWord ++ tailWord_2045336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045336).length < 2 ^ (prefixWord ++ tailWord_2045336).sum := by decide
  have hdescent : baseEnd_2045336 < baseStart_2045336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045346 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2045346 : Nat := 118140960795 + 2045346 * 2 ^ 59
def prefixEnd_2045346 : Nat := 4983230072969 + 3 ^ 40 * 2045346 * 2
def baseEnd_2045346 : Nat := 1050245602751059808068631

theorem tailTrace_2045346 : CollatzResearch.WordTrace tailWord_2045346 prefixEnd_2045346 1050245602751059808068631 := by
  unfold tailWord_2045346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18649974312017058532834973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49733264832045489420893261 18649974312017058532834973)
  ·
    refine ⟨6993740367006396949813115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18649974312017058532834973 6993740367006396949813115)
    ·
      refine ⟨10490610550509595424719673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6993740367006396949813115 10490610550509595424719673)
      ·
        refine ⟨7867957912882196568539755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10490610550509595424719673 7867957912882196568539755)
        ·
          refine ⟨11801936869323294852809633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7867957912882196568539755 11801936869323294852809633)
          ·
            refine ⟨8851452651992471139607225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11801936869323294852809633 8851452651992471139607225)
            ·
              refine ⟨6638589488994353354705419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8851452651992471139607225 6638589488994353354705419)
              ·
                refine ⟨9957884233491530032058129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6638589488994353354705419 9957884233491530032058129)
                ·
                  refine ⟨7468413175118647524043597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9957884233491530032058129 7468413175118647524043597)
                  ·
                    refine ⟨2800654940669492821516349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7468413175118647524043597 2800654940669492821516349)
                    ·
                      refine ⟨1050245602751059808068631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2800654940669492821516349 1050245602751059808068631)
                      ·
                        rfl

theorem cell23_2045346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2045346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045346 prefixEnd_2045346 := by exact prefixLift 2045346
  have htrace : WordTrace (prefixWord ++ tailWord_2045346) baseStart_2045346 baseEnd_2045346 := by
    simpa [prefixWord, tailWord_2045346, baseEnd_2045346] using wordTrace_append hprefix tailTrace_2045346
  have hstable : (prefixWord ++ tailWord_2045346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045346).length < 2 ^ (prefixWord ++ tailWord_2045346).sum := by decide
  have hdescent : baseEnd_2045346 < baseStart_2045346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045379 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 5, 4]
def baseStart_2045379 : Nat := 118140960795 + 2045379 * 2 ^ 59
def prefixEnd_2045379 : Nat := 4983230072969 + 3 ^ 40 * 2045379 * 2
def baseEnd_2045379 : Nat := 350087515870886059651993

theorem tailTrace_2045379 : CollatzResearch.WordTrace tailWord_2045379 prefixEnd_2045379 350087515870886059651993 := by
  unfold tailWord_2045379
  simp only [CollatzResearch.WordTrace]
  refine ⟨74601100856948680767291191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49734067237965787178194127 74601100856948680767291191)
  ·
    refine ⟨111901651285423021150936787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74601100856948680767291191 111901651285423021150936787)
    ·
      refine ⟨167852476928134531726405181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111901651285423021150936787 167852476928134531726405181)
      ·
        refine ⟨62944678848050449397401943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167852476928134531726405181 62944678848050449397401943)
        ·
          refine ⟨94417018272075674096102915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62944678848050449397401943 94417018272075674096102915)
          ·
            refine ⟨141625527408113511144154373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94417018272075674096102915 141625527408113511144154373)
            ·
              refine ⟨26554786389021283339528945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141625527408113511144154373 26554786389021283339528945)
              ·
                refine ⟨19916089791765962504646709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26554786389021283339528945 19916089791765962504646709)
                ·
                  refine ⟨1867133417978058984810629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19916089791765962504646709 1867133417978058984810629)
                  ·
                    refine ⟨350087515870886059651993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867133417978058984810629 350087515870886059651993)
                    ·
                      rfl

theorem cell23_2045379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 4].length) (baseStart_2045379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045379 prefixEnd_2045379 := by exact prefixLift 2045379
  have htrace : WordTrace (prefixWord ++ tailWord_2045379) baseStart_2045379 baseEnd_2045379 := by
    simpa [prefixWord, tailWord_2045379, baseEnd_2045379] using wordTrace_append hprefix tailTrace_2045379
  have hstable : (prefixWord ++ tailWord_2045379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045379).length < 2 ^ (prefixWord ++ tailWord_2045379).sum := by decide
  have hdescent : baseEnd_2045379 < baseStart_2045379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045386 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_2045386 : Nat := 118140960795 + 2045386 * 2 ^ 59
def prefixEnd_2045386 : Nat := 4983230072969 + 3 ^ 40 * 2045386 * 2
def baseEnd_2045386 : Nat := 1050266141977239651568447

theorem tailTrace_2045386 : CollatzResearch.WordTrace tailWord_2045386 prefixEnd_2045386 1050266141977239651568447 := by
  unfold tailWord_2045386
  simp only [CollatzResearch.WordTrace]
  refine ⟨18650339041980830240699003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49734237445282213975197341 18650339041980830240699003)
  ·
    refine ⟨27975508562971245361048505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18650339041980830240699003 27975508562971245361048505)
    ·
      refine ⟨20981631422228434020786379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27975508562971245361048505 20981631422228434020786379)
      ·
        refine ⟨31472447133342651031179569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20981631422228434020786379 31472447133342651031179569)
        ·
          refine ⟨23604335350006988273384677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31472447133342651031179569 23604335350006988273384677)
          ·
            refine ⟨4425812878126310301259627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23604335350006988273384677 4425812878126310301259627)
            ·
              refine ⟨6638719317189465451889441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4425812878126310301259627 6638719317189465451889441)
              ·
                refine ⟨4979039487892099088917081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6638719317189465451889441 4979039487892099088917081)
                ·
                  refine ⟨3734279615919074316687811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4979039487892099088917081 3734279615919074316687811)
                  ·
                    refine ⟨5601419423878611475031717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734279615919074316687811 5601419423878611475031717)
                    ·
                      refine ⟨1050266141977239651568447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5601419423878611475031717 1050266141977239651568447)
                      ·
                        rfl

theorem cell23_2045386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_2045386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045386 prefixEnd_2045386 := by exact prefixLift 2045386
  have htrace : WordTrace (prefixWord ++ tailWord_2045386) baseStart_2045386 baseEnd_2045386 := by
    simpa [prefixWord, tailWord_2045386, baseEnd_2045386] using wordTrace_append hprefix tailTrace_2045386
  have hstable : (prefixWord ++ tailWord_2045386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045386).length < 2 ^ (prefixWord ++ tailWord_2045386).sum := by decide
  have hdescent : baseEnd_2045386 < baseStart_2045386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045447 : List Nat := [1, 1, 4, 3, 2, 3, 2, 2, 1, 4]
def baseStart_2045447 : Nat := 118140960795 + 2045447 * 2 ^ 59
def prefixEnd_2045447 : Nat := 4983230072969 + 3 ^ 40 * 2045447 * 2
def baseEnd_2045447 : Nat := 350099154765721304301889

theorem tailTrace_2045447 : CollatzResearch.WordTrace tailWord_2045447 prefixEnd_2045447 350099154765721304301889 := by
  unfold tailWord_2045447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74603581020702328380766595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49735720680468218920511063 74603581020702328380766595)
  ·
    refine ⟨111905371531053492571149893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74603581020702328380766595 111905371531053492571149893)
    ·
      refine ⟨20982257162072529857090605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111905371531053492571149893 20982257162072529857090605)
      ·
        refine ⟨7868346435777198696408977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20982257162072529857090605 7868346435777198696408977)
        ·
          refine ⟨5901259826832899022306733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7868346435777198696408977 5901259826832899022306733)
          ·
            refine ⟨2212972435062337133365025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5901259826832899022306733 2212972435062337133365025)
            ·
              refine ⟨1659729326296752850023769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2212972435062337133365025 1659729326296752850023769)
              ·
                refine ⟨1244796994722564637517827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1659729326296752850023769 1244796994722564637517827)
                ·
                  refine ⟨1867195492083846956276741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244796994722564637517827 1867195492083846956276741)
                  ·
                    refine ⟨350099154765721304301889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867195492083846956276741 350099154765721304301889)
                    ·
                      rfl

theorem cell23_2045447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_2045447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045447 prefixEnd_2045447 := by exact prefixLift 2045447
  have htrace : WordTrace (prefixWord ++ tailWord_2045447) baseStart_2045447 baseEnd_2045447 := by
    simpa [prefixWord, tailWord_2045447, baseEnd_2045447] using wordTrace_append hprefix tailTrace_2045447
  have hstable : (prefixWord ++ tailWord_2045447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045447).length < 2 ^ (prefixWord ++ tailWord_2045447).sum := by decide
  have hdescent : baseEnd_2045447 < baseStart_2045447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045480 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_2045480 : Nat := 118140960795 + 2045480 * 2 ^ 59
def prefixEnd_2045480 : Nat := 4983230072969 + 3 ^ 40 * 2045480 * 2
def baseEnd_2045480 : Nat := 1050314409158762283793015

theorem tailTrace_2045480 : CollatzResearch.WordTrace tailWord_2045480 prefixEnd_2045480 1050314409158762283793015 := by
  unfold tailWord_2045480
  simp only [CollatzResearch.WordTrace]
  refine ⟨37302392314791387508358947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49736523086388516677811929 37302392314791387508358947)
  ·
    refine ⟨55953588472187081262538421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37302392314791387508358947 55953588472187081262538421)
    ·
      refine ⟨5245648919267538868362977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55953588472187081262538421 5245648919267538868362977)
      ·
        refine ⟨3934236689450654151272233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5245648919267538868362977 3934236689450654151272233)
        ·
          refine ⟨2950677517087990613454175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934236689450654151272233 2950677517087990613454175)
          ·
            refine ⟨4426016275631985920181263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2950677517087990613454175 4426016275631985920181263)
            ·
              refine ⟨6639024413447978880271895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426016275631985920181263 6639024413447978880271895)
              ·
                refine ⟨9958536620171968320407843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6639024413447978880271895 9958536620171968320407843)
                ·
                  refine ⟨14937804930257952480611765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9958536620171968320407843 14937804930257952480611765)
                  ·
                    refine ⟨1400419212211683045057353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14937804930257952480611765 1400419212211683045057353)
                    ·
                      refine ⟨1050314409158762283793015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400419212211683045057353 1050314409158762283793015)
                      ·
                        rfl

theorem cell23_2045480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_2045480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045480 prefixEnd_2045480 := by exact prefixLift 2045480
  have htrace : WordTrace (prefixWord ++ tailWord_2045480) baseStart_2045480 baseEnd_2045480 := by
    simpa [prefixWord, tailWord_2045480, baseEnd_2045480] using wordTrace_append hprefix tailTrace_2045480
  have hstable : (prefixWord ++ tailWord_2045480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045480).length < 2 ^ (prefixWord ++ tailWord_2045480).sum := by decide
  have hdescent : baseEnd_2045480 < baseStart_2045480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045489 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_2045489 : Nat := 118140960795 + 2045489 * 2 ^ 59
def prefixEnd_2045489 : Nat := 4983230072969 + 3 ^ 40 * 2045489 * 2
def baseEnd_2045489 : Nat := 1050319030484652748580473

theorem tailTrace_2045489 : CollatzResearch.WordTrace tailWord_2045489 prefixEnd_2045489 1050319030484652748580473 := by
  unfold tailWord_2045489
  simp only [CollatzResearch.WordTrace]
  refine ⟨74605112886550169553795521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49736741924366779702530347 74605112886550169553795521)
  ·
    refine ⟨55953834664912627165346641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74605112886550169553795521 55953834664912627165346641)
    ·
      refine ⟨41965375998684470374009981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55953834664912627165346641 41965375998684470374009981)
      ·
        refine ⟨15737015999506676390253743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41965375998684470374009981 15737015999506676390253743)
        ·
          refine ⟨23605523999260014585380615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737015999506676390253743 23605523999260014585380615)
          ·
            refine ⟨35408285998890021878070923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23605523999260014585380615 35408285998890021878070923)
            ·
              refine ⟨53112428998335032817106385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35408285998890021878070923 53112428998335032817106385)
              ·
                refine ⟨39834321748751274612829789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53112428998335032817106385 39834321748751274612829789)
                ·
                  refine ⟨14937870655781727979811171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39834321748751274612829789 14937870655781727979811171)
                  ·
                    refine ⟨22406805983672591969716757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14937870655781727979811171 22406805983672591969716757)
                    ·
                      refine ⟨1050319030484652748580473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22406805983672591969716757 1050319030484652748580473)
                      ·
                        rfl

theorem cell23_2045489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_2045489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045489 prefixEnd_2045489 := by exact prefixLift 2045489
  have htrace : WordTrace (prefixWord ++ tailWord_2045489) baseStart_2045489 baseEnd_2045489 := by
    simpa [prefixWord, tailWord_2045489, baseEnd_2045489] using wordTrace_append hprefix tailTrace_2045489
  have hstable : (prefixWord ++ tailWord_2045489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045489).length < 2 ^ (prefixWord ++ tailWord_2045489).sum := by decide
  have hdescent : baseEnd_2045489 < baseStart_2045489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045493 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_2045493 : Nat := 118140960795 + 2045493 * 2 ^ 59
def prefixEnd_2045493 : Nat := 4983230072969 + 3 ^ 40 * 2045493 * 2
def baseEnd_2045493 : Nat := 1050321084407270732930455

theorem tailTrace_2045493 : CollatzResearch.WordTrace tailWord_2045493 prefixEnd_2045493 1050321084407270732930455 := by
  unfold tailWord_2045493
  simp only [CollatzResearch.WordTrace]
  refine ⟨74605258778535678236941133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49736839185690452157960755 74605258778535678236941133)
  ·
    refine ⟨27976972041950879338852925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74605258778535678236941133 27976972041950879338852925)
    ·
      refine ⟨10491364515731579752069847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27976972041950879338852925 10491364515731579752069847)
      ·
        refine ⟨15737046773597369628104771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10491364515731579752069847 15737046773597369628104771)
        ·
          refine ⟨23605570160396054442157157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737046773597369628104771 23605570160396054442157157)
          ·
            refine ⟨4426044405074260207904467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23605570160396054442157157 4426044405074260207904467)
            ·
              refine ⟨6639066607611390311856701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426044405074260207904467 6639066607611390311856701)
              ·
                refine ⟨2489649977854271366946263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6639066607611390311856701 2489649977854271366946263)
                ·
                  refine ⟨3734474966781407050419395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489649977854271366946263 3734474966781407050419395)
                  ·
                    refine ⟨5601712450172110575629093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3734474966781407050419395 5601712450172110575629093)
                    ·
                      refine ⟨1050321084407270732930455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5601712450172110575629093 1050321084407270732930455)
                      ·
                        rfl

theorem cell23_2045493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_2045493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045493 prefixEnd_2045493 := by exact prefixLift 2045493
  have htrace : WordTrace (prefixWord ++ tailWord_2045493) baseStart_2045493 baseEnd_2045493 := by
    simpa [prefixWord, tailWord_2045493, baseEnd_2045493] using wordTrace_append hprefix tailTrace_2045493
  have hstable : (prefixWord ++ tailWord_2045493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045493).length < 2 ^ (prefixWord ++ tailWord_2045493).sum := by decide
  have hdescent : baseEnd_2045493 < baseStart_2045493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045503 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 2, 4]
def baseStart_2045503 : Nat := 118140960795 + 2045503 * 2 ^ 59
def prefixEnd_2045503 : Nat := 4983230072969 + 3 ^ 40 * 2045503 * 2
def baseEnd_2045503 : Nat := 350108739737938564601803

theorem tailTrace_2045503 : CollatzResearch.WordTrace tailWord_2045503 prefixEnd_2045503 350108739737938564601803 := by
  unfold tailWord_2045503
  simp only [CollatzResearch.WordTrace]
  refine ⟨74605623508499449944805163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49737082338999633296536775 74605623508499449944805163)
  ·
    refine ⟨111908435262749174917207745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74605623508499449944805163 111908435262749174917207745)
    ·
      refine ⟨83931326447061881187905809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111908435262749174917207745 83931326447061881187905809)
      ·
        refine ⟨62948494835296410890929357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83931326447061881187905809 62948494835296410890929357)
        ·
          refine ⟨23605685563236154084098509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62948494835296410890929357 23605685563236154084098509)
          ·
            refine ⟨8852132086213557781536941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23605685563236154084098509 8852132086213557781536941)
            ·
              refine ⟨3319549532330084168076353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8852132086213557781536941 3319549532330084168076353)
              ·
                refine ⟨2489662149247563126057265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3319549532330084168076353 2489662149247563126057265)
                ·
                  refine ⟨1867246611935672344542949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2489662149247563126057265 1867246611935672344542949)
                  ·
                    refine ⟨350108739737938564601803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867246611935672344542949 350108739737938564601803)
                    ·
                      rfl

theorem cell23_2045503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_2045503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045503 prefixEnd_2045503 := by exact prefixLift 2045503
  have htrace : WordTrace (prefixWord ++ tailWord_2045503) baseStart_2045503 baseEnd_2045503 := by
    simpa [prefixWord, tailWord_2045503, baseEnd_2045503] using wordTrace_append hprefix tailTrace_2045503
  have hstable : (prefixWord ++ tailWord_2045503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045503).length < 2 ^ (prefixWord ++ tailWord_2045503).sum := by decide
  have hdescent : baseEnd_2045503 < baseStart_2045503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045529 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_2045529 : Nat := 118140960795 + 2045529 * 2 ^ 59
def prefixEnd_2045529 : Nat := 4983230072969 + 3 ^ 40 * 2045529 * 2
def baseEnd_2045529 : Nat := 350113189903610864026763

theorem tailTrace_2045529 : CollatzResearch.WordTrace tailWord_2045529 prefixEnd_2045529 350113189903610864026763 := by
  unfold tailWord_2045529
  simp only [CollatzResearch.WordTrace]
  refine ⟨74606571806405256385251641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49737714537603504256834427 74606571806405256385251641)
  ·
    refine ⟨55954928854803942288938731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74606571806405256385251641 55954928854803942288938731)
    ·
      refine ⟨83932393282205913433408097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55954928854803942288938731 83932393282205913433408097)
      ·
        refine ⟨62949294961654435075056073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83932393282205913433408097 62949294961654435075056073)
        ·
          refine ⟨47211971221240826306292055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62949294961654435075056073 47211971221240826306292055)
          ·
            refine ⟨70817956831861239459438083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47211971221240826306292055 70817956831861239459438083)
            ·
              refine ⟨106226935247791859189157125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70817956831861239459438083 106226935247791859189157125)
              ·
                refine ⟨19917550358960973597966961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106226935247791859189157125 19917550358960973597966961)
                ·
                  refine ⟨14938162769220730198475221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19917550358960973597966961 14938162769220730198475221)
                  ·
                    refine ⟨350113189903610864026763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14938162769220730198475221 350113189903610864026763)
                    ·
                      rfl

theorem cell23_2045529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_2045529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045529 prefixEnd_2045529 := by exact prefixLift 2045529
  have htrace : WordTrace (prefixWord ++ tailWord_2045529) baseStart_2045529 baseEnd_2045529 := by
    simpa [prefixWord, tailWord_2045529, baseEnd_2045529] using wordTrace_append hprefix tailTrace_2045529
  have hstable : (prefixWord ++ tailWord_2045529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045529).length < 2 ^ (prefixWord ++ tailWord_2045529).sum := by decide
  have hdescent : baseEnd_2045529 < baseStart_2045529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045543 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_2045543 : Nat := 118140960795 + 2045543 * 2 ^ 59
def prefixEnd_2045543 : Nat := 4983230072969 + 3 ^ 40 * 2045543 * 2
def baseEnd_2045543 : Nat := 1050346758439995537305225

theorem tailTrace_2045543 : CollatzResearch.WordTrace tailWord_2045543 prefixEnd_2045543 1050346758439995537305225 := by
  unfold tailWord_2045543
  simp only [CollatzResearch.WordTrace]
  refine ⟨74607082428354536776261283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49738054952236357850840855 74607082428354536776261283)
  ·
    refine ⟨111910623642531805164391925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74607082428354536776261283 111910623642531805164391925)
    ·
      refine ⟨10491620966487356734161743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111910623642531805164391925 10491620966487356734161743)
      ·
        refine ⟨15737431449731035101242615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10491620966487356734161743 15737431449731035101242615)
        ·
          refine ⟨23606147174596552651863923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15737431449731035101242615 23606147174596552651863923)
          ·
            refine ⟨35409220761894828977795885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23606147174596552651863923 35409220761894828977795885)
            ·
              refine ⟨13278457785710560866673457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35409220761894828977795885 13278457785710560866673457)
              ·
                refine ⟨9958843339282920650005093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278457785710560866673457 9958843339282920650005093)
                ·
                  refine ⟨1867283126115547621875955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9958843339282920650005093 1867283126115547621875955)
                  ·
                    refine ⟨2800924689173321432813933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1867283126115547621875955 2800924689173321432813933)
                    ·
                      refine ⟨1050346758439995537305225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2800924689173321432813933 1050346758439995537305225)
                      ·
                        rfl

theorem cell23_2045543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_2045543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045543 prefixEnd_2045543 := by exact prefixLift 2045543
  have htrace : WordTrace (prefixWord ++ tailWord_2045543) baseStart_2045543 baseEnd_2045543 := by
    simpa [prefixWord, tailWord_2045543, baseEnd_2045543] using wordTrace_append hprefix tailTrace_2045543
  have hstable : (prefixWord ++ tailWord_2045543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045543).length < 2 ^ (prefixWord ++ tailWord_2045543).sum := by decide
  have hdescent : baseEnd_2045543 < baseStart_2045543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045544 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 1, 2, 2]
def baseStart_2045544 : Nat := 118140960795 + 2045544 * 2 ^ 59
def prefixEnd_2045544 : Nat := 4983230072969 + 3 ^ 40 * 2045544 * 2
def baseEnd_2045544 : Nat := 1050347271920650033392721

theorem tailTrace_2045544 : CollatzResearch.WordTrace tailWord_2045544 prefixEnd_2045544 1050347271920650033392721 := by
  unfold tailWord_2045544
  simp only [CollatzResearch.WordTrace]
  refine ⟨37303559450675456973523843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49738079267567275964698457 37303559450675456973523843)
  ·
    refine ⟨55955339176013185460285765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37303559450675456973523843 55955339176013185460285765)
    ·
      refine ⟨10491626095502472273803581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55955339176013185460285765 10491626095502472273803581)
      ·
        refine ⟨3934359785813427102676343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10491626095502472273803581 3934359785813427102676343)
        ·
          refine ⟨5901539678720140654014515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3934359785813427102676343 5901539678720140654014515)
          ·
            refine ⟨8852309518080210981021773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5901539678720140654014515 8852309518080210981021773)
            ·
              refine ⟨3319616069280079117883165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8852309518080210981021773 3319616069280079117883165)
              ·
                refine ⟨1244856025980029669206187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3319616069280079117883165 1244856025980029669206187)
                ·
                  refine ⟨1867284038970044503809281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244856025980029669206187 1867284038970044503809281)
                  ·
                    refine ⟨1400463029227533377856961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867284038970044503809281 1400463029227533377856961)
                    ·
                      refine ⟨1050347271920650033392721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400463029227533377856961 1050347271920650033392721)
                      ·
                        rfl

theorem cell23_2045544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_2045544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045544 prefixEnd_2045544 := by exact prefixLift 2045544
  have htrace : WordTrace (prefixWord ++ tailWord_2045544) baseStart_2045544 baseEnd_2045544 := by
    simpa [prefixWord, tailWord_2045544, baseEnd_2045544] using wordTrace_append hprefix tailTrace_2045544
  have hstable : (prefixWord ++ tailWord_2045544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045544).length < 2 ^ (prefixWord ++ tailWord_2045544).sum := by decide
  have hdescent : baseEnd_2045544 < baseStart_2045544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045600 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2]
def baseStart_2045600 : Nat := 118140960795 + 2045600 * 2 ^ 59
def prefixEnd_2045600 : Nat := 4983230072969 + 3 ^ 40 * 2045600 * 2
def baseEnd_2045600 : Nat := 1050376026837301814292463

theorem tailTrace_2045600 : CollatzResearch.WordTrace tailWord_2045600 prefixEnd_2045600 1050376026837301814292463 := by
  unfold tailWord_2045600
  simp only [CollatzResearch.WordTrace]
  refine ⟨37304580694574017755543127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49739440926098690340724169 37304580694574017755543127)
  ·
    refine ⟨55956871041861026633314691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37304580694574017755543127 55956871041861026633314691)
    ·
      refine ⟨83935306562791539949972037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55956871041861026633314691 83935306562791539949972037)
      ·
        refine ⟨15737869980523413740619757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83935306562791539949972037 15737869980523413740619757)
        ·
          refine ⟨5901701242696280152732409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15737869980523413740619757 5901701242696280152732409)
          ·
            refine ⟨4426275932022210114549307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5901701242696280152732409 4426275932022210114549307)
            ·
              refine ⟨6639413898033315171823961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426275932022210114549307 6639413898033315171823961)
              ·
                refine ⟨4979560423524986378867971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639413898033315171823961 4979560423524986378867971)
                ·
                  refine ⟨7469340635287479568301957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4979560423524986378867971 7469340635287479568301957)
                  ·
                    refine ⟨1400501369116402419056617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7469340635287479568301957 1400501369116402419056617)
                    ·
                      refine ⟨1050376026837301814292463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400501369116402419056617 1050376026837301814292463)
                      ·
                        rfl

theorem cell23_2045600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_2045600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045600 prefixEnd_2045600 := by exact prefixLift 2045600
  have htrace : WordTrace (prefixWord ++ tailWord_2045600) baseStart_2045600 baseEnd_2045600 := by
    simpa [prefixWord, tailWord_2045600, baseEnd_2045600] using wordTrace_append hprefix tailTrace_2045600
  have hstable : (prefixWord ++ tailWord_2045600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045600).length < 2 ^ (prefixWord ++ tailWord_2045600).sum := by decide
  have hdescent : baseEnd_2045600 < baseStart_2045600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045613 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_2045613 : Nat := 118140960795 + 2045613 * 2 ^ 59
def prefixEnd_2045613 : Nat := 4983230072969 + 3 ^ 40 * 2045613 * 2
def baseEnd_2045613 : Nat := 1050382702085810263429903

theorem tailTrace_2045613 : CollatzResearch.WordTrace tailWord_2045613 prefixEnd_2045613 1050382702085810263429903 := by
  unfold tailWord_2045613
  simp only [CollatzResearch.WordTrace]
  refine ⟨74609635538100938731309493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49739757025400625820872995 74609635538100938731309493)
  ·
    refine ⟨6994653331696963006060265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74609635538100938731309493 6994653331696963006060265)
    ·
      refine ⟨5245989998772722254545199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6994653331696963006060265 5245989998772722254545199)
      ·
        refine ⟨7868984998159083381817799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245989998772722254545199 7868984998159083381817799)
        ·
          refine ⟨11803477497238625072726699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7868984998159083381817799 11803477497238625072726699)
          ·
            refine ⟨17705216245857937609090049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11803477497238625072726699 17705216245857937609090049)
            ·
              refine ⟨13278912184393453206817537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17705216245857937609090049 13278912184393453206817537)
              ·
                refine ⟨9959184138295089905113153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13278912184393453206817537 9959184138295089905113153)
                ·
                  refine ⟨7469388103721317428834865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9959184138295089905113153 7469388103721317428834865)
                  ·
                    refine ⟨5602041077790988071626149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7469388103721317428834865 5602041077790988071626149)
                    ·
                      refine ⟨1050382702085810263429903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5602041077790988071626149 1050382702085810263429903)
                      ·
                        rfl

theorem cell23_2045613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_2045613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045613 prefixEnd_2045613 := by exact prefixLift 2045613
  have htrace : WordTrace (prefixWord ++ tailWord_2045613) baseStart_2045613 baseEnd_2045613 := by
    simpa [prefixWord, tailWord_2045613, baseEnd_2045613] using wordTrace_append hprefix tailTrace_2045613
  have hstable : (prefixWord ++ tailWord_2045613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045613).length < 2 ^ (prefixWord ++ tailWord_2045613).sum := by decide
  have hdescent : baseEnd_2045613 < baseStart_2045613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045676 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_2045676 : Nat := 118140960795 + 2045676 * 2 ^ 59
def prefixEnd_2045676 : Nat := 4983230072969 + 3 ^ 40 * 2045676 * 2
def baseEnd_2045676 : Nat := 1050415051367043516942113

theorem tailTrace_2045676 : CollatzResearch.WordTrace tailWord_2045676 prefixEnd_2045676 1050415051367043516942113 := by
  unfold tailWord_2045676
  simp only [CollatzResearch.WordTrace]
  refine ⟨37305966668436350245426441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49741288891248466993901921 37305966668436350245426441)
  ·
    refine ⟨27979475001327262684069831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37305966668436350245426441 27979475001327262684069831)
    ·
      refine ⟨41969212501990894026104747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27979475001327262684069831 41969212501990894026104747)
      ·
        refine ⟨62953818752986341039157121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41969212501990894026104747 62953818752986341039157121)
        ·
          refine ⟨47215364064739755779367841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62953818752986341039157121 47215364064739755779367841)
          ·
            refine ⟨35411523048554816834525881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47215364064739755779367841 35411523048554816834525881)
            ·
              refine ⟨26558642286416112625894411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35411523048554816834525881 26558642286416112625894411)
              ·
                refine ⟨39837963429624168938841617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26558642286416112625894411 39837963429624168938841617)
                ·
                  refine ⟨29878472572218126704131213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39837963429624168938841617 29878472572218126704131213)
                  ·
                    refine ⟨11204427214581797514049205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29878472572218126704131213 11204427214581797514049205)
                    ·
                      refine ⟨1050415051367043516942113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11204427214581797514049205 1050415051367043516942113)
                      ·
                        rfl

theorem cell23_2045676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_2045676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045676 prefixEnd_2045676 := by exact prefixLift 2045676
  have htrace : WordTrace (prefixWord ++ tailWord_2045676) baseStart_2045676 baseEnd_2045676 := by
    simpa [prefixWord, tailWord_2045676, baseEnd_2045676] using wordTrace_append hprefix tailTrace_2045676
  have hstable : (prefixWord ++ tailWord_2045676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045676).length < 2 ^ (prefixWord ++ tailWord_2045676).sum := by decide
  have hdescent : baseEnd_2045676 < baseStart_2045676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045683 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 3, 4]
def baseStart_2045683 : Nat := 118140960795 + 2045683 * 2 ^ 59
def prefixEnd_2045683 : Nat := 4983230072969 + 3 ^ 40 * 2045683 * 2
def baseEnd_2045683 : Nat := 350139548577208329851527

theorem tailTrace_2045683 : CollatzResearch.WordTrace tailWord_2045683 prefixEnd_2045683 350139548577208329851527 := by
  unfold tailWord_2045683
  simp only [CollatzResearch.WordTrace]
  refine ⟨74612188647847340686357703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49741459098564893790905135 74612188647847340686357703)
  ·
    refine ⟨111918282971771011029536555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74612188647847340686357703 111918282971771011029536555)
    ·
      refine ⟨167877424457656516544304833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111918282971771011029536555 167877424457656516544304833)
      ·
        refine ⟨125908068343242387408228625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167877424457656516544304833 125908068343242387408228625)
        ·
          refine ⟨94431051257431790556171469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125908068343242387408228625 94431051257431790556171469)
          ·
            refine ⟨35411644221536921458564301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94431051257431790556171469 35411644221536921458564301)
            ·
              refine ⟨13279366583076345546961613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35411644221536921458564301 13279366583076345546961613)
              ·
                refine ⟨4979762468653629580110605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13279366583076345546961613 4979762468653629580110605)
                ·
                  refine ⟨1867410925745111092541477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4979762468653629580110605 1867410925745111092541477)
                  ·
                    refine ⟨350139548577208329851527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867410925745111092541477 350139548577208329851527)
                    ·
                      rfl

theorem cell23_2045683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4].length) (baseStart_2045683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045683 prefixEnd_2045683 := by exact prefixLift 2045683
  have htrace : WordTrace (prefixWord ++ tailWord_2045683) baseStart_2045683 baseEnd_2045683 := by
    simpa [prefixWord, tailWord_2045683, baseEnd_2045683] using wordTrace_append hprefix tailTrace_2045683
  have hstable : (prefixWord ++ tailWord_2045683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045683).length < 2 ^ (prefixWord ++ tailWord_2045683).sum := by decide
  have hdescent : baseEnd_2045683 < baseStart_2045683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045693 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_2045693 : Nat := 118140960795 + 2045693 * 2 ^ 59
def prefixEnd_2045693 : Nat := 4983230072969 + 3 ^ 40 * 2045693 * 2
def baseEnd_2045693 : Nat := 1050423780538169950429535

theorem tailTrace_2045693 : CollatzResearch.WordTrace tailWord_2045693 prefixEnd_2045693 1050423780538169950429535 := by
  unfold tailWord_2045693
  simp only [CollatzResearch.WordTrace]
  refine ⟨74612553377811112394221733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49741702251874074929481155 74612553377811112394221733)
  ·
    refine ⟨13989853758339583573916575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74612553377811112394221733 13989853758339583573916575)
    ·
      refine ⟨20984780637509375360874863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13989853758339583573916575 20984780637509375360874863)
      ·
        refine ⟨31477170956264063041312295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20984780637509375360874863 31477170956264063041312295)
        ·
          refine ⟨47215756434396094561968443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31477170956264063041312295 47215756434396094561968443)
          ·
            refine ⟨70823634651594141842952665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47215756434396094561968443 70823634651594141842952665)
            ·
              refine ⟨53117725988695606382214499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70823634651594141842952665 53117725988695606382214499)
              ·
                refine ⟨79676588983043409573321749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53117725988695606382214499 79676588983043409573321749)
                ·
                  refine ⟨3734840108580159823749457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79676588983043409573321749 3734840108580159823749457)
                  ·
                    refine ⟨2801130081435119867812093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3734840108580159823749457 2801130081435119867812093)
                    ·
                      refine ⟨1050423780538169950429535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801130081435119867812093 1050423780538169950429535)
                      ·
                        rfl

theorem cell23_2045693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_2045693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045693 prefixEnd_2045693 := by exact prefixLift 2045693
  have htrace : WordTrace (prefixWord ++ tailWord_2045693) baseStart_2045693 baseEnd_2045693 := by
    simpa [prefixWord, tailWord_2045693, baseEnd_2045693] using wordTrace_append hprefix tailTrace_2045693
  have hstable : (prefixWord ++ tailWord_2045693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045693).length < 2 ^ (prefixWord ++ tailWord_2045693).sum := by decide
  have hdescent : baseEnd_2045693 < baseStart_2045693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045700 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_2045700 : Nat := 118140960795 + 2045700 * 2 ^ 59
def prefixEnd_2045700 : Nat := 4983230072969 + 3 ^ 40 * 2045700 * 2
def baseEnd_2045700 : Nat := 350142458300917141014001

theorem tailTrace_2045700 : CollatzResearch.WordTrace tailWord_2045700 prefixEnd_2045700 350142458300917141014001 := by
  unfold tailWord_2045700
  simp only [CollatzResearch.WordTrace]
  refine ⟨37306404344392876294863277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49741872459190501726484369 37306404344392876294863277)
  ·
    refine ⟨13989901629147328610573729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37306404344392876294863277 13989901629147328610573729)
    ·
      refine ⟨10492426221860496457930297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13989901629147328610573729 10492426221860496457930297)
      ·
        refine ⟨7869319666395372343447723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492426221860496457930297 7869319666395372343447723)
        ·
          refine ⟨11803979499593058515171585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869319666395372343447723 11803979499593058515171585)
          ·
            refine ⟨8852984624694793886378689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11803979499593058515171585 8852984624694793886378689)
            ·
              refine ⟨6639738468521095414784017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8852984624694793886378689 6639738468521095414784017)
              ·
                refine ⟨4979803851390821561088013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6639738468521095414784017 4979803851390821561088013)
                ·
                  refine ⟨1867426444271558085408005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4979803851390821561088013 1867426444271558085408005)
                  ·
                    refine ⟨350142458300917141014001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867426444271558085408005 350142458300917141014001)
                    ·
                      rfl

theorem cell23_2045700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_2045700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045700 prefixEnd_2045700 := by exact prefixLift 2045700
  have htrace : WordTrace (prefixWord ++ tailWord_2045700) baseStart_2045700 baseEnd_2045700 := by
    simpa [prefixWord, tailWord_2045700, baseEnd_2045700] using wordTrace_append hprefix tailTrace_2045700
  have hstable : (prefixWord ++ tailWord_2045700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045700).length < 2 ^ (prefixWord ++ tailWord_2045700).sum := by decide
  have hdescent : baseEnd_2045700 < baseStart_2045700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045717 : List Nat := [1, 3, 2, 1, 2, 3, 3, 3, 1, 4]
def baseStart_2045717 : Nat := 118140960795 + 2045717 * 2 ^ 59
def prefixEnd_2045717 : Nat := 4983230072969 + 3 ^ 40 * 2045717 * 2
def baseEnd_2045717 : Nat := 350145368024625952176475

theorem tailTrace_2045717 : CollatzResearch.WordTrace tailWord_2045717 prefixEnd_2045717 350145368024625952176475 := by
  unfold tailWord_2045717
  simp only [CollatzResearch.WordTrace]
  refine ⟨74613428729724164493095405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49742285819816109662063603 74613428729724164493095405)
  ·
    refine ⟨27980035773646561684910777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74613428729724164493095405 27980035773646561684910777)
    ·
      refine ⟨20985026830234921263683083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27980035773646561684910777 20985026830234921263683083)
      ·
        refine ⟨31477540245352381895524625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20985026830234921263683083 31477540245352381895524625)
        ·
          refine ⟨23608155184014286421643469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31477540245352381895524625 23608155184014286421643469)
          ·
            refine ⟨8853058194005357408116301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23608155184014286421643469 8853058194005357408116301)
            ·
              refine ⟨3319896822752009028043613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8853058194005357408116301 3319896822752009028043613)
              ·
                refine ⟨1244961308532003385516355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3319896822752009028043613 1244961308532003385516355)
                ·
                  refine ⟨1867441962798005078274533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1244961308532003385516355 1867441962798005078274533)
                  ·
                    refine ⟨350145368024625952176475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867441962798005078274533 350145368024625952176475)
                    ·
                      rfl

theorem cell23_2045717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_2045717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045717 prefixEnd_2045717 := by exact prefixLift 2045717
  have htrace : WordTrace (prefixWord ++ tailWord_2045717) baseStart_2045717 baseEnd_2045717 := by
    simpa [prefixWord, tailWord_2045717, baseEnd_2045717] using wordTrace_append hprefix tailTrace_2045717
  have hstable : (prefixWord ++ tailWord_2045717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045717).length < 2 ^ (prefixWord ++ tailWord_2045717).sum := by decide
  have hdescent : baseEnd_2045717 < baseStart_2045717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045747 : List Nat := [1, 1, 1, 2, 7, 2, 2, 1, 6]
def baseStart_2045747 : Nat := 118140960795 + 2045747 * 2 ^ 59
def prefixEnd_2045747 : Nat := 4983230072969 + 3 ^ 40 * 2045747 * 2
def baseEnd_2045747 : Nat := 116716834277056971017143

theorem tailTrace_2045747 : CollatzResearch.WordTrace tailWord_2045747 prefixEnd_2045747 116716834277056971017143 := by
  unfold tailWord_2045747
  simp only [CollatzResearch.WordTrace]
  refine ⟨74614522919615479616687495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49743015279743653077791663 74614522919615479616687495)
  ·
    refine ⟨111921784379423219425031243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74614522919615479616687495 111921784379423219425031243)
    ·
      refine ⟨167882676569134829137546865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111921784379423219425031243 167882676569134829137546865)
      ·
        refine ⟨125912007426851121853160149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167882676569134829137546865 125912007426851121853160149)
        ·
          refine ⟨2951062674066823168433441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125912007426851121853160149 2951062674066823168433441)
          ·
            refine ⟨2213297005550117376325081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951062674066823168433441 2213297005550117376325081)
            ·
              refine ⟨1659972754162588032243811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213297005550117376325081 1659972754162588032243811)
              ·
                refine ⟨2489959131243882048365717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659972754162588032243811 2489959131243882048365717)
                ·
                  refine ⟨116716834277056971017143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2489959131243882048365717 116716834277056971017143)
                  ·
                    rfl

theorem cell23_2045747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 1, 6].length) (baseStart_2045747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045747 prefixEnd_2045747 := by exact prefixLift 2045747
  have htrace : WordTrace (prefixWord ++ tailWord_2045747) baseStart_2045747 baseEnd_2045747 := by
    simpa [prefixWord, tailWord_2045747, baseEnd_2045747] using wordTrace_append hprefix tailTrace_2045747
  have hstable : (prefixWord ++ tailWord_2045747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045747).length < 2 ^ (prefixWord ++ tailWord_2045747).sum := by decide
  have hdescent : baseEnd_2045747 < baseStart_2045747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045777 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 1, 5]
def baseStart_2045777 : Nat := 118140960795 + 2045777 * 2 ^ 59
def prefixEnd_2045777 : Nat := 4983230072969 + 3 ^ 40 * 2045777 * 2
def baseEnd_2045777 : Nat := 350155637637715873926383

theorem tailTrace_2045777 : CollatzResearch.WordTrace tailWord_2045777 prefixEnd_2045777 350155637637715873926383 := by
  unfold tailWord_2045777
  simp only [CollatzResearch.WordTrace]
  refine ⟨74615617109506794740279585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49743744739671196493519723 74615617109506794740279585)
  ·
    refine ⟨55961712832130096055209689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74615617109506794740279585 55961712832130096055209689)
    ·
      refine ⟨41971284624097572041407267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55961712832130096055209689 41971284624097572041407267)
      ·
        refine ⟨62956926936146358062110901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41971284624097572041407267 62956926936146358062110901)
        ·
          refine ⟨5902211900263721068322897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62956926936146358062110901 5902211900263721068322897)
          ·
            refine ⟨4426658925197790801242173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902211900263721068322897 4426658925197790801242173)
            ·
              refine ⟨1659997096949171550465815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4426658925197790801242173 1659997096949171550465815)
              ·
                refine ⟨2489995645423757325698723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1659997096949171550465815 2489995645423757325698723)
                ·
                  refine ⟨3734993468135635988548085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2489995645423757325698723 3734993468135635988548085)
                  ·
                    refine ⟨350155637637715873926383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3734993468135635988548085 350155637637715873926383)
                    ·
                      rfl

theorem cell23_2045777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 1, 5].length) (baseStart_2045777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045777 prefixEnd_2045777 := by exact prefixLift 2045777
  have htrace : WordTrace (prefixWord ++ tailWord_2045777) baseStart_2045777 baseEnd_2045777 := by
    simpa [prefixWord, tailWord_2045777, baseEnd_2045777] using wordTrace_append hprefix tailTrace_2045777
  have hstable : (prefixWord ++ tailWord_2045777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045777).length < 2 ^ (prefixWord ++ tailWord_2045777).sum := by decide
  have hdescent : baseEnd_2045777 < baseStart_2045777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045791 : List Nat := [1, 1, 2, 3, 1, 6, 2, 2, 1, 1, 3]
def baseStart_2045791 : Nat := 118140960795 + 2045791 * 2 ^ 59
def prefixEnd_2045791 : Nat := 4983230072969 + 3 ^ 40 * 2045791 * 2
def baseEnd_2045791 : Nat := 1050474101642310567004085

theorem tailTrace_2045791 : CollatzResearch.WordTrace tailWord_2045791 prefixEnd_2045791 1050474101642310567004085 := by
  unfold tailWord_2045791
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616127731456075131289227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49744085154304050087526151 74616127731456075131289227)
  ·
    refine ⟨111924191597184112696933841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74616127731456075131289227 111924191597184112696933841)
    ·
      refine ⟨83943143697888084522700381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111924191597184112696933841 83943143697888084522700381)
      ·
        refine ⟨31478678886708031696012643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83943143697888084522700381 31478678886708031696012643)
        ·
          refine ⟨47218018330062047544018965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31478678886708031696012643 47218018330062047544018965)
          ·
            refine ⟨2213344609221658478625889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47218018330062047544018965 2213344609221658478625889)
            ·
              refine ⟨1660008456916243858969417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213344609221658478625889 1660008456916243858969417)
              ·
                refine ⟨1245006342687182894227063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660008456916243858969417 1245006342687182894227063)
                ·
                  refine ⟨1867509514030774341340595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245006342687182894227063 1867509514030774341340595)
                  ·
                    refine ⟨2801264271046161512010893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1867509514030774341340595 2801264271046161512010893)
                    ·
                      refine ⟨1050474101642310567004085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801264271046161512010893 1050474101642310567004085)
                      ·
                        rfl

theorem cell23_2045791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 2, 1, 1, 3].length) (baseStart_2045791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045791 prefixEnd_2045791 := by exact prefixLift 2045791
  have htrace : WordTrace (prefixWord ++ tailWord_2045791) baseStart_2045791 baseEnd_2045791 := by
    simpa [prefixWord, tailWord_2045791, baseEnd_2045791] using wordTrace_append hprefix tailTrace_2045791
  have hstable : (prefixWord ++ tailWord_2045791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045791).length < 2 ^ (prefixWord ++ tailWord_2045791).sum := by decide
  have hdescent : baseEnd_2045791 < baseStart_2045791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045793 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_2045793 : Nat := 118140960795 + 2045793 * 2 ^ 59
def prefixEnd_2045793 : Nat := 4983230072969 + 3 ^ 40 * 2045793 * 2
def baseEnd_2045793 : Nat := 1050475128603619559179075

theorem tailTrace_2045793 : CollatzResearch.WordTrace tailWord_2045793 prefixEnd_2045793 1050475128603619559179075 := by
  unfold tailWord_2045793
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616200677448829472862033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49744133784965886315241355 74616200677448829472862033)
  ·
    refine ⟨55962150508086622104646525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74616200677448829472862033 55962150508086622104646525)
    ·
      refine ⟨20985806440532483289242447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55962150508086622104646525 20985806440532483289242447)
      ·
        refine ⟨31478709660798724933863671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20985806440532483289242447 31478709660798724933863671)
        ·
          refine ⟨47218064491198087400795507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31478709660798724933863671 47218064491198087400795507)
          ·
            refine ⟨70827096736797131101193261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47218064491198087400795507 70827096736797131101193261)
            ·
              refine ⟨26560161276298924162947473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70827096736797131101193261 26560161276298924162947473)
              ·
                refine ⟨19920120957224193122210605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26560161276298924162947473 19920120957224193122210605)
                ·
                  refine ⟨7470045358959072420828977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19920120957224193122210605 7470045358959072420828977)
                  ·
                    refine ⟨5602534019219304315621733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7470045358959072420828977 5602534019219304315621733)
                    ·
                      refine ⟨1050475128603619559179075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5602534019219304315621733 1050475128603619559179075)
                      ·
                        rfl

theorem cell23_2045793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_2045793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045793 prefixEnd_2045793 := by exact prefixLift 2045793
  have htrace : WordTrace (prefixWord ++ tailWord_2045793) baseStart_2045793 baseEnd_2045793 := by
    simpa [prefixWord, tailWord_2045793, baseEnd_2045793] using wordTrace_append hprefix tailTrace_2045793
  have hstable : (prefixWord ++ tailWord_2045793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045793).length < 2 ^ (prefixWord ++ tailWord_2045793).sum := by decide
  have hdescent : baseEnd_2045793 < baseStart_2045793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045797 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 3, 2, 2]
def baseStart_2045797 : Nat := 118140960795 + 2045797 * 2 ^ 59
def prefixEnd_2045797 : Nat := 4983230072969 + 3 ^ 40 * 2045797 * 2
def baseEnd_2045797 : Nat := 1050477182526237543529057

theorem tailTrace_2045797 : CollatzResearch.WordTrace tailWord_2045797 prefixEnd_2045797 1050477182526237543529057 := by
  unfold tailWord_2045797
  simp only [CollatzResearch.WordTrace]
  refine ⟨74616346569434338156007645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49744231046289558770671763 74616346569434338156007645)
  ·
    refine ⟨27981129963537876808502867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74616346569434338156007645 27981129963537876808502867)
    ·
      refine ⟨41971694945306815212754301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27981129963537876808502867 41971694945306815212754301)
      ·
        refine ⟨15739385604490055704782863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41971694945306815212754301 15739385604490055704782863)
        ·
          refine ⟨23609078406735083557174295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15739385604490055704782863 23609078406735083557174295)
          ·
            refine ⟨35413617610102625335761443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23609078406735083557174295 35413617610102625335761443)
            ·
              refine ⟨53120426415153938003642165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35413617610102625335761443 53120426415153938003642165)
              ·
                refine ⟨4980039976420681687841453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53120426415153938003642165 4980039976420681687841453)
                ·
                  refine ⟨1867514991157755632940545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4980039976420681687841453 1867514991157755632940545)
                  ·
                    refine ⟨1400636243368316724705409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867514991157755632940545 1400636243368316724705409)
                    ·
                      refine ⟨1050477182526237543529057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400636243368316724705409 1050477182526237543529057)
                      ·
                        rfl

theorem cell23_2045797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_2045797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045797 prefixEnd_2045797 := by exact prefixLift 2045797
  have htrace : WordTrace (prefixWord ++ tailWord_2045797) baseStart_2045797 baseEnd_2045797 := by
    simpa [prefixWord, tailWord_2045797, baseEnd_2045797] using wordTrace_append hprefix tailTrace_2045797
  have hstable : (prefixWord ++ tailWord_2045797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045797).length < 2 ^ (prefixWord ++ tailWord_2045797).sum := by decide
  have hdescent : baseEnd_2045797 < baseStart_2045797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045800 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_2045800 : Nat := 118140960795 + 2045800 * 2 ^ 59
def prefixEnd_2045800 : Nat := 4983230072969 + 3 ^ 40 * 2045800 * 2
def baseEnd_2045800 : Nat := 1050478722968201031791543

theorem tailTrace_2045800 : CollatzResearch.WordTrace tailWord_2045800 prefixEnd_2045800 1050478722968201031791543 := by
  unfold tailWord_2045800
  simp only [CollatzResearch.WordTrace]
  refine ⟨37308227994211734834183427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49744303992282313112244569 37308227994211734834183427)
  ·
    refine ⟨55962341991317602251275141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37308227994211734834183427 55962341991317602251275141)
    ·
      refine ⟨10492939123372050422114089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55962341991317602251275141 10492939123372050422114089)
      ·
        refine ⟨7869704342529037816585567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10492939123372050422114089 7869704342529037816585567)
        ·
          refine ⟨11804556513793556724878351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7869704342529037816585567 11804556513793556724878351)
          ·
            refine ⟨17706834770690335087317527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11804556513793556724878351 17706834770690335087317527)
            ·
              refine ⟨26560252156035502630976291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17706834770690335087317527 26560252156035502630976291)
              ·
                refine ⟨39840378234053253946464437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26560252156035502630976291 39840378234053253946464437)
                ·
                  refine ⟨3735035459442492557481041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39840378234053253946464437 3735035459442492557481041)
                  ·
                    refine ⟨2801276594581869418110781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735035459442492557481041 2801276594581869418110781)
                    ·
                      refine ⟨1050478722968201031791543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801276594581869418110781 1050478722968201031791543)
                      ·
                        rfl

theorem cell23_2045800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_2045800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045800 prefixEnd_2045800 := by exact prefixLift 2045800
  have htrace : WordTrace (prefixWord ++ tailWord_2045800) baseStart_2045800 baseEnd_2045800 := by
    simpa [prefixWord, tailWord_2045800, baseEnd_2045800] using wordTrace_append hprefix tailTrace_2045800
  have hstable : (prefixWord ++ tailWord_2045800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045800).length < 2 ^ (prefixWord ++ tailWord_2045800).sum := by decide
  have hdescent : baseEnd_2045800 < baseStart_2045800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045831 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_2045831 : Nat := 118140960795 + 2045831 * 2 ^ 59
def prefixEnd_2045831 : Nat := 4983230072969 + 3 ^ 40 * 2045831 * 2
def baseEnd_2045831 : Nat := 1050494640868490410503901

theorem tailTrace_2045831 : CollatzResearch.WordTrace tailWord_2045831 prefixEnd_2045831 1050494640868490410503901 := by
  unfold tailWord_2045831
  simp only [CollatzResearch.WordTrace]
  refine ⟨74617586651311161962745347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49745057767540774641830231 74617586651311161962745347)
  ·
    refine ⟨111926379976966742944118021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74617586651311161962745347 111926379976966742944118021)
    ·
      refine ⟨20986196245681264302022129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111926379976966742944118021 20986196245681264302022129)
      ·
        refine ⟨15739647184260948226516597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20986196245681264302022129 15739647184260948226516597)
        ·
          refine ⟨1475591923524463896235931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15739647184260948226516597 1475591923524463896235931)
          ·
            refine ⟨2213387885286695844353897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475591923524463896235931 2213387885286695844353897)
            ·
              refine ⟨1660040913965021883265423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213387885286695844353897 1660040913965021883265423)
              ·
                refine ⟨2490061370947532824898135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660040913965021883265423 2490061370947532824898135)
                ·
                  refine ⟨3735092056421299237347203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490061370947532824898135 3735092056421299237347203)
                  ·
                    refine ⟨5602638084631948856020805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3735092056421299237347203 5602638084631948856020805)
                    ·
                      refine ⟨1050494640868490410503901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5602638084631948856020805 1050494640868490410503901)
                      ·
                        rfl

theorem cell23_2045831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_2045831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045831 prefixEnd_2045831 := by exact prefixLift 2045831
  have htrace : WordTrace (prefixWord ++ tailWord_2045831) baseStart_2045831 baseEnd_2045831 := by
    simpa [prefixWord, tailWord_2045831, baseEnd_2045831] using wordTrace_append hprefix tailTrace_2045831
  have hstable : (prefixWord ++ tailWord_2045831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045831).length < 2 ^ (prefixWord ++ tailWord_2045831).sum := by decide
  have hdescent : baseEnd_2045831 < baseStart_2045831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045834 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_2045834 : Nat := 118140960795 + 2045834 * 2 ^ 59
def prefixEnd_2045834 : Nat := 4983230072969 + 3 ^ 40 * 2045834 * 2
def baseEnd_2045834 : Nat := 1050496181310453898766387

theorem tailTrace_2045834 : CollatzResearch.WordTrace tailWord_2045834 prefixEnd_2045834 1050496181310453898766387 := by
  unfold tailWord_2045834
  simp only [CollatzResearch.WordTrace]
  refine ⟨18654424017575073368776139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49745130713533528983403037 18654424017575073368776139)
  ·
    refine ⟨27981636026362610053164209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18654424017575073368776139 27981636026362610053164209)
    ·
      refine ⟨20986227019771957539873157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27981636026362610053164209 20986227019771957539873157)
      ·
        refine ⟨3934917566207242038726217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20986227019771957539873157 3934917566207242038726217)
        ·
          refine ⟨2951188174655431529044663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3934917566207242038726217 2951188174655431529044663)
          ·
            refine ⟨4426782261983147293566995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951188174655431529044663 4426782261983147293566995)
            ·
              refine ⟨6640173392974720940350493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426782261983147293566995 6640173392974720940350493)
              ·
                refine ⟨2490065022365520352631435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6640173392974720940350493 2490065022365520352631435)
                ·
                  refine ⟨3735097533548280528947153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490065022365520352631435 3735097533548280528947153)
                  ·
                    refine ⟨2801323150161210396710365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735097533548280528947153 2801323150161210396710365)
                    ·
                      refine ⟨1050496181310453898766387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801323150161210396710365 1050496181310453898766387)
                      ·
                        rfl

theorem cell23_2045834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_2045834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045834 prefixEnd_2045834 := by exact prefixLift 2045834
  have htrace : WordTrace (prefixWord ++ tailWord_2045834) baseStart_2045834 baseEnd_2045834 := by
    simpa [prefixWord, tailWord_2045834, baseEnd_2045834] using wordTrace_append hprefix tailTrace_2045834
  have hstable : (prefixWord ++ tailWord_2045834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045834).length < 2 ^ (prefixWord ++ tailWord_2045834).sum := by decide
  have hdescent : baseEnd_2045834 < baseStart_2045834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045847 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_2045847 : Nat := 118140960795 + 2045847 * 2 ^ 59
def prefixEnd_2045847 : Nat := 4983230072969 + 3 ^ 40 * 2045847 * 2
def baseEnd_2045847 : Nat := 1050502856558962347903827

theorem tailTrace_2045847 : CollatzResearch.WordTrace tailWord_2045847 prefixEnd_2045847 1050502856558962347903827 := by
  unfold tailWord_2045847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74618170219253196695327795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49745446812835464463551863 74618170219253196695327795)
  ·
    refine ⟨111927255328879795042991693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74618170219253196695327795 111927255328879795042991693)
    ·
      refine ⟨41972720748329923141121885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111927255328879795042991693 41972720748329923141121885)
      ·
        refine ⟨15739770280623721177920707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41972720748329923141121885 15739770280623721177920707)
        ·
          refine ⟨23609655420935581766881061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15739770280623721177920707 23609655420935581766881061)
          ·
            refine ⟨4426810391425421581290199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23609655420935581766881061 4426810391425421581290199)
            ·
              refine ⟨6640215587138132371935299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4426810391425421581290199 6640215587138132371935299)
              ·
                refine ⟨9960323380707198557902949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640215587138132371935299 9960323380707198557902949)
                ·
                  refine ⟨1867560633882599729606803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9960323380707198557902949 1867560633882599729606803)
                  ·
                    refine ⟨2801340950823899594410205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1867560633882599729606803 2801340950823899594410205)
                    ·
                      refine ⟨1050502856558962347903827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801340950823899594410205 1050502856558962347903827)
                      ·
                        rfl

theorem cell23_2045847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_2045847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045847 prefixEnd_2045847 := by exact prefixLift 2045847
  have htrace : WordTrace (prefixWord ++ tailWord_2045847) baseStart_2045847 baseEnd_2045847 := by
    simpa [prefixWord, tailWord_2045847, baseEnd_2045847] using wordTrace_append hprefix tailTrace_2045847
  have hstable : (prefixWord ++ tailWord_2045847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045847).length < 2 ^ (prefixWord ++ tailWord_2045847).sum := by decide
  have hdescent : baseEnd_2045847 < baseStart_2045847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045883 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_2045883 : Nat := 118140960795 + 2045883 * 2 ^ 59
def prefixEnd_2045883 : Nat := 4983230072969 + 3 ^ 40 * 2045883 * 2
def baseEnd_2045883 : Nat := 1050521341862524207053661

theorem tailTrace_2045883 : CollatzResearch.WordTrace tailWord_2045883 prefixEnd_2045883 1050521341862524207053661 := by
  unfold tailWord_2045883
  simp only [CollatzResearch.WordTrace]
  refine ⟨74619483247122774843638303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49746322164748516562425535 74619483247122774843638303)
  ·
    refine ⟨111929224870684162265457455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74619483247122774843638303 111929224870684162265457455)
    ·
      refine ⟨167893837306026243398186183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111929224870684162265457455 167893837306026243398186183)
      ·
        refine ⟨251840755959039365097279275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167893837306026243398186183 251840755959039365097279275)
        ·
          refine ⟨377761133938559047645918913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251840755959039365097279275 377761133938559047645918913)
          ·
            refine ⟨283320850453919285734439185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377761133938559047645918913 283320850453919285734439185)
            ·
              refine ⟨212490637840439464300829389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283320850453919285734439185 212490637840439464300829389)
              ·
                refine ⟨79683989190164799112811021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212490637840439464300829389 79683989190164799112811021)
                ·
                  refine ⟨29881495946311799667304133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79683989190164799112811021 29881495946311799667304133)
                  ·
                    refine ⟨5602780489933462437619525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29881495946311799667304133 5602780489933462437619525)
                    ·
                      refine ⟨1050521341862524207053661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5602780489933462437619525 1050521341862524207053661)
                      ·
                        rfl

theorem cell23_2045883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_2045883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045883 prefixEnd_2045883 := by exact prefixLift 2045883
  have htrace : WordTrace (prefixWord ++ tailWord_2045883) baseStart_2045883 baseEnd_2045883 := by
    simpa [prefixWord, tailWord_2045883, baseEnd_2045883] using wordTrace_append hprefix tailTrace_2045883
  have hstable : (prefixWord ++ tailWord_2045883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045883).length < 2 ^ (prefixWord ++ tailWord_2045883).sum := by decide
  have hdescent : baseEnd_2045883 < baseStart_2045883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045887 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 6, 2, 2]
def baseStart_2045887 : Nat := 118140960795 + 2045887 * 2 ^ 59
def prefixEnd_2045887 : Nat := 4983230072969 + 3 ^ 40 * 2045887 * 2
def baseEnd_2045887 : Nat := 1050523395785142191403643

theorem tailTrace_2045887 : CollatzResearch.WordTrace tailWord_2045887 prefixEnd_2045887 1050523395785142191403643 := by
  unfold tailWord_2045887
  simp only [CollatzResearch.WordTrace]
  refine ⟨74619629139108283526783915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49746419426072189017855943 74619629139108283526783915)
  ·
    refine ⟨111929443708662425290175873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74619629139108283526783915 111929443708662425290175873)
    ·
      refine ⟨83947082781496818967631905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111929443708662425290175873 83947082781496818967631905)
      ·
        refine ⟨62960312086122614225723929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83947082781496818967631905 62960312086122614225723929)
        ·
          refine ⟨47220234064591960669292947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62960312086122614225723929 47220234064591960669292947)
          ·
            refine ⟨70830351096887941003939421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47220234064591960669292947 70830351096887941003939421)
            ·
              refine ⟨26561381661332977876477283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70830351096887941003939421 26561381661332977876477283)
              ·
                refine ⟨39842072491999466814715925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26561381661332977876477283 39842072491999466814715925)
                ·
                  refine ⟨1867597148062475006939809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39842072491999466814715925 1867597148062475006939809)
                  ·
                    refine ⟨1400697861046856255204857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867597148062475006939809 1400697861046856255204857)
                    ·
                      refine ⟨1050523395785142191403643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400697861046856255204857 1050523395785142191403643)
                      ·
                        rfl

theorem cell23_2045887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 2, 2].length) (baseStart_2045887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045887 prefixEnd_2045887 := by exact prefixLift 2045887
  have htrace : WordTrace (prefixWord ++ tailWord_2045887) baseStart_2045887 baseEnd_2045887 := by
    simpa [prefixWord, tailWord_2045887, baseEnd_2045887] using wordTrace_append hprefix tailTrace_2045887
  have hstable : (prefixWord ++ tailWord_2045887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045887).length < 2 ^ (prefixWord ++ tailWord_2045887).sum := by decide
  have hdescent : baseEnd_2045887 < baseStart_2045887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045903 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_2045903 : Nat := 118140960795 + 2045903 * 2 ^ 59
def prefixEnd_2045903 : Nat := 4983230072969 + 3 ^ 40 * 2045903 * 2
def baseEnd_2045903 : Nat := 1050531611475614128803569

theorem tailTrace_2045903 : CollatzResearch.WordTrace tailWord_2045903 prefixEnd_2045903 1050531611475614128803569 := by
  unfold tailWord_2045903
  simp only [CollatzResearch.WordTrace]
  refine ⟨74620212707050318259366363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49746808471366878839577575 74620212707050318259366363)
  ·
    refine ⟨111930319060575477389049545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74620212707050318259366363 111930319060575477389049545)
    ·
      refine ⟨83947739295431608041787159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111930319060575477389049545 83947739295431608041787159)
      ·
        refine ⟨125921608943147412062680739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83947739295431608041787159 125921608943147412062680739)
        ·
          refine ⟨188882413414721118094021109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125921608943147412062680739 188882413414721118094021109)
          ·
            refine ⟨17707726257630104821314479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188882413414721118094021109 17707726257630104821314479)
            ·
              refine ⟨26561589386445157231971719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17707726257630104821314479 26561589386445157231971719)
              ·
                refine ⟨39842384079667735847957579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26561589386445157231971719 39842384079667735847957579)
                ·
                  refine ⟨59763576119501603771936369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39842384079667735847957579 59763576119501603771936369)
                  ·
                    refine ⟨44822682089626202828952277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59763576119501603771936369 44822682089626202828952277)
                    ·
                      refine ⟨1050531611475614128803569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44822682089626202828952277 1050531611475614128803569)
                      ·
                        rfl

theorem cell23_2045903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_2045903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045903 prefixEnd_2045903 := by exact prefixLift 2045903
  have htrace : WordTrace (prefixWord ++ tailWord_2045903) baseStart_2045903 baseEnd_2045903 := by
    simpa [prefixWord, tailWord_2045903, baseEnd_2045903] using wordTrace_append hprefix tailTrace_2045903
  have hstable : (prefixWord ++ tailWord_2045903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045903).length < 2 ^ (prefixWord ++ tailWord_2045903).sum := by decide
  have hdescent : baseEnd_2045903 < baseStart_2045903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045920 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_2045920 : Nat := 118140960795 + 2045920 * 2 ^ 59
def prefixEnd_2045920 : Nat := 4983230072969 + 3 ^ 40 * 2045920 * 2
def baseEnd_2045920 : Nat := 1050540340646740562290991

theorem tailTrace_2045920 : CollatzResearch.WordTrace tailWord_2045920 prefixEnd_2045920 1050540340646740562290991 := by
  unfold tailWord_2045920
  simp only [CollatzResearch.WordTrace]
  refine ⟨37310416373994365081367607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49747221831992486775156809 37310416373994365081367607)
  ·
    refine ⟨55965624560991547622051411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37310416373994365081367607 55965624560991547622051411)
    ·
      refine ⟨83948436841487321433077117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55965624560991547622051411 83948436841487321433077117)
      ·
        refine ⟨31480663815557745537403919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83948436841487321433077117 31480663815557745537403919)
        ·
          refine ⟨47220995723336618306105879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31480663815557745537403919 47220995723336618306105879)
          ·
            refine ⟨70831493585004927459158819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47220995723336618306105879 70831493585004927459158819)
            ·
              refine ⟨106247240377507391188738229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70831493585004927459158819 106247240377507391188738229)
              ·
                refine ⟨9960678785391317923944209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106247240377507391188738229 9960678785391317923944209)
                ·
                  refine ⟨7470509089043488442958157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9960678785391317923944209 7470509089043488442958157)
                  ·
                    refine ⟨2801440908391308166109309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7470509089043488442958157 2801440908391308166109309)
                    ·
                      refine ⟨1050540340646740562290991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801440908391308166109309 1050540340646740562290991)
                      ·
                        rfl

theorem cell23_2045920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_2045920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045920 prefixEnd_2045920 := by exact prefixLift 2045920
  have htrace : WordTrace (prefixWord ++ tailWord_2045920) baseStart_2045920 baseEnd_2045920 := by
    simpa [prefixWord, tailWord_2045920, baseEnd_2045920] using wordTrace_append hprefix tailTrace_2045920
  have hstable : (prefixWord ++ tailWord_2045920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045920).length < 2 ^ (prefixWord ++ tailWord_2045920).sum := by decide
  have hdescent : baseEnd_2045920 < baseStart_2045920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045921 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 2, 2, 2]
def baseStart_2045921 : Nat := 118140960795 + 2045921 * 2 ^ 59
def prefixEnd_2045921 : Nat := 4983230072969 + 3 ^ 40 * 2045921 * 2
def baseEnd_2045921 : Nat := 1050540854127395058378487

theorem tailTrace_2045921 : CollatzResearch.WordTrace tailWord_2045921 prefixEnd_2045921 1050540854127395058378487 := by
  unfold tailWord_2045921
  simp only [CollatzResearch.WordTrace]
  refine ⟨74620869220985107333521617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49747246147323404889014411 74620869220985107333521617)
  ·
    refine ⟨55965651915738830500141213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74620869220985107333521617 55965651915738830500141213)
    ·
      refine ⟨20987119468402061437552955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55965651915738830500141213 20987119468402061437552955)
      ·
        refine ⟨31480679202603092156329433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20987119468402061437552955 31480679202603092156329433)
        ·
          refine ⟨23610509401952319117247075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31480679202603092156329433 23610509401952319117247075)
          ·
            refine ⟨35415764102928478675870613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23610509401952319117247075 35415764102928478675870613)
            ·
              refine ⟨1660113942324772437931435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35415764102928478675870613 1660113942324772437931435)
              ·
                refine ⟨2490170913487158656897153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660113942324772437931435 2490170913487158656897153)
                ·
                  refine ⟨1867628185115368992672865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490170913487158656897153 1867628185115368992672865)
                  ·
                    refine ⟨1400721138836526744504649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867628185115368992672865 1400721138836526744504649)
                    ·
                      refine ⟨1050540854127395058378487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400721138836526744504649 1050540854127395058378487)
                      ·
                        rfl

theorem cell23_2045921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_2045921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045921 prefixEnd_2045921 := by exact prefixLift 2045921
  have htrace : WordTrace (prefixWord ++ tailWord_2045921) baseStart_2045921 baseEnd_2045921 := by
    simpa [prefixWord, tailWord_2045921, baseEnd_2045921] using wordTrace_append hprefix tailTrace_2045921
  have hstable : (prefixWord ++ tailWord_2045921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045921).length < 2 ^ (prefixWord ++ tailWord_2045921).sum := by decide
  have hdescent : baseEnd_2045921 < baseStart_2045921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045987 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 3, 4]
def baseStart_2045987 : Nat := 118140960795 + 2045987 * 2 ^ 59
def prefixEnd_2045987 : Nat := 4983230072969 + 3 ^ 40 * 2045987 * 2
def baseEnd_2045987 : Nat := 350191581283530600051061

theorem tailTrace_2045987 : CollatzResearch.WordTrace tailWord_2045987 prefixEnd_2045987 350191581283530600051061 := by
  unfold tailWord_2045987
  simp only [CollatzResearch.WordTrace]
  refine ⟨74623276438746000605424215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49748850959164000403616143 74623276438746000605424215)
  ·
    refine ⟨111934914658119000908136323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74623276438746000605424215 111934914658119000908136323)
    ·
      refine ⟨167902371987178501362204485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111934914658119000908136323 167902371987178501362204485)
      ·
        refine ⟨31481694747595969005413341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167902371987178501362204485 31481694747595969005413341)
        ·
          refine ⟨11805635530348488377030003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31481694747595969005413341 11805635530348488377030003)
          ·
            refine ⟨17708453295522732565545005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11805635530348488377030003 17708453295522732565545005)
            ·
              refine ⟨6640669985821024712079377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17708453295522732565545005 6640669985821024712079377)
              ·
                refine ⟨4980502489365768534059533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640669985821024712079377 4980502489365768534059533)
                ·
                  refine ⟨1867688433512163200272325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4980502489365768534059533 1867688433512163200272325)
                  ·
                    refine ⟨350191581283530600051061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867688433512163200272325 350191581283530600051061)
                    ·
                      rfl

theorem cell23_2045987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 4].length) (baseStart_2045987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045987 prefixEnd_2045987 := by exact prefixLift 2045987
  have htrace : WordTrace (prefixWord ++ tailWord_2045987) baseStart_2045987 baseEnd_2045987 := by
    simpa [prefixWord, tailWord_2045987, baseEnd_2045987] using wordTrace_append hprefix tailTrace_2045987
  have hstable : (prefixWord ++ tailWord_2045987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045987).length < 2 ^ (prefixWord ++ tailWord_2045987).sum := by decide
  have hdescent : baseEnd_2045987 < baseStart_2045987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045991 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2045991 : Nat := 118140960795 + 2045991 * 2 ^ 59
def prefixEnd_2045991 : Nat := 4983230072969 + 3 ^ 40 * 2045991 * 2
def baseEnd_2045991 : Nat := 350192265924403261501055

theorem tailTrace_2045991 : CollatzResearch.WordTrace tailWord_2045991 prefixEnd_2045991 350192265924403261501055 := by
  unfold tailWord_2045991
  simp only [CollatzResearch.WordTrace]
  refine ⟨74623422330731509288569827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49748948220487672859046551 74623422330731509288569827)
  ·
    refine ⟨111935133496097263932854741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74623422330731509288569827 111935133496097263932854741)
    ·
      refine ⟨2623479691314779623426283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 111935133496097263932854741 2623479691314779623426283)
      ·
        refine ⟨3935219536972169435139425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2623479691314779623426283 3935219536972169435139425)
        ·
          refine ⟨2951414652729127076354569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3935219536972169435139425 2951414652729127076354569)
          ·
            refine ⟨2213560989546845307265927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951414652729127076354569 2213560989546845307265927)
            ·
              refine ⟨3320341484320267960898891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213560989546845307265927 3320341484320267960898891)
              ·
                refine ⟨4980512226480401941348337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320341484320267960898891 4980512226480401941348337)
                ·
                  refine ⟨3735384169860301456011253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4980512226480401941348337 3735384169860301456011253)
                  ·
                    refine ⟨350192265924403261501055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3735384169860301456011253 350192265924403261501055)
                    ·
                      rfl

theorem cell23_2045991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2045991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045991 prefixEnd_2045991 := by exact prefixLift 2045991
  have htrace : WordTrace (prefixWord ++ tailWord_2045991) baseStart_2045991 baseEnd_2045991 := by
    simpa [prefixWord, tailWord_2045991, baseEnd_2045991] using wordTrace_append hprefix tailTrace_2045991
  have hstable : (prefixWord ++ tailWord_2045991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045991).length < 2 ^ (prefixWord ++ tailWord_2045991).sum := by decide
  have hdescent : baseEnd_2045991 < baseStart_2045991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2045994 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_2045994 : Nat := 118140960795 + 2045994 * 2 ^ 59
def prefixEnd_2045994 : Nat := 4983230072969 + 3 ^ 40 * 2045994 * 2
def baseEnd_2045994 : Nat := 1050578338215173272765651

theorem tailTrace_2045994 : CollatzResearch.WordTrace tailWord_2045994 prefixEnd_2045994 1050578338215173272765651 := by
  unfold tailWord_2045994
  simp only [CollatzResearch.WordTrace]
  refine ⟨18655882937430160200232259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49749021166480427200619357 18655882937430160200232259)
  ·
    refine ⟨27983824406145240300348389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18655882937430160200232259 27983824406145240300348389)
    ·
      refine ⟨5246967076152232556315323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27983824406145240300348389 5246967076152232556315323)
      ·
        refine ⟨7870450614228348834472985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5246967076152232556315323 7870450614228348834472985)
        ·
          refine ⟨5902837960671261625854739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7870450614228348834472985 5902837960671261625854739)
          ·
            refine ⟨8854256941006892438782109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5902837960671261625854739 8854256941006892438782109)
            ·
              refine ⟨3320346352877584664543291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8854256941006892438782109 3320346352877584664543291)
              ·
                refine ⟨4980519529316376996814937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320346352877584664543291 4980519529316376996814937)
                ·
                  refine ⟨3735389646987282747611203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4980519529316376996814937 3735389646987282747611203)
                  ·
                    refine ⟨5603084470480924121416805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3735389646987282747611203 5603084470480924121416805)
                    ·
                      refine ⟨1050578338215173272765651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5603084470480924121416805 1050578338215173272765651)
                      ·
                        rfl

theorem cell23_2045994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_2045994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2045994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2045994 prefixEnd_2045994 := by exact prefixLift 2045994
  have htrace : WordTrace (prefixWord ++ tailWord_2045994) baseStart_2045994 baseEnd_2045994 := by
    simpa [prefixWord, tailWord_2045994, baseEnd_2045994] using wordTrace_append hprefix tailTrace_2045994
  have hstable : (prefixWord ++ tailWord_2045994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2045994).length < 2 ^ (prefixWord ++ tailWord_2045994).sum := by decide
  have hdescent : baseEnd_2045994 < baseStart_2045994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2045994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046017 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 8]
def baseStart_2046017 : Nat := 118140960795 + 2046017 * 2 ^ 59
def prefixEnd_2046017 : Nat := 4983230072969 + 3 ^ 40 * 2046017 * 2
def baseEnd_2046017 : Nat := 116732238696691853642005

theorem tailTrace_2046017 : CollatzResearch.WordTrace tailWord_2046017 prefixEnd_2046017 116732238696691853642005 := by
  unfold tailWord_2046017
  simp only [CollatzResearch.WordTrace]
  refine ⟨74624370628637315729016305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49749580419091543819344203 74624370628637315729016305)
  ·
    refine ⟨55968277971477986796762229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74624370628637315729016305 55968277971477986796762229)
    ·
      refine ⟨5247026059826061262196459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55968277971477986796762229 5247026059826061262196459)
      ·
        refine ⟨7870539089739091893294689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247026059826061262196459 7870539089739091893294689)
        ·
          refine ⟨5902904317304318919971017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7870539089739091893294689 5902904317304318919971017)
          ·
            refine ⟨4427178237978239189978263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5902904317304318919971017 4427178237978239189978263)
            ·
              refine ⟨6640767356967358784967395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4427178237978239189978263 6640767356967358784967395)
              ·
                refine ⟨9961151035451038177451093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6640767356967358784967395 9961151035451038177451093)
                ·
                  refine ⟨116732238696691853642005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9961151035451038177451093 116732238696691853642005)
                  ·
                    rfl

theorem cell23_2046017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_2046017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046017 prefixEnd_2046017 := by exact prefixLift 2046017
  have htrace : WordTrace (prefixWord ++ tailWord_2046017) baseStart_2046017 baseEnd_2046017 := by
    simpa [prefixWord, tailWord_2046017, baseEnd_2046017] using wordTrace_append hprefix tailTrace_2046017
  have hstable : (prefixWord ++ tailWord_2046017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046017).length < 2 ^ (prefixWord ++ tailWord_2046017).sum := by decide
  have hdescent : baseEnd_2046017 < baseStart_2046017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046027 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 3]
def baseStart_2046027 : Nat := 118140960795 + 2046027 * 2 ^ 59
def prefixEnd_2046027 : Nat := 4983230072969 + 3 ^ 40 * 2046027 * 2
def baseEnd_2046027 : Nat := 1050595283076771643652999

theorem tailTrace_2046027 : CollatzResearch.WordTrace tailWord_2046027 prefixEnd_2046027 1050595283076771643652999 := by
  unfold tailWord_2046027
  simp only [CollatzResearch.WordTrace]
  refine ⟨74624735358601087436880335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49749823572400724957920223 74624735358601087436880335)
  ·
    refine ⟨111937103037901631155320503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74624735358601087436880335 111937103037901631155320503)
    ·
      refine ⟨167905654556852446732980755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111937103037901631155320503 167905654556852446732980755)
      ·
        refine ⟨251858481835278670099471133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167905654556852446732980755 251858481835278670099471133)
        ·
          refine ⟨94446930688229501287301675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251858481835278670099471133 94446930688229501287301675)
          ·
            refine ⟨141670396032344251930952513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94446930688229501287301675 141670396032344251930952513)
            ·
              refine ⟨106252797024258188948214385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141670396032344251930952513 106252797024258188948214385)
              ·
                refine ⟨79689597768193641711160789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106252797024258188948214385 79689597768193641711160789)
                ·
                  refine ⟨1867724947692038477605331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79689597768193641711160789 1867724947692038477605331)
                  ·
                    refine ⟨2801587421538057716407997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1867724947692038477605331 2801587421538057716407997)
                    ·
                      refine ⟨1050595283076771643652999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801587421538057716407997 1050595283076771643652999)
                      ·
                        rfl

theorem cell23_2046027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 3].length) (baseStart_2046027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046027 prefixEnd_2046027 := by exact prefixLift 2046027
  have htrace : WordTrace (prefixWord ++ tailWord_2046027) baseStart_2046027 baseEnd_2046027 := by
    simpa [prefixWord, tailWord_2046027, baseEnd_2046027] using wordTrace_append hprefix tailTrace_2046027
  have hstable : (prefixWord ++ tailWord_2046027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046027).length < 2 ^ (prefixWord ++ tailWord_2046027).sum := by decide
  have hdescent : baseEnd_2046027 < baseStart_2046027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046087 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_2046087 : Nat := 118140960795 + 2046087 * 2 ^ 59
def prefixEnd_2046087 : Nat := 4983230072969 + 3 ^ 40 * 2046087 * 2
def baseEnd_2046087 : Nat := 1050626091916041408902723

theorem tailTrace_2046087 : CollatzResearch.WordTrace tailWord_2046087 prefixEnd_2046087 1050626091916041408902723 := by
  unfold tailWord_2046087
  simp only [CollatzResearch.WordTrace]
  refine ⟨74626923738383717684064515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49751282492255811789376343 74626923738383717684064515)
  ·
    refine ⟨111940385607575576526096773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74626923738383717684064515 111940385607575576526096773)
    ·
      refine ⟨20988822301420420598643145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111940385607575576526096773 20988822301420420598643145)
      ·
        refine ⟨15741616726065315448982359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20988822301420420598643145 15741616726065315448982359)
        ·
          refine ⟨23612425089097973173473539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741616726065315448982359 23612425089097973173473539)
          ·
            refine ⟨35418637633646959760210309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23612425089097973173473539 35418637633646959760210309)
            ·
              refine ⟨6640994556308804955039433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35418637633646959760210309 6640994556308804955039433)
              ·
                refine ⟨4980745917231603716279575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6640994556308804955039433 4980745917231603716279575)
                ·
                  refine ⟨7471118875847405574419363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4980745917231603716279575 7471118875847405574419363)
                  ·
                    refine ⟨11206678313771108361629045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7471118875847405574419363 11206678313771108361629045)
                    ·
                      refine ⟨1050626091916041408902723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11206678313771108361629045 1050626091916041408902723)
                      ·
                        rfl

theorem cell23_2046087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_2046087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046087 prefixEnd_2046087 := by exact prefixLift 2046087
  have htrace : WordTrace (prefixWord ++ tailWord_2046087) baseStart_2046087 baseEnd_2046087 := by
    simpa [prefixWord, tailWord_2046087, baseEnd_2046087] using wordTrace_append hprefix tailTrace_2046087
  have hstable : (prefixWord ++ tailWord_2046087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046087).length < 2 ^ (prefixWord ++ tailWord_2046087).sum := by decide
  have hdescent : baseEnd_2046087 < baseStart_2046087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046114 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_2046114 : Nat := 118140960795 + 2046114 * 2 ^ 59
def prefixEnd_2046114 : Nat := 4983230072969 + 3 ^ 40 * 2046114 * 2
def baseEnd_2046114 : Nat := 1050639955893712803265099

theorem tailTrace_2046114 : CollatzResearch.WordTrace tailWord_2046114 prefixEnd_2046114 1050639955893712803265099 := by
  unfold tailWord_2046114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18656977127321475323824349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49751939006190600863531597 18656977127321475323824349)
  ·
    refine ⟨6996366422745553246434131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18656977127321475323824349 6996366422745553246434131)
    ·
      refine ⟨10494549634118329869651197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6996366422745553246434131 10494549634118329869651197)
      ·
        refine ⟨3935456112794373701119199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10494549634118329869651197 3935456112794373701119199)
        ·
          refine ⟨5903184169191560551678799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3935456112794373701119199 5903184169191560551678799)
          ·
            refine ⟨8854776253787340827518199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903184169191560551678799 8854776253787340827518199)
            ·
              refine ⟨13282164380681011241277299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8854776253787340827518199 13282164380681011241277299)
              ·
                refine ⟨19923246571021516861915949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13282164380681011241277299 19923246571021516861915949)
                ·
                  refine ⟨7471217464133068823218481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19923246571021516861915949 7471217464133068823218481)
                  ·
                    refine ⟨5603413098099801617413861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471217464133068823218481 5603413098099801617413861)
                    ·
                      refine ⟨1050639955893712803265099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5603413098099801617413861 1050639955893712803265099)
                      ·
                        rfl

theorem cell23_2046114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_2046114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046114 prefixEnd_2046114 := by exact prefixLift 2046114
  have htrace : WordTrace (prefixWord ++ tailWord_2046114) baseStart_2046114 baseEnd_2046114 := by
    simpa [prefixWord, tailWord_2046114, baseEnd_2046114] using wordTrace_append hprefix tailTrace_2046114
  have hstable : (prefixWord ++ tailWord_2046114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046114).length < 2 ^ (prefixWord ++ tailWord_2046114).sum := by decide
  have hdescent : baseEnd_2046114 < baseStart_2046114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046135 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 1, 2, 2]
def baseStart_2046135 : Nat := 118140960795 + 2046135 * 2 ^ 59
def prefixEnd_2046135 : Nat := 4983230072969 + 3 ^ 40 * 2046135 * 2
def baseEnd_2046135 : Nat := 1050650738987457221102503

theorem tailTrace_2046135 : CollatzResearch.WordTrace tailWord_2046135 prefixEnd_2046135 1050650738987457221102503 := by
  unfold tailWord_2046135
  simp only [CollatzResearch.WordTrace]
  refine ⟨74628674442209821881811859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49752449628139881254541239 74628674442209821881811859)
  ·
    refine ⟨111943011663314732822717789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74628674442209821881811859 111943011663314732822717789)
    ·
      refine ⟨41978629373743024808519171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111943011663314732822717789 41978629373743024808519171)
      ·
        refine ⟨62967944060614537212778757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41978629373743024808519171 62967944060614537212778757)
        ·
          refine ⟨11806489511365225727396017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62967944060614537212778757 11806489511365225727396017)
          ·
            refine ⟨8854867133523919295547013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11806489511365225727396017 8854867133523919295547013)
            ·
              refine ⟨1660287587535734867915065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8854867133523919295547013 1660287587535734867915065)
              ·
                refine ⟨1245215690651801150936299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660287587535734867915065 1245215690651801150936299)
                ·
                  refine ⟨1867823535977701726404449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245215690651801150936299 1867823535977701726404449)
                  ·
                    refine ⟨1400867651983276294803337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1867823535977701726404449 1400867651983276294803337)
                    ·
                      refine ⟨1050650738987457221102503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1400867651983276294803337 1050650738987457221102503)
                      ·
                        rfl

theorem cell23_2046135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_2046135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046135 prefixEnd_2046135 := by exact prefixLift 2046135
  have htrace : WordTrace (prefixWord ++ tailWord_2046135) baseStart_2046135 baseEnd_2046135 := by
    simpa [prefixWord, tailWord_2046135, baseEnd_2046135] using wordTrace_append hprefix tailTrace_2046135
  have hstable : (prefixWord ++ tailWord_2046135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046135).length < 2 ^ (prefixWord ++ tailWord_2046135).sum := by decide
  have hdescent : baseEnd_2046135 < baseStart_2046135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046172 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_2046172 : Nat := 118140960795 + 2046172 * 2 ^ 59
def prefixEnd_2046172 : Nat := 4983230072969 + 3 ^ 40 * 2046172 * 2
def baseEnd_2046172 : Nat := 1050669737771673576339833

theorem tailTrace_2046172 : CollatzResearch.WordTrace tailWord_2046172 prefixEnd_2046172 1050669737771673576339833 := by
  unfold tailWord_2046172
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315011971537888600454385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49753349295383851467272513 37315011971537888600454385)
  ·
    refine ⟨27986258978653416450340789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37315011971537888600454385 27986258978653416450340789)
    ·
      refine ⟨2623711779248757792219449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27986258978653416450340789 2623711779248757792219449)
      ·
        refine ⟨1967783834436568344164587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2623711779248757792219449 1967783834436568344164587)
        ·
          refine ⟨2951675751654852516246881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1967783834436568344164587 2951675751654852516246881)
          ·
            refine ⟨2213756813741139387185161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2951675751654852516246881 2213756813741139387185161)
            ·
              refine ⟨1660317610305854540388871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2213756813741139387185161 1660317610305854540388871)
              ·
                refine ⟨2490476415458781810583307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660317610305854540388871 2490476415458781810583307)
                ·
                  refine ⟨3735714623188172715874961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490476415458781810583307 3735714623188172715874961)
                  ·
                    refine ⟨2801785967391129536906221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3735714623188172715874961 2801785967391129536906221)
                    ·
                      refine ⟨1050669737771673576339833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2801785967391129536906221 1050669737771673576339833)
                      ·
                        rfl

theorem cell23_2046172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_2046172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046172 prefixEnd_2046172 := by exact prefixLift 2046172
  have htrace : WordTrace (prefixWord ++ tailWord_2046172) baseStart_2046172 baseEnd_2046172 := by
    simpa [prefixWord, tailWord_2046172, baseEnd_2046172] using wordTrace_append hprefix tailTrace_2046172
  have hstable : (prefixWord ++ tailWord_2046172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046172).length < 2 ^ (prefixWord ++ tailWord_2046172).sum := by decide
  have hdescent : baseEnd_2046172 < baseStart_2046172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046177 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2046177 : Nat := 118140960795 + 2046177 * 2 ^ 59
def prefixEnd_2046177 : Nat := 4983230072969 + 3 ^ 40 * 2046177 * 2
def baseEnd_2046177 : Nat := 1050672305174946056777309

theorem tailTrace_2046177 : CollatzResearch.WordTrace tailWord_2046177 prefixEnd_2046177 1050672305174946056777309 := by
  unfold tailWord_2046177
  simp only [CollatzResearch.WordTrace]
  refine ⟨74630206308057663054840785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49753470872038442036560523 74630206308057663054840785)
  ·
    refine ⟨55972654731043247291130589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74630206308057663054840785 55972654731043247291130589)
    ·
      refine ⟨20989745524141217734173971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55972654731043247291130589 20989745524141217734173971)
      ·
        refine ⟨31484618286211826601260957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20989745524141217734173971 31484618286211826601260957)
        ·
          refine ⟨11806731857329434975472859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31484618286211826601260957 11806731857329434975472859)
          ·
            refine ⟨17710097785994152463209289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11806731857329434975472859 17710097785994152463209289)
            ·
              refine ⟨13282573339495614347406967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17710097785994152463209289 13282573339495614347406967)
              ·
                refine ⟨19923860009243421521110451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13282573339495614347406967 19923860009243421521110451)
                ·
                  refine ⟨29885790013865132281665677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19923860009243421521110451 29885790013865132281665677)
                  ·
                    refine ⟨11207171255199424605624629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29885790013865132281665677 11207171255199424605624629)
                    ·
                      refine ⟨1050672305174946056777309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11207171255199424605624629 1050672305174946056777309)
                      ·
                        rfl

theorem cell23_2046177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2046177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046177 prefixEnd_2046177 := by exact prefixLift 2046177
  have htrace : WordTrace (prefixWord ++ tailWord_2046177) baseStart_2046177 baseEnd_2046177 := by
    simpa [prefixWord, tailWord_2046177, baseEnd_2046177] using wordTrace_append hprefix tailTrace_2046177
  have hstable : (prefixWord ++ tailWord_2046177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046177).length < 2 ^ (prefixWord ++ tailWord_2046177).sum := by decide
  have hdescent : baseEnd_2046177 < baseStart_2046177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046187 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_2046187 : Nat := 118140960795 + 2046187 * 2 ^ 59
def prefixEnd_2046187 : Nat := 4983230072969 + 3 ^ 40 * 2046187 * 2
def baseEnd_2046187 : Nat := 1050677439981491017652263

theorem tailTrace_2046187 : CollatzResearch.WordTrace tailWord_2046187 prefixEnd_2046187 1050677439981491017652263 := by
  unfold tailWord_2046187
  simp only [CollatzResearch.WordTrace]
  refine ⟨74630571038021434762704815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49753714025347623175136543 74630571038021434762704815)
  ·
    refine ⟨111945856557032152144057223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74630571038021434762704815 111945856557032152144057223)
    ·
      refine ⟨167918784835548228216085835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111945856557032152144057223 167918784835548228216085835)
      ·
        refine ⟨251878177253322342324128753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167918784835548228216085835 251878177253322342324128753)
        ·
          refine ⟨188908632939991756743096565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251878177253322342324128753 188908632939991756743096565)
          ·
            refine ⟨17710184338124227194665303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188908632939991756743096565 17710184338124227194665303)
            ·
              refine ⟨26565276507186340791997955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17710184338124227194665303 26565276507186340791997955)
              ·
                refine ⟨39847914760779511187996933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26565276507186340791997955 39847914760779511187996933)
                ·
                  refine ⟨7471484017646158347749425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39847914760779511187996933 7471484017646158347749425)
                  ·
                    refine ⟨5603613013234618760812069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471484017646158347749425 5603613013234618760812069)
                    ·
                      refine ⟨1050677439981491017652263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5603613013234618760812069 1050677439981491017652263)
                      ·
                        rfl

theorem cell23_2046187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_2046187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046187 prefixEnd_2046187 := by exact prefixLift 2046187
  have htrace : WordTrace (prefixWord ++ tailWord_2046187) baseStart_2046187 baseEnd_2046187 := by
    simpa [prefixWord, tailWord_2046187, baseEnd_2046187] using wordTrace_append hprefix tailTrace_2046187
  have hstable : (prefixWord ++ tailWord_2046187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046187).length < 2 ^ (prefixWord ++ tailWord_2046187).sum := by decide
  have hdescent : baseEnd_2046187 < baseStart_2046187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046204 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_2046204 : Nat := 118140960795 + 2046204 * 2 ^ 59
def prefixEnd_2046204 : Nat := 4983230072969 + 3 ^ 40 * 2046204 * 2
def baseEnd_2046204 : Nat := 1050686169152617451139685

theorem tailTrace_2046204 : CollatzResearch.WordTrace tailWord_2046204 prefixEnd_2046204 1050686169152617451139685 := by
  unfold tailWord_2046204
  simp only [CollatzResearch.WordTrace]
  refine ⟨37315595539479923333036833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49754127385973231110715777 37315595539479923333036833)
  ·
    refine ⟨27986696654609942499777625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37315595539479923333036833 27986696654609942499777625)
    ·
      refine ⟨20990022490957456874833219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27986696654609942499777625 20990022490957456874833219)
      ·
        refine ⟨31485033736436185312249829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20990022490957456874833219 31485033736436185312249829)
        ·
          refine ⟨5903443825581784746046843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31485033736436185312249829 5903443825581784746046843)
          ·
            refine ⟨8855165738372677119070265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5903443825581784746046843 8855165738372677119070265)
            ·
              refine ⟨6641374303779507839302699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8855165738372677119070265 6641374303779507839302699)
              ·
                refine ⟨9962061455669261758954049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6641374303779507839302699 9962061455669261758954049)
                ·
                  refine ⟨7471546091751946319215537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9962061455669261758954049 7471546091751946319215537)
                  ·
                    refine ⟨5603659568813959739411653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7471546091751946319215537 5603659568813959739411653)
                    ·
                      refine ⟨1050686169152617451139685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5603659568813959739411653 1050686169152617451139685)
                      ·
                        rfl

theorem cell23_2046204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_2046204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046204 prefixEnd_2046204 := by exact prefixLift 2046204
  have htrace : WordTrace (prefixWord ++ tailWord_2046204) baseStart_2046204 baseEnd_2046204 := by
    simpa [prefixWord, tailWord_2046204, baseEnd_2046204] using wordTrace_append hprefix tailTrace_2046204
  have hstable : (prefixWord ++ tailWord_2046204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046204).length < 2 ^ (prefixWord ++ tailWord_2046204).sum := by decide
  have hdescent : baseEnd_2046204 < baseStart_2046204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046227 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 6, 5]
def baseStart_2046227 : Nat := 118140960795 + 2046227 * 2 ^ 59
def prefixEnd_2046227 : Nat := 4983230072969 + 3 ^ 40 * 2046227 * 2
def baseEnd_2046227 : Nat := 350232659735890287050693

theorem tailTrace_2046227 : CollatzResearch.WordTrace tailWord_2046227 prefixEnd_2046227 350232659735890287050693 := by
  unfold tailWord_2046227
  simp only [CollatzResearch.WordTrace]
  refine ⟨74632029957876521594160935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49754686638584347729440623 74632029957876521594160935)
  ·
    refine ⟨111948044936814782391241403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74632029957876521594160935 111948044936814782391241403)
    ·
      refine ⟨167922067405222173586862105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111948044936814782391241403 167922067405222173586862105)
      ·
        refine ⟨125941550553916630190146579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167922067405222173586862105 125941550553916630190146579)
        ·
          refine ⟨188912325830874945285219869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125941550553916630190146579 188912325830874945285219869)
          ·
            refine ⟨70842122186578104481957451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188912325830874945285219869 70842122186578104481957451)
            ·
              refine ⟨106263183279867156722936177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70842122186578104481957451 106263183279867156722936177)
              ·
                refine ⟨79697387459900367542202133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106263183279867156722936177 79697387459900367542202133)
                ·
                  refine ⟨3735815037182829728540725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79697387459900367542202133 3735815037182829728540725)
                  ·
                    refine ⟨350232659735890287050693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3735815037182829728540725 350232659735890287050693)
                    ·
                      rfl

theorem cell23_2046227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 5].length) (baseStart_2046227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046227 prefixEnd_2046227 := by exact prefixLift 2046227
  have htrace : WordTrace (prefixWord ++ tailWord_2046227) baseStart_2046227 baseEnd_2046227 := by
    simpa [prefixWord, tailWord_2046227, baseEnd_2046227] using wordTrace_append hprefix tailTrace_2046227
  have hstable : (prefixWord ++ tailWord_2046227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046227).length < 2 ^ (prefixWord ++ tailWord_2046227).sum := by decide
  have hdescent : baseEnd_2046227 < baseStart_2046227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046231 : List Nat := [1, 1, 3, 4, 1, 2, 3, 3, 5]
def baseStart_2046231 : Nat := 118140960795 + 2046231 * 2 ^ 59
def prefixEnd_2046231 : Nat := 4983230072969 + 3 ^ 40 * 2046231 * 2
def baseEnd_2046231 : Nat := 116744448125587649500229

theorem tailTrace_2046231 : CollatzResearch.WordTrace tailWord_2046231 prefixEnd_2046231 116744448125587649500229 := by
  unfold tailWord_2046231
  simp only [CollatzResearch.WordTrace]
  refine ⟨74632175849862030277306547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49754783899908020184871031 74632175849862030277306547)
  ·
    refine ⟨111948263774793045415959821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74632175849862030277306547 111948263774793045415959821)
    ·
      refine ⟨41980598915547392030984933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111948263774793045415959821 41980598915547392030984933)
      ·
        refine ⟨7871362296665136005809675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41980598915547392030984933 7871362296665136005809675)
        ·
          refine ⟨11807043444997704008714513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871362296665136005809675 11807043444997704008714513)
          ·
            refine ⟨8855282583748278006535885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11807043444997704008714513 8855282583748278006535885)
            ·
              refine ⟨3320730968905604252450957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8855282583748278006535885 3320730968905604252450957)
              ·
                refine ⟨1245274113339601594669109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3320730968905604252450957 1245274113339601594669109)
                ·
                  refine ⟨116744448125587649500229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1245274113339601594669109 116744448125587649500229)
                  ·
                    rfl

theorem cell23_2046231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 5].length) (baseStart_2046231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046231 prefixEnd_2046231 := by exact prefixLift 2046231
  have htrace : WordTrace (prefixWord ++ tailWord_2046231) baseStart_2046231 baseEnd_2046231 := by
    simpa [prefixWord, tailWord_2046231, baseEnd_2046231] using wordTrace_append hprefix tailTrace_2046231
  have hstable : (prefixWord ++ tailWord_2046231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046231).length < 2 ^ (prefixWord ++ tailWord_2046231).sum := by decide
  have hdescent : baseEnd_2046231 < baseStart_2046231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046244 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_2046244 : Nat := 118140960795 + 2046244 * 2 ^ 59
def prefixEnd_2046244 : Nat := 4983230072969 + 3 ^ 40 * 2046244 * 2
def baseEnd_2046244 : Nat := 350235569459599098213167

theorem tailTrace_2046244 : CollatzResearch.WordTrace tailWord_2046244 prefixEnd_2046244 350235569459599098213167 := by
  unfold tailWord_2046244
  simp only [CollatzResearch.WordTrace]
  refine ⟨37316324999407466748764893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49755099999209955665019857 37316324999407466748764893)
  ·
    refine ⟨13993621874777800030786835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37316324999407466748764893 13993621874777800030786835)
    ·
      refine ⟨20990432812166700046180253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13993621874777800030786835 20990432812166700046180253)
      ·
        refine ⟨7871412304562512517317595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20990432812166700046180253 7871412304562512517317595)
        ·
          refine ⟨11807118456843768775976393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7871412304562512517317595 11807118456843768775976393)
          ·
            refine ⟨8855338842632826581982295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11807118456843768775976393 8855338842632826581982295)
            ·
              refine ⟨13283008263949239872973443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855338842632826581982295 13283008263949239872973443)
              ·
                refine ⟨19924512395923859809460165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13283008263949239872973443 19924512395923859809460165)
                ·
                  refine ⟨3735846074235723714273781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19924512395923859809460165 3735846074235723714273781)
                  ·
                    refine ⟨350235569459599098213167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3735846074235723714273781 350235569459599098213167)
                    ·
                      rfl

theorem cell23_2046244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_2046244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046244 prefixEnd_2046244 := by exact prefixLift 2046244
  have htrace : WordTrace (prefixWord ++ tailWord_2046244) baseStart_2046244 baseEnd_2046244 := by
    simpa [prefixWord, tailWord_2046244, baseEnd_2046244] using wordTrace_append hprefix tailTrace_2046244
  have hstable : (prefixWord ++ tailWord_2046244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046244).length < 2 ^ (prefixWord ++ tailWord_2046244).sum := by decide
  have hdescent : baseEnd_2046244 < baseStart_2046244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046248 : List Nat := [2, 1, 5, 1, 4, 1, 1, 1, 7]
def baseStart_2046248 : Nat := 118140960795 + 2046248 * 2 ^ 59
def prefixEnd_2046248 : Nat := 4983230072969 + 3 ^ 40 * 2046248 * 2
def baseEnd_2046248 : Nat := 116745418033490586554387

theorem tailTrace_2046248 : CollatzResearch.WordTrace tailWord_2046248 prefixEnd_2046248 116745418033490586554387 := by
  unfold tailWord_2046248
  simp only [CollatzResearch.WordTrace]
  refine ⟨37316397945400221090337699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49755197260533628120450265 37316397945400221090337699)
  ·
    refine ⟨55974596918100331635506549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37316397945400221090337699 55974596918100331635506549)
    ·
      refine ⟨5247618461071906090828739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55974596918100331635506549 5247618461071906090828739)
      ·
        refine ⟨7871427691607859136243109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5247618461071906090828739 7871427691607859136243109)
        ·
          refine ⟨1475892692176473588045583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7871427691607859136243109 1475892692176473588045583)
          ·
            refine ⟨2213839038264710382068375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1475892692176473588045583 2213839038264710382068375)
            ·
              refine ⟨3320758557397065573102563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2213839038264710382068375 3320758557397065573102563)
              ·
                refine ⟨4981137836095598359653845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320758557397065573102563 4981137836095598359653845)
                ·
                  refine ⟨116745418033490586554387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4981137836095598359653845 116745418033490586554387)
                  ·
                    rfl

theorem cell23_2046248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 1, 7].length) (baseStart_2046248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046248 prefixEnd_2046248 := by exact prefixLift 2046248
  have htrace : WordTrace (prefixWord ++ tailWord_2046248) baseStart_2046248 baseEnd_2046248 := by
    simpa [prefixWord, tailWord_2046248, baseEnd_2046248] using wordTrace_append hprefix tailTrace_2046248
  have hstable : (prefixWord ++ tailWord_2046248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046248).length < 2 ^ (prefixWord ++ tailWord_2046248).sum := by decide
  have hdescent : baseEnd_2046248 < baseStart_2046248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046277 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_2046277 : Nat := 118140960795 + 2046277 * 2 ^ 59
def prefixEnd_2046277 : Nat := 4983230072969 + 3 ^ 40 * 2046277 * 2
def baseEnd_2046277 : Nat := 1050723653240395665526849

theorem tailTrace_2046277 : CollatzResearch.WordTrace tailWord_2046277 prefixEnd_2046277 1050723653240395665526849 := by
  unfold tailWord_2046277
  simp only [CollatzResearch.WordTrace]
  refine ⟨74633853607695380133481085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49755902405130253422320723 74633853607695380133481085)
  ·
    refine ⟨27987695102885767550055407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74633853607695380133481085 27987695102885767550055407)
    ·
      refine ⟨41981542654328651325083111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27987695102885767550055407 41981542654328651325083111)
      ·
        refine ⟨62972313981492976987624667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41981542654328651325083111 62972313981492976987624667)
        ·
          refine ⟨94458470972239465481437001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62972313981492976987624667 94458470972239465481437001)
          ·
            refine ⟨70843853229179599111077751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94458470972239465481437001 70843853229179599111077751)
            ·
              refine ⟨106265779843769398666616627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70843853229179599111077751 106265779843769398666616627)
              ·
                refine ⟨159398669765654097999924941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106265779843769398666616627 159398669765654097999924941)
                ·
                  refine ⟨59774501162120286749971853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 159398669765654097999924941 59774501162120286749971853)
                  ·
                    refine ⟨22415437935795107531239445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59774501162120286749971853 22415437935795107531239445)
                    ·
                      refine ⟨1050723653240395665526849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22415437935795107531239445 1050723653240395665526849)
                      ·
                        rfl

theorem cell23_2046277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_2046277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046277 prefixEnd_2046277 := by exact prefixLift 2046277
  have htrace : WordTrace (prefixWord ++ tailWord_2046277) baseStart_2046277 baseEnd_2046277 := by
    simpa [prefixWord, tailWord_2046277, baseEnd_2046277] using wordTrace_append hprefix tailTrace_2046277
  have hstable : (prefixWord ++ tailWord_2046277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046277).length < 2 ^ (prefixWord ++ tailWord_2046277).sum := by decide
  have hdescent : baseEnd_2046277 < baseStart_2046277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046287 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 8]
def baseStart_2046287 : Nat := 118140960795 + 2046287 * 2 ^ 59
def prefixEnd_2046287 : Nat := 4983230072969 + 3 ^ 40 * 2046287 * 2
def baseEnd_2046287 : Nat := 116747643116326736266867

theorem tailTrace_2046287 : CollatzResearch.WordTrace tailWord_2046287 prefixEnd_2046287 116747643116326736266867 := by
  unfold tailWord_2046287
  simp only [CollatzResearch.WordTrace]
  refine ⟨74634218337659151841345115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49756145558439434560896743 74634218337659151841345115)
  ·
    refine ⟨111951327506488727762017673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74634218337659151841345115 111951327506488727762017673)
    ·
      refine ⟨83963495629866545821513255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111951327506488727762017673 83963495629866545821513255)
      ·
        refine ⟨125945243444799818732269883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83963495629866545821513255 125945243444799818732269883)
        ·
          refine ⟨188917865167199728098404825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125945243444799818732269883 188917865167199728098404825)
          ·
            refine ⟨141688398875399796073803619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188917865167199728098404825 141688398875399796073803619)
            ·
              refine ⟨212532598313099694110705429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141688398875399796073803619 212532598313099694110705429)
              ·
                refine ⟨9962465545926548161439317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212532598313099694110705429 9962465545926548161439317)
                ·
                  refine ⟨116747643116326736266867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9962465545926548161439317 116747643116326736266867)
                  ·
                    rfl

theorem cell23_2046287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 8].length) (baseStart_2046287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046287 prefixEnd_2046287 := by exact prefixLift 2046287
  have htrace : WordTrace (prefixWord ++ tailWord_2046287) baseStart_2046287 baseEnd_2046287 := by
    simpa [prefixWord, tailWord_2046287, baseEnd_2046287] using wordTrace_append hprefix tailTrace_2046287
  have hstable : (prefixWord ++ tailWord_2046287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046287).length < 2 ^ (prefixWord ++ tailWord_2046287).sum := by decide
  have hdescent : baseEnd_2046287 < baseStart_2046287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046308 : List Nat := [2, 3, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_2046308 : Nat := 118140960795 + 2046308 * 2 ^ 59
def prefixEnd_2046308 : Nat := 4983230072969 + 3 ^ 40 * 2046308 * 2
def baseEnd_2046308 : Nat := 350246523713561681413069

theorem tailTrace_2046308 : CollatzResearch.WordTrace tailWord_2046308 prefixEnd_2046308 350246523713561681413069 := by
  unfold tailWord_2046308
  simp only [CollatzResearch.WordTrace]
  refine ⟨37317492135291536213929789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49756656180388714951906385 37317492135291536213929789)
  ·
    refine ⟨13994059550734326080223671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37317492135291536213929789 13994059550734326080223671)
    ·
      refine ⟨20991089326101489120335507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13994059550734326080223671 20991089326101489120335507)
      ·
        refine ⟨31486633989152233680503261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20991089326101489120335507 31486633989152233680503261)
        ·
          refine ⟨11807487745932087630188723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31486633989152233680503261 11807487745932087630188723)
          ·
            refine ⟨17711231618898131445283085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11807487745932087630188723 17711231618898131445283085)
            ·
              refine ⟨6641711857086799291981157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17711231618898131445283085 6641711857086799291981157)
              ·
                refine ⟨1245320973203774867246467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6641711857086799291981157 1245320973203774867246467)
                ·
                  refine ⟨1867981459805662300869701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245320973203774867246467 1867981459805662300869701)
                  ·
                    refine ⟨350246523713561681413069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1867981459805662300869701 350246523713561681413069)
                    ·
                      rfl

theorem cell23_2046308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_2046308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046308 prefixEnd_2046308 := by exact prefixLift 2046308
  have htrace : WordTrace (prefixWord ++ tailWord_2046308) baseStart_2046308 baseEnd_2046308 := by
    simpa [prefixWord, tailWord_2046308, baseEnd_2046308] using wordTrace_append hprefix tailTrace_2046308
  have hstable : (prefixWord ++ tailWord_2046308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046308).length < 2 ^ (prefixWord ++ tailWord_2046308).sum := by decide
  have hdescent : baseEnd_2046308 < baseStart_2046308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046331 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 3]
def baseStart_2046331 : Nat := 118140960795 + 2046331 * 2 ^ 59
def prefixEnd_2046331 : Nat := 4983230072969 + 3 ^ 40 * 2046331 * 2
def baseEnd_2046331 : Nat := 1050751381195738454251601

theorem tailTrace_2046331 : CollatzResearch.WordTrace tailWord_2046331 prefixEnd_2046331 1050751381195738454251601 := by
  unfold tailWord_2046331
  simp only [CollatzResearch.WordTrace]
  refine ⟨74635823149499747355946847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49757215432999831570631231 74635823149499747355946847)
  ·
    refine ⟨111953734724249621033920271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74635823149499747355946847 111953734724249621033920271)
    ·
      refine ⟨167930602086374431550880407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111953734724249621033920271 167930602086374431550880407)
      ·
        refine ⟨251895903129561647326320611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167930602086374431550880407 251895903129561647326320611)
        ·
          refine ⟨377843854694342470989480917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251895903129561647326320611 377843854694342470989480917)
          ·
            refine ⟨8855715344398651663815959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 377843854694342470989480917 8855715344398651663815959)
            ·
              refine ⟨13283573016597977495723939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8855715344398651663815959 13283573016597977495723939)
              ·
                refine ⟨19925359524896966243585909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13283573016597977495723939 19925359524896966243585909)
                ·
                  refine ⟨1868002455459090585336179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19925359524896966243585909 1868002455459090585336179)
                  ·
                    refine ⟨2802003683188635878004269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868002455459090585336179 2802003683188635878004269)
                    ·
                      refine ⟨1050751381195738454251601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802003683188635878004269 1050751381195738454251601)
                      ·
                        rfl

theorem cell23_2046331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 3].length) (baseStart_2046331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046331 prefixEnd_2046331 := by exact prefixLift 2046331
  have htrace : WordTrace (prefixWord ++ tailWord_2046331) baseStart_2046331 baseEnd_2046331 := by
    simpa [prefixWord, tailWord_2046331, baseEnd_2046331] using wordTrace_append hprefix tailTrace_2046331
  have hstable : (prefixWord ++ tailWord_2046331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046331).length < 2 ^ (prefixWord ++ tailWord_2046331).sum := by decide
  have hdescent : baseEnd_2046331 < baseStart_2046331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046365 : List Nat := [1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_2046365 : Nat := 118140960795 + 2046365 * 2 ^ 59
def prefixEnd_2046365 : Nat := 4983230072969 + 3 ^ 40 * 2046365 * 2
def baseEnd_2046365 : Nat := 1050768839537991321226445

theorem tailTrace_2046365 : CollatzResearch.WordTrace tailWord_2046365 prefixEnd_2046365 1050768839537991321226445 := by
  unfold tailWord_2046365
  simp only [CollatzResearch.WordTrace]
  refine ⟨74637063231376571162684549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49758042154251047441789699 74637063231376571162684549)
  ·
    refine ⟨13994449355883107093003353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74637063231376571162684549 13994449355883107093003353)
    ·
      refine ⟨10495837016912330319752515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13994449355883107093003353 10495837016912330319752515)
      ·
        refine ⟨15743755525368495479628773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10495837016912330319752515 15743755525368495479628773)
        ·
          refine ⟨2951954161006592902430395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15743755525368495479628773 2951954161006592902430395)
          ·
            refine ⟨4427931241509889353645593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2951954161006592902430395 4427931241509889353645593)
            ·
              refine ⟨3320948431132417015234195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4427931241509889353645593 3320948431132417015234195)
              ·
                refine ⟨4981422646698625522851293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3320948431132417015234195 4981422646698625522851293)
                ·
                  refine ⟨1868033492511984571069235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4981422646698625522851293 1868033492511984571069235)
                  ·
                    refine ⟨2802050238767976856603853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1868033492511984571069235 2802050238767976856603853)
                    ·
                      refine ⟨1050768839537991321226445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802050238767976856603853 1050768839537991321226445)
                      ·
                        rfl

theorem cell23_2046365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_2046365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046365 prefixEnd_2046365 := by exact prefixLift 2046365
  have htrace : WordTrace (prefixWord ++ tailWord_2046365) baseStart_2046365 baseEnd_2046365 := by
    simpa [prefixWord, tailWord_2046365, baseEnd_2046365] using wordTrace_append hprefix tailTrace_2046365
  have hstable : (prefixWord ++ tailWord_2046365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046365).length < 2 ^ (prefixWord ++ tailWord_2046365).sum := by decide
  have hdescent : baseEnd_2046365 < baseStart_2046365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046408 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3]
def baseStart_2046408 : Nat := 118140960795 + 2046408 * 2 ^ 59
def prefixEnd_2046408 : Nat := 4983230072969 + 3 ^ 40 * 2046408 * 2
def baseEnd_2046408 : Nat := 1050790919206134652988747

theorem tailTrace_2046408 : CollatzResearch.WordTrace tailWord_2046408 prefixEnd_2046408 1050790919206134652988747 := by
  unfold tailWord_2046408
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319315785110394753249939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49759087713480526337666585 37319315785110394753249939)
  ·
    refine ⟨55978973677665592129874909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319315785110394753249939 55978973677665592129874909)
    ·
      refine ⟨20992115129124597048703091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55978973677665592129874909 20992115129124597048703091)
      ·
        refine ⟨31488172693686895573054637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20992115129124597048703091 31488172693686895573054637)
        ·
          refine ⟨11808064760132585839895489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31488172693686895573054637 11808064760132585839895489)
          ·
            refine ⟨8856048570099439379921617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11808064760132585839895489 8856048570099439379921617)
            ·
              refine ⟨6642036427574579534941213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8856048570099439379921617 6642036427574579534941213)
              ·
                refine ⟨2490763660340467325602955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6642036427574579534941213 2490763660340467325602955)
                ·
                  refine ⟨3736145490510700988404433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2490763660340467325602955 3736145490510700988404433)
                  ·
                    refine ⟨2802109117883025741303325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736145490510700988404433 2802109117883025741303325)
                    ·
                      refine ⟨1050790919206134652988747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802109117883025741303325 1050790919206134652988747)
                      ·
                        rfl

theorem cell23_2046408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_2046408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046408 prefixEnd_2046408 := by exact prefixLift 2046408
  have htrace : WordTrace (prefixWord ++ tailWord_2046408) baseStart_2046408 baseEnd_2046408 := by
    simpa [prefixWord, tailWord_2046408, baseEnd_2046408] using wordTrace_append hprefix tailTrace_2046408
  have hstable : (prefixWord ++ tailWord_2046408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046408).length < 2 ^ (prefixWord ++ tailWord_2046408).sum := by decide
  have hdescent : baseEnd_2046408 < baseStart_2046408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046424 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 2, 7]
def baseStart_2046424 : Nat := 118140960795 + 2046424 * 2 ^ 59
def prefixEnd_2046424 : Nat := 4983230072969 + 3 ^ 40 * 2046424 * 2
def baseEnd_2046424 : Nat := 350266378298868863462891

theorem tailTrace_2046424 : CollatzResearch.WordTrace tailWord_2046424 prefixEnd_2046424 350266378298868863462891 := by
  unfold tailWord_2046424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37319607569081412119541163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49759476758775216159388217 37319607569081412119541163)
  ·
    refine ⟨55979411353622118179311745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37319607569081412119541163 55979411353622118179311745)
    ·
      refine ⟨41984558515216588634483809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55979411353622118179311745 41984558515216588634483809)
      ·
        refine ⟨31488418886412441475862857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41984558515216588634483809 31488418886412441475862857)
        ·
          refine ⟨23616314164809331106897143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31488418886412441475862857 23616314164809331106897143)
          ·
            refine ⟨35424471247213996660345715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23616314164809331106897143 35424471247213996660345715)
            ·
              refine ⟨53136706870820994990518573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35424471247213996660345715 53136706870820994990518573)
              ·
                refine ⟨19926265076557873121444465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53136706870820994990518573 19926265076557873121444465)
                ·
                  refine ⟨14944698807418404841083349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19926265076557873121444465 14944698807418404841083349)
                  ·
                    refine ⟨350266378298868863462891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14944698807418404841083349 350266378298868863462891)
                    ·
                      rfl

theorem cell23_2046424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_2046424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046424 prefixEnd_2046424 := by exact prefixLift 2046424
  have htrace : WordTrace (prefixWord ++ tailWord_2046424) baseStart_2046424 baseEnd_2046424 := by
    simpa [prefixWord, tailWord_2046424, baseEnd_2046424] using wordTrace_append hprefix tailTrace_2046424
  have hstable : (prefixWord ++ tailWord_2046424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046424).length < 2 ^ (prefixWord ++ tailWord_2046424).sum := by decide
  have hdescent : baseEnd_2046424 < baseStart_2046424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046448 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2]
def baseStart_2046448 : Nat := 118140960795 + 2046448 * 2 ^ 59
def prefixEnd_2046448 : Nat := 4983230072969 + 3 ^ 40 * 2046448 * 2
def baseEnd_2046448 : Nat := 1050811458432314496488563

theorem tailTrace_2046448 : CollatzResearch.WordTrace tailWord_2046448 prefixEnd_2046448 1050811458432314496488563 := by
  unfold tailWord_2046448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37320045245037938168977999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49760060326717250891970665 37320045245037938168977999)
  ·
    refine ⟨55980067867556907253466999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37320045245037938168977999 55980067867556907253466999)
    ·
      refine ⟨83970101801335360880200499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55980067867556907253466999 83970101801335360880200499)
      ·
        refine ⟨125955152702003041320300749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83970101801335360880200499 125955152702003041320300749)
        ·
          refine ⟨47233182263251140495112781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125955152702003041320300749 47233182263251140495112781)
          ·
            refine ⟨17712443348719177685667293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47233182263251140495112781 17712443348719177685667293)
            ·
              refine ⟨6642166255769691632125235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17712443348719177685667293 6642166255769691632125235)
              ·
                refine ⟨9963249383654537448187853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6642166255769691632125235 9963249383654537448187853)
                ·
                  refine ⟨3736218518870451543070445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9963249383654537448187853 3736218518870451543070445)
                  ·
                    refine ⟨1401081944576419328651417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3736218518870451543070445 1401081944576419328651417)
                    ·
                      refine ⟨1050811458432314496488563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401081944576419328651417 1050811458432314496488563)
                      ·
                        rfl

theorem cell23_2046448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 3, 2].length) (baseStart_2046448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046448 prefixEnd_2046448 := by exact prefixLift 2046448
  have htrace : WordTrace (prefixWord ++ tailWord_2046448) baseStart_2046448 baseEnd_2046448 := by
    simpa [prefixWord, tailWord_2046448, baseEnd_2046448] using wordTrace_append hprefix tailTrace_2046448
  have hstable : (prefixWord ++ tailWord_2046448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046448).length < 2 ^ (prefixWord ++ tailWord_2046448).sum := by decide
  have hdescent : baseEnd_2046448 < baseStart_2046448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046529 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 2, 2, 2]
def baseStart_2046529 : Nat := 118140960795 + 2046529 * 2 ^ 59
def prefixEnd_2046529 : Nat := 4983230072969 + 3 ^ 40 * 2046529 * 2
def baseEnd_2046529 : Nat := 1050853050365328679575691

theorem tailTrace_2046529 : CollatzResearch.WordTrace tailWord_2046529 prefixEnd_2046529 1050853050365328679575691 := by
  unfold tailWord_2046529
  simp only [CollatzResearch.WordTrace]
  refine ⟨74643044802782427171654641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49762029868521618114436427 74643044802782427171654641)
  ·
    refine ⟨55982283602086820378740981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74643044802782427171654641 55982283602086820378740981)
    ·
      refine ⟨5248339087695639410506967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55982283602086820378740981 5248339087695639410506967)
      ·
        refine ⟨7872508631543459115760451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248339087695639410506967 7872508631543459115760451)
        ·
          refine ⟨11808762947315188673640677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872508631543459115760451 11808762947315188673640677)
          ·
            refine ⟨2214143052621597876307627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11808762947315188673640677 2214143052621597876307627)
            ·
              refine ⟨3321214578932396814461441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214143052621597876307627 3321214578932396814461441)
              ·
                refine ⟨2490910934199297610846081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321214578932396814461441 2490910934199297610846081)
                ·
                  refine ⟨1868183200649473208134561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2490910934199297610846081 1868183200649473208134561)
                  ·
                    refine ⟨1401137400487104906100921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1868183200649473208134561 1401137400487104906100921)
                    ·
                      refine ⟨1050853050365328679575691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401137400487104906100921 1050853050365328679575691)
                      ·
                        rfl

theorem cell23_2046529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_2046529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046529 prefixEnd_2046529 := by exact prefixLift 2046529
  have htrace : WordTrace (prefixWord ++ tailWord_2046529) baseStart_2046529 baseEnd_2046529 := by
    simpa [prefixWord, tailWord_2046529, baseEnd_2046529] using wordTrace_append hprefix tailTrace_2046529
  have hstable : (prefixWord ++ tailWord_2046529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046529).length < 2 ^ (prefixWord ++ tailWord_2046529).sum := by decide
  have hdescent : baseEnd_2046529 < baseStart_2046529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046531 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 2, 5]
def baseStart_2046531 : Nat := 118140960795 + 2046531 * 2 ^ 59
def prefixEnd_2046531 : Nat := 4983230072969 + 3 ^ 40 * 2046531 * 2
def baseEnd_2046531 : Nat := 350284692442212557250227

theorem tailTrace_2046531 : CollatzResearch.WordTrace tailWord_2046531 prefixEnd_2046531 350284692442212557250227 := by
  unfold tailWord_2046531
  simp only [CollatzResearch.WordTrace]
  refine ⟨74643117748775181513227447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49762078499183454342151631 74643117748775181513227447)
  ·
    refine ⟨111964676623162772269841171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74643117748775181513227447 111964676623162772269841171)
    ·
      refine ⟨167947014934744158404761757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111964676623162772269841171 167947014934744158404761757)
      ·
        refine ⟨62980130600529059401785659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167947014934744158404761757 62980130600529059401785659)
        ·
          refine ⟨94470195900793589102678489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62980130600529059401785659 94470195900793589102678489)
          ·
            refine ⟨70852646925595191827008867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94470195900793589102678489 70852646925595191827008867)
            ·
              refine ⟨106278970388392787740513301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70852646925595191827008867 106278970388392787740513301)
              ·
                refine ⟨4981826736955911925336561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 106278970388392787740513301 4981826736955911925336561)
                ·
                  refine ⟨3736370052716933944002421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4981826736955911925336561 3736370052716933944002421)
                  ·
                    refine ⟨350284692442212557250227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3736370052716933944002421 350284692442212557250227)
                    ·
                      rfl

theorem cell23_2046531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 5].length) (baseStart_2046531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046531 prefixEnd_2046531 := by exact prefixLift 2046531
  have htrace : WordTrace (prefixWord ++ tailWord_2046531) baseStart_2046531 baseEnd_2046531 := by
    simpa [prefixWord, tailWord_2046531, baseEnd_2046531] using wordTrace_append hprefix tailTrace_2046531
  have hstable : (prefixWord ++ tailWord_2046531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046531).length < 2 ^ (prefixWord ++ tailWord_2046531).sum := by decide
  have hdescent : baseEnd_2046531 < baseStart_2046531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046551 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_2046551 : Nat := 118140960795 + 2046551 * 2 ^ 59
def prefixEnd_2046551 : Nat := 4983230072969 + 3 ^ 40 * 2046551 * 2
def baseEnd_2046551 : Nat := 1050864346939727593500589

theorem tailTrace_2046551 : CollatzResearch.WordTrace tailWord_2046551 prefixEnd_2046551 1050864346939727593500589 := by
  unfold tailWord_2046551
  simp only [CollatzResearch.WordTrace]
  refine ⟨74643847208702724928955507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49762564805801816619303671 74643847208702724928955507)
  ·
    refine ⟨111965770813054087393433261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74643847208702724928955507 111965770813054087393433261)
    ·
      refine ⟨41987164054895282772537473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111965770813054087393433261 41987164054895282772537473)
      ·
        refine ⟨31490373041171462079403105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41987164054895282772537473 31490373041171462079403105)
        ·
          refine ⟨23617779780878596559552329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31490373041171462079403105 23617779780878596559552329)
          ·
            refine ⟨17713334835658947419664247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23617779780878596559552329 17713334835658947419664247)
            ·
              refine ⟨26570002253488421129496371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17713334835658947419664247 26570002253488421129496371)
              ·
                refine ⟨39855003380232631694244557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26570002253488421129496371 39855003380232631694244557)
                ·
                  refine ⟨14945626267587236885341709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39855003380232631694244557 14945626267587236885341709)
                  ·
                    refine ⟨5604609850345213832003141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14945626267587236885341709 5604609850345213832003141)
                    ·
                      refine ⟨1050864346939727593500589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5604609850345213832003141 1050864346939727593500589)
                      ·
                        rfl

theorem cell23_2046551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_2046551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046551 prefixEnd_2046551 := by exact prefixLift 2046551
  have htrace : WordTrace (prefixWord ++ tailWord_2046551) baseStart_2046551 baseEnd_2046551 := by
    simpa [prefixWord, tailWord_2046551, baseEnd_2046551] using wordTrace_append hprefix tailTrace_2046551
  have hstable : (prefixWord ++ tailWord_2046551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046551).length < 2 ^ (prefixWord ++ tailWord_2046551).sum := by decide
  have hdescent : baseEnd_2046551 < baseStart_2046551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046588 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_2046588 : Nat := 118140960795 + 2046588 * 2 ^ 59
def prefixEnd_2046588 : Nat := 4983230072969 + 3 ^ 40 * 2046588 * 2
def baseEnd_2046588 : Nat := 1050883345723943948737919

theorem tailTrace_2046588 : CollatzResearch.WordTrace tailWord_2046588 prefixEnd_2046588 1050883345723943948737919 := by
  unfold tailWord_2046588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37322598354784340124026209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49763464473045786832034945 37322598354784340124026209)
  ·
    refine ⟨27991948766088255093019657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37322598354784340124026209 27991948766088255093019657)
    ·
      refine ⟨20993961574566191319764743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27991948766088255093019657 20993961574566191319764743)
      ·
        refine ⟨31490942361849286979647115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20993961574566191319764743 31490942361849286979647115)
        ·
          refine ⟨47236413542773930469470673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31490942361849286979647115 47236413542773930469470673)
          ·
            refine ⟨35427310157080447852103005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47236413542773930469470673 35427310157080447852103005)
            ·
              refine ⟨13285241308905167944538627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35427310157080447852103005 13285241308905167944538627)
              ·
                refine ⟨19927861963357751916807941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13285241308905167944538627 19927861963357751916807941)
                ·
                  refine ⟨3736474118129578484401489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19927861963357751916807941 3736474118129578484401489)
                  ·
                    refine ⟨2802355588597183863301117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736474118129578484401489 2802355588597183863301117)
                    ·
                      refine ⟨1050883345723943948737919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802355588597183863301117 1050883345723943948737919)
                      ·
                        rfl

theorem cell23_2046588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_2046588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046588 prefixEnd_2046588 := by exact prefixLift 2046588
  have htrace : WordTrace (prefixWord ++ tailWord_2046588) baseStart_2046588 baseEnd_2046588 := by
    simpa [prefixWord, tailWord_2046588, baseEnd_2046588] using wordTrace_append hprefix tailTrace_2046588
  have hstable : (prefixWord ++ tailWord_2046588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046588).length < 2 ^ (prefixWord ++ tailWord_2046588).sum := by decide
  have hdescent : baseEnd_2046588 < baseStart_2046588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046595 : List Nat := [1, 1, 1, 3, 3, 1, 2, 6, 1, 4]
def baseStart_2046595 : Nat := 118140960795 + 2046595 * 2 ^ 59
def prefixEnd_2046595 : Nat := 4983230072969 + 3 ^ 40 * 2046595 * 2
def baseEnd_2046595 : Nat := 350295646696175140450129

theorem tailTrace_2046595 : CollatzResearch.WordTrace tailWord_2046595 prefixEnd_2046595 350295646696175140450129 := by
  unfold tailWord_2046595
  simp only [CollatzResearch.WordTrace]
  refine ⟨74645452020543320443557239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49763634680362213629038159 74645452020543320443557239)
  ·
    refine ⟨111968178030814980665335859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74645452020543320443557239 111968178030814980665335859)
    ·
      refine ⟨167952267046222470998003789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111968178030814980665335859 167952267046222470998003789)
      ·
        refine ⟨62982100142333426624251421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167952267046222470998003789 62982100142333426624251421)
        ·
          refine ⟨23618287553375034984094283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62982100142333426624251421 23618287553375034984094283)
          ·
            refine ⟨35427431330062552476141425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23618287553375034984094283 35427431330062552476141425)
            ·
              refine ⟨26570573497546914357106069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35427431330062552476141425 26570573497546914357106069)
              ·
                refine ⟨1245495632697511610489347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26570573497546914357106069 1245495632697511610489347)
                ·
                  refine ⟨1868243449046267415734021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245495632697511610489347 1868243449046267415734021)
                  ·
                    refine ⟨350295646696175140450129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868243449046267415734021 350295646696175140450129)
                    ·
                      rfl

theorem cell23_2046595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 1, 4].length) (baseStart_2046595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046595 prefixEnd_2046595 := by exact prefixLift 2046595
  have htrace : WordTrace (prefixWord ++ tailWord_2046595) baseStart_2046595 baseEnd_2046595 := by
    simpa [prefixWord, tailWord_2046595, baseEnd_2046595] using wordTrace_append hprefix tailTrace_2046595
  have hstable : (prefixWord ++ tailWord_2046595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046595).length < 2 ^ (prefixWord ++ tailWord_2046595).sum := by decide
  have hdescent : baseEnd_2046595 < baseStart_2046595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046622 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_2046622 : Nat := 118140960795 + 2046622 * 2 ^ 59
def prefixEnd_2046622 : Nat := 4983230072969 + 3 ^ 40 * 2046622 * 2
def baseEnd_2046622 : Nat := 1050900804066196815712763

theorem tailTrace_2046622 : CollatzResearch.WordTrace tailWord_2046622 prefixEnd_2046622 1050900804066196815712763 := by
  unfold tailWord_2046622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9330804598930688006848765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49764291194297002703193413 9330804598930688006848765)
  ·
    refine ⟨3499051724599008002568287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9330804598930688006848765 3499051724599008002568287)
    ·
      refine ⟨5248577586898512003852431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499051724599008002568287 5248577586898512003852431)
      ·
        refine ⟨7872866380347768005778647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248577586898512003852431 7872866380347768005778647)
        ·
          refine ⟨11809299570521652008667971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7872866380347768005778647 11809299570521652008667971)
          ·
            refine ⟨17713949355782478013001957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11809299570521652008667971 17713949355782478013001957)
            ·
              refine ⟨3321365504209214627437867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17713949355782478013001957 3321365504209214627437867)
              ·
                refine ⟨4982048256313821941156801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321365504209214627437867 4982048256313821941156801)
                ·
                  refine ⟨3736536192235366455867601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4982048256313821941156801 3736536192235366455867601)
                  ·
                    refine ⟨2802402144176524841900701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3736536192235366455867601 2802402144176524841900701)
                    ·
                      refine ⟨1050900804066196815712763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802402144176524841900701 1050900804066196815712763)
                      ·
                        rfl

theorem cell23_2046622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_2046622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046622 prefixEnd_2046622 := by exact prefixLift 2046622
  have htrace : WordTrace (prefixWord ++ tailWord_2046622) baseStart_2046622 baseEnd_2046622 := by
    simpa [prefixWord, tailWord_2046622, baseEnd_2046622] using wordTrace_append hprefix tailTrace_2046622
  have hstable : (prefixWord ++ tailWord_2046622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046622).length < 2 ^ (prefixWord ++ tailWord_2046622).sum := by decide
  have hdescent : baseEnd_2046622 < baseStart_2046622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046646 : List Nat := [5, 1, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2046646 : Nat := 118140960795 + 2046646 * 2 ^ 59
def prefixEnd_2046646 : Nat := 4983230072969 + 3 ^ 40 * 2046646 * 2
def baseEnd_2046646 : Nat := 350304375867301573937551

theorem tailTrace_2046646 : CollatzResearch.WordTrace tailWord_2046646 prefixEnd_2046646 350304375867301573937551 := by
  unfold tailWord_2046646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4665457008959909759603987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49764874762239037435775861 4665457008959909759603987)
  ·
    refine ⟨6998185513439864639405981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4665457008959909759603987 6998185513439864639405981)
    ·
      refine ⟨2624319567539949239777243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6998185513439864639405981 2624319567539949239777243)
      ·
        refine ⟨3936479351309923859665865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2624319567539949239777243 3936479351309923859665865)
        ·
          refine ⟨2952359513482442894749399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3936479351309923859665865 2952359513482442894749399)
          ·
            refine ⟨4428539270223664342124099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952359513482442894749399 4428539270223664342124099)
            ·
              refine ⟨6642808905335496513186149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4428539270223664342124099 6642808905335496513186149)
              ·
                refine ⟨1245526669750405596222403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6642808905335496513186149 1245526669750405596222403)
                ·
                  refine ⟨1868290004625608394333605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245526669750405596222403 1868290004625608394333605)
                  ·
                    refine ⟨350304375867301573937551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868290004625608394333605 350304375867301573937551)
                    ·
                      rfl

theorem cell23_2046646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2046646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046646 prefixEnd_2046646 := by exact prefixLift 2046646
  have htrace : WordTrace (prefixWord ++ tailWord_2046646) baseStart_2046646 baseEnd_2046646 := by
    simpa [prefixWord, tailWord_2046646, baseEnd_2046646] using wordTrace_append hprefix tailTrace_2046646
  have hstable : (prefixWord ++ tailWord_2046646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046646).length < 2 ^ (prefixWord ++ tailWord_2046646).sum := by decide
  have hdescent : baseEnd_2046646 < baseStart_2046646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046692 : List Nat := [2, 3, 1, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_2046692 : Nat := 118140960795 + 2046692 * 2 ^ 59
def prefixEnd_2046692 : Nat := 4983230072969 + 3 ^ 40 * 2046692 * 2
def baseEnd_2046692 : Nat := 1050936747712011541837441

theorem tailTrace_2046692 : CollatzResearch.WordTrace tailWord_2046692 prefixEnd_2046692 1050936747712011541837441 := by
  unfold tailWord_2046692
  simp only [CollatzResearch.WordTrace]
  refine ⟨37324494950595953004919165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49765993267461270673225553 37324494950595953004919165)
  ·
    refine ⟨13996685606473482376844687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37324494950595953004919165 13996685606473482376844687)
    ·
      refine ⟨20995028409710223565267031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13996685606473482376844687 20995028409710223565267031)
      ·
        refine ⟨31492542614565335347900547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20995028409710223565267031 31492542614565335347900547)
        ·
          refine ⟨47238813921848003021850821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31492542614565335347900547 47238813921848003021850821)
          ·
            refine ⟨8857277610346500566597029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47238813921848003021850821 8857277610346500566597029)
            ·
              refine ⟨1660739551939968856236943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8857277610346500566597029 1660739551939968856236943)
              ·
                refine ⟨2491109327909953284355415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1660739551939968856236943 2491109327909953284355415)
                ·
                  refine ⟨3736663991864929926533123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2491109327909953284355415 3736663991864929926533123)
                  ·
                    refine ⟨5604995987797394889799685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3736663991864929926533123 5604995987797394889799685)
                    ·
                      refine ⟨1050936747712011541837441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5604995987797394889799685 1050936747712011541837441)
                      ·
                        rfl

theorem cell23_2046692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_2046692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046692 prefixEnd_2046692 := by exact prefixLift 2046692
  have htrace : WordTrace (prefixWord ++ tailWord_2046692) baseStart_2046692 baseEnd_2046692 := by
    simpa [prefixWord, tailWord_2046692, baseEnd_2046692] using wordTrace_append hprefix tailTrace_2046692
  have hstable : (prefixWord ++ tailWord_2046692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046692).length < 2 ^ (prefixWord ++ tailWord_2046692).sum := by decide
  have hdescent : baseEnd_2046692 < baseStart_2046692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046702 : List Nat := [4, 1, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_2046702 : Nat := 118140960795 + 2046702 * 2 ^ 59
def prefixEnd_2046702 : Nat := 4983230072969 + 3 ^ 40 * 2046702 * 2
def baseEnd_2046702 : Nat := 350313960839518834237465

theorem tailTrace_2046702 : CollatzResearch.WordTrace tailWord_2046702 prefixEnd_2046702 350313960839518834237465 := by
  unfold tailWord_2046702
  simp only [CollatzResearch.WordTrace]
  refine ⟨9331169328894459714712795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49766236420770451811801573 9331169328894459714712795)
  ·
    refine ⟨13996753993341689572069193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9331169328894459714712795 13996753993341689572069193)
    ·
      refine ⟨10497565495006267179051895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13996753993341689572069193 10497565495006267179051895)
      ·
        refine ⟨15746348242509400768577843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10497565495006267179051895 15746348242509400768577843)
        ·
          refine ⟨23619522363764101152866765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15746348242509400768577843 23619522363764101152866765)
          ·
            refine ⟨8857320886411537932325037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23619522363764101152866765 8857320886411537932325037)
            ·
              refine ⟨3321495332404326724621889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8857320886411537932325037 3321495332404326724621889)
              ·
                refine ⟨2491121499303245043466417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321495332404326724621889 2491121499303245043466417)
                ·
                  refine ⟨1868341124477433782599813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2491121499303245043466417 1868341124477433782599813)
                  ·
                    refine ⟨350313960839518834237465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868341124477433782599813 350313960839518834237465)
                    ·
                      rfl

theorem cell23_2046702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_2046702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046702 prefixEnd_2046702 := by exact prefixLift 2046702
  have htrace : WordTrace (prefixWord ++ tailWord_2046702) baseStart_2046702 baseEnd_2046702 := by
    simpa [prefixWord, tailWord_2046702, baseEnd_2046702] using wordTrace_append hprefix tailTrace_2046702
  have hstable : (prefixWord ++ tailWord_2046702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046702).length < 2 ^ (prefixWord ++ tailWord_2046702).sum := by decide
  have hdescent : baseEnd_2046702 < baseStart_2046702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046722 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_2046722 : Nat := 118140960795 + 2046722 * 2 ^ 59
def prefixEnd_2046722 : Nat := 4983230072969 + 3 ^ 40 * 2046722 * 2
def baseEnd_2046722 : Nat := 1050952152131646424462303

theorem tailTrace_2046722 : CollatzResearch.WordTrace tailWord_2046722 prefixEnd_2046722 1050952152131646424462303 := by
  unfold tailWord_2046722
  simp only [CollatzResearch.WordTrace]
  refine ⟨18662521022770805283357605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49766722727388814088953613 18662521022770805283357605)
  ·
    refine ⟨3499222691769525990629551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18662521022770805283357605 3499222691769525990629551)
    ·
      refine ⟨5248834037654288985944327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3499222691769525990629551 5248834037654288985944327)
      ·
        refine ⟨7873251056481433478916491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5248834037654288985944327 7873251056481433478916491)
        ·
          refine ⟨11809876584722150218374737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7873251056481433478916491 11809876584722150218374737)
          ·
            refine ⟨8857407438541612663781053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11809876584722150218374737 8857407438541612663781053)
            ·
              refine ⟨3321527789453104748917895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8857407438541612663781053 3321527789453104748917895)
              ·
                refine ⟨4982291684179657123376843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3321527789453104748917895 4982291684179657123376843)
                ·
                  refine ⟨7473437526269485685065265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4982291684179657123376843 7473437526269485685065265)
                  ·
                    refine ⟨5605078144702114263798949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7473437526269485685065265 5605078144702114263798949)
                    ·
                      refine ⟨1050952152131646424462303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5605078144702114263798949 1050952152131646424462303)
                      ·
                        rfl

theorem cell23_2046722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_2046722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046722 prefixEnd_2046722 := by exact prefixLift 2046722
  have htrace : WordTrace (prefixWord ++ tailWord_2046722) baseStart_2046722 baseEnd_2046722 := by
    simpa [prefixWord, tailWord_2046722, baseEnd_2046722] using wordTrace_append hprefix tailTrace_2046722
  have hstable : (prefixWord ++ tailWord_2046722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046722).length < 2 ^ (prefixWord ++ tailWord_2046722).sum := by decide
  have hdescent : baseEnd_2046722 < baseStart_2046722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046743 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 1, 2, 2]
def baseStart_2046743 : Nat := 118140960795 + 2046743 * 2 ^ 59
def prefixEnd_2046743 : Nat := 4983230072969 + 3 ^ 40 * 2046743 * 2
def baseEnd_2046743 : Nat := 1050962935225390842299707

theorem tailTrace_2046743 : CollatzResearch.WordTrace tailWord_2046743 prefixEnd_2046743 1050962935225390842299707 := by
  unfold tailWord_2046743
  simp only [CollatzResearch.WordTrace]
  refine ⟨74650850024007141719944883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49767233349338094479963255 74650850024007141719944883)
  ·
    refine ⟨111976275036010712579917325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74650850024007141719944883 111976275036010712579917325)
    ·
      refine ⟨41991103138504017217468997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111976275036010712579917325 41991103138504017217468997)
      ·
        refine ⟨7873331838469503228275437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41991103138504017217468997 7873331838469503228275437)
        ·
          refine ⟨2952499439426063710603289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7873331838469503228275437 2952499439426063710603289)
          ·
            refine ⟨2214374579569547782952467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2952499439426063710603289 2214374579569547782952467)
            ·
              refine ⟨3321561869354321674428701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2214374579569547782952467 3321561869354321674428701)
              ·
                refine ⟨1245585701007870627910763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3321561869354321674428701 1245585701007870627910763)
                ·
                  refine ⟨1868378551511805941866145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245585701007870627910763 1868378551511805941866145)
                  ·
                    refine ⟨1401283913633854456399609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1868378551511805941866145 1401283913633854456399609)
                    ·
                      refine ⟨1050962935225390842299707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1401283913633854456399609 1050962935225390842299707)
                      ·
                        rfl

theorem cell23_2046743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_2046743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046743 prefixEnd_2046743 := by exact prefixLift 2046743
  have htrace : WordTrace (prefixWord ++ tailWord_2046743) baseStart_2046743 baseEnd_2046743 := by
    simpa [prefixWord, tailWord_2046743, baseEnd_2046743] using wordTrace_append hprefix tailTrace_2046743
  have hstable : (prefixWord ++ tailWord_2046743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046743).length < 2 ^ (prefixWord ++ tailWord_2046743).sum := by decide
  have hdescent : baseEnd_2046743 < baseStart_2046743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046815 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_2046815 : Nat := 118140960795 + 2046815 * 2 ^ 59
def prefixEnd_2046815 : Nat := 4983230072969 + 3 ^ 40 * 2046815 * 2
def baseEnd_2046815 : Nat := 1050999905832514560599375

theorem tailTrace_2046815 : CollatzResearch.WordTrace tailWord_2046815 prefixEnd_2046815 1050999905832514560599375 := by
  unfold tailWord_2046815
  simp only [CollatzResearch.WordTrace]
  refine ⟨74653476079746298016565899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49768984053164198677710599 74653476079746298016565899)
  ·
    refine ⟨111980214119619447024848849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74653476079746298016565899 111980214119619447024848849)
    ·
      refine ⟨83985160589714585268636637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111980214119619447024848849 83985160589714585268636637)
      ·
        refine ⟨31494435221142969475738739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83985160589714585268636637 31494435221142969475738739)
        ·
          refine ⟨47241652831714454213608109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31494435221142969475738739 47241652831714454213608109)
          ·
            refine ⟨17715619811892920330103041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47241652831714454213608109 17715619811892920330103041)
            ·
              refine ⟨13286714858919690247577281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17715619811892920330103041 13286714858919690247577281)
              ·
                refine ⟨9965036144189767685682961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13286714858919690247577281 9965036144189767685682961)
                ·
                  refine ⟨7473777108142325764262221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9965036144189767685682961 7473777108142325764262221)
                  ·
                    refine ⟨2802666415553372161598333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7473777108142325764262221 2802666415553372161598333)
                    ·
                      refine ⟨1050999905832514560599375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2802666415553372161598333 1050999905832514560599375)
                      ·
                        rfl

theorem cell23_2046815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_2046815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046815 prefixEnd_2046815 := by exact prefixLift 2046815
  have htrace : WordTrace (prefixWord ++ tailWord_2046815) baseStart_2046815 baseEnd_2046815 := by
    simpa [prefixWord, tailWord_2046815, baseEnd_2046815] using wordTrace_append hprefix tailTrace_2046815
  have hstable : (prefixWord ++ tailWord_2046815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046815).length < 2 ^ (prefixWord ++ tailWord_2046815).sum := by decide
  have hdescent : baseEnd_2046815 < baseStart_2046815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046848 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 1, 10]
def baseStart_2046848 : Nat := 118140960795 + 2046848 * 2 ^ 59
def prefixEnd_2046848 : Nat := 4983230072969 + 3 ^ 40 * 2046848 * 2
def baseEnd_2046848 : Nat := 350338950231370977162241

theorem tailTrace_2046848 : CollatzResearch.WordTrace tailWord_2046848 prefixEnd_2046848 350338950231370977162241 := by
  unfold tailWord_2046848
  simp only [CollatzResearch.WordTrace]
  refine ⟨37327339844313372326258599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49769786459084496435011465 37327339844313372326258599)
  ·
    refine ⟨55991009766470058489387899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37327339844313372326258599 55991009766470058489387899)
    ·
      refine ⟨83986514649705087734081849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55991009766470058489387899 83986514649705087734081849)
      ·
        refine ⟨62989885987278815800561387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83986514649705087734081849 62989885987278815800561387)
        ·
          refine ⟨94484828980918223700842081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62989885987278815800561387 94484828980918223700842081)
          ·
            refine ⟨70863621735688667775631561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94484828980918223700842081 70863621735688667775631561)
            ·
              refine ⟨53147716301766500831723671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70863621735688667775631561 53147716301766500831723671)
              ·
                refine ⟨79721574452649751247585507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53147716301766500831723671 79721574452649751247585507)
                ·
                  refine ⟨119582361678974626871378261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79721574452649751247585507 119582361678974626871378261)
                  ·
                    refine ⟨350338950231370977162241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 119582361678974626871378261 350338950231370977162241)
                    ·
                      rfl

theorem cell23_2046848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_2046848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046848 prefixEnd_2046848 := by exact prefixLift 2046848
  have htrace : WordTrace (prefixWord ++ tailWord_2046848) baseStart_2046848 baseEnd_2046848 := by
    simpa [prefixWord, tailWord_2046848, baseEnd_2046848] using wordTrace_append hprefix tailTrace_2046848
  have hstable : (prefixWord ++ tailWord_2046848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046848).length < 2 ^ (prefixWord ++ tailWord_2046848).sum := by decide
  have hdescent : baseEnd_2046848 < baseStart_2046848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046865 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_2046865 : Nat := 118140960795 + 2046865 * 2 ^ 59
def prefixEnd_2046865 : Nat := 4983230072969 + 3 ^ 40 * 2046865 * 2
def baseEnd_2046865 : Nat := 350341859955079788324715

theorem tailTrace_2046865 : CollatzResearch.WordTrace tailWord_2046865 prefixEnd_2046865 350341859955079788324715 := by
  unfold tailWord_2046865
  simp only [CollatzResearch.WordTrace]
  refine ⟨74655299729565156555886049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49770199819710104370590699 74655299729565156555886049)
  ·
    refine ⟨55991474797173867416914537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74655299729565156555886049 55991474797173867416914537)
    ·
      refine ⟨41993606097880400562685903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55991474797173867416914537 41993606097880400562685903)
      ·
        refine ⟨62990409146820600844028855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41993606097880400562685903 62990409146820600844028855)
        ·
          refine ⟨94485613720230901266043283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62990409146820600844028855 94485613720230901266043283)
          ·
            refine ⟨141728420580346351899064925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94485613720230901266043283 141728420580346351899064925)
            ·
              refine ⟨53148157717629881962149347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141728420580346351899064925 53148157717629881962149347)
              ·
                refine ⟨79722236576444822943224021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53148157717629881962149347 79722236576444822943224021)
                ·
                  refine ⟨1868489919760425537731813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79722236576444822943224021 1868489919760425537731813)
                  ·
                    refine ⟨350341859955079788324715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868489919760425537731813 350341859955079788324715)
                    ·
                      rfl

theorem cell23_2046865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_2046865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046865 prefixEnd_2046865 := by exact prefixLift 2046865
  have htrace : WordTrace (prefixWord ++ tailWord_2046865) baseStart_2046865 baseEnd_2046865 := by
    simpa [prefixWord, tailWord_2046865, baseEnd_2046865] using wordTrace_append hprefix tailTrace_2046865
  have hstable : (prefixWord ++ tailWord_2046865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046865).length < 2 ^ (prefixWord ++ tailWord_2046865).sum := by decide
  have hdescent : baseEnd_2046865 < baseStart_2046865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046933 : List Nat := [1, 3, 2, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2046933 : Nat := 118140960795 + 2046933 * 2 ^ 59
def prefixEnd_2046933 : Nat := 4983230072969 + 3 ^ 40 * 2046933 * 2
def baseEnd_2046933 : Nat := 350353498849915032974611

theorem tailTrace_2046933 : CollatzResearch.WordTrace tailWord_2046933 prefixEnd_2046933 350353498849915032974611 := by
  unfold tailWord_2046933
  simp only [CollatzResearch.WordTrace]
  refine ⟨74657779893318804169361453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49771853262212536112907635 74657779893318804169361453)
  ·
    refine ⟨27996667459994551563510545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74657779893318804169361453 27996667459994551563510545)
    ·
      refine ⟨20997500594995913672632909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27996667459994551563510545 20997500594995913672632909)
      ·
        refine ⟨7874062723123467627237341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20997500594995913672632909 7874062723123467627237341)
        ·
          refine ⟨2952773521171300360214003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7874062723123467627237341 2952773521171300360214003)
          ·
            refine ⟨4429160281756950540321005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952773521171300360214003 4429160281756950540321005)
            ·
              refine ⟨1660935105658856452620377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4429160281756950540321005 1660935105658856452620377)
              ·
                refine ⟨1245701329244142339465283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1660935105658856452620377 1245701329244142339465283)
                ·
                  refine ⟨1868551993866213509197925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1245701329244142339465283 1868551993866213509197925)
                  ·
                    refine ⟨350353498849915032974611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1868551993866213509197925 350353498849915032974611)
                    ·
                      rfl

theorem cell23_2046933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2046933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046933 prefixEnd_2046933 := by exact prefixLift 2046933
  have htrace : WordTrace (prefixWord ++ tailWord_2046933) baseStart_2046933 baseEnd_2046933 := by
    simpa [prefixWord, tailWord_2046933, baseEnd_2046933] using wordTrace_append hprefix tailTrace_2046933
  have hstable : (prefixWord ++ tailWord_2046933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046933).length < 2 ^ (prefixWord ++ tailWord_2046933).sum := by decide
  have hdescent : baseEnd_2046933 < baseStart_2046933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2046945 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2046945 : Nat := 118140960795 + 2046945 * 2 ^ 59
def prefixEnd_2046945 : Nat := 4983230072969 + 3 ^ 40 * 2046945 * 2
def baseEnd_2046945 : Nat := 1051066658317599051973777

theorem tailTrace_2046945 : CollatzResearch.WordTrace tailWord_2046945 prefixEnd_2046945 1051066658317599051973777 := by
  unfold tailWord_2046945
  simp only [CollatzResearch.WordTrace]
  refine ⟨74658217569275330218798289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49772145046183553479198859 74658217569275330218798289)
  ·
    refine ⟨55993663176956497664098717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74658217569275330218798289 55993663176956497664098717)
    ·
      refine ⟨20997623691358686624037019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55993663176956497664098717 20997623691358686624037019)
      ·
        refine ⟨31496435537038029936055529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20997623691358686624037019 31496435537038029936055529)
        ·
          refine ⟨23622326652778522452041647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31496435537038029936055529 23622326652778522452041647)
          ·
            refine ⟨35433489979167783678062471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23622326652778522452041647 35433489979167783678062471)
            ·
              refine ⟨53150234968751675517093707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35433489979167783678062471 53150234968751675517093707)
              ·
                refine ⟨79725352453127513275640561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53150234968751675517093707 79725352453127513275640561)
                ·
                  refine ⟨59794014339845634956730421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79725352453127513275640561 59794014339845634956730421)
                  ·
                    refine ⟨5605688844360528277193477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59794014339845634956730421 5605688844360528277193477)
                    ·
                      refine ⟨1051066658317599051973777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5605688844360528277193477 1051066658317599051973777)
                      ·
                        rfl

theorem cell23_2046945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2046945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2046945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2046945 prefixEnd_2046945 := by exact prefixLift 2046945
  have htrace : WordTrace (prefixWord ++ tailWord_2046945) baseStart_2046945 baseEnd_2046945 := by
    simpa [prefixWord, tailWord_2046945, baseEnd_2046945] using wordTrace_append hprefix tailTrace_2046945
  have hstable : (prefixWord ++ tailWord_2046945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2046945).length < 2 ^ (prefixWord ++ tailWord_2046945).sum := by decide
  have hdescent : baseEnd_2046945 < baseStart_2046945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2046945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
