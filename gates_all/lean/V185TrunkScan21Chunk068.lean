import V185TrunkScan21Chunk067

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_822948 : List Nat := [2, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_822948 : Nat := 118140960795 + 822948 * 2 ^ 59
def prefixEnd_822948 : Nat := 4983230072969 + 3 ^ 40 * 822948 * 2
def baseEnd_822948 : Nat := 187807945625045087051261

theorem tailTrace_822948 : CollatzResearch.WordTrace tailWord_822948 prefixEnd_822948 187807945625045087051261 := by
  unfold tailWord_822948
  simp only [CollatzResearch.WordTrace]
  refine ⟨15007689711303709586942749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20010252948404946115923665 15007689711303709586942749)
  ·
    refine ⟨5627883641738891095103531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15007689711303709586942749 5627883641738891095103531)
    ·
      refine ⟨8441825462608336642655297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5627883641738891095103531 8441825462608336642655297)
      ·
        refine ⟨6331369096956252481991473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8441825462608336642655297 6331369096956252481991473)
        ·
          refine ⟨4748526822717189361493605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6331369096956252481991473 4748526822717189361493605)
          ·
            refine ⟨890348779259473005280051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4748526822717189361493605 890348779259473005280051)
            ·
              refine ⟨1335523168889209507920077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890348779259473005280051 1335523168889209507920077)
              ·
                refine ⟨500821188333453565470029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335523168889209507920077 500821188333453565470029)
                ·
                  refine ⟨187807945625045087051261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500821188333453565470029 187807945625045087051261)
                  ·
                    rfl

theorem cell21_822948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_822948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822948 prefixEnd_822948 := by exact prefixLift 822948
  have htrace : WordTrace (prefixWord ++ tailWord_822948) baseStart_822948 baseEnd_822948 := by
    simpa [prefixWord, tailWord_822948, baseEnd_822948] using wordTrace_append hprefix tailTrace_822948
  have hstable : (prefixWord ++ tailWord_822948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822948).length < 2 ^ (prefixWord ++ tailWord_822948).sum := by decide
  have hdescent : baseEnd_822948 < baseStart_822948 := by decide
  rcases family_descends (prefixWord ++ tailWord_822948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_822965 : List Nat := [1, 3, 3, 3, 2, 1, 3, 2, 3]
def baseStart_822965 : Nat := 118140960795 + 822965 * 2 ^ 59
def prefixEnd_822965 : Nat := 4983230072969 + 3 ^ 40 * 822965 * 2
def baseEnd_822965 : Nat := 187811825256656835267893

theorem tailTrace_822965 : CollatzResearch.WordTrace tailWord_822965 prefixEnd_822965 187811825256656835267893 := by
  unfold tailWord_822965
  simp only [CollatzResearch.WordTrace]
  refine ⟨30015999463545831077254349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20010666309030554051502899 30015999463545831077254349)
  ·
    refine ⟨11255999798829686653970381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30015999463545831077254349 11255999798829686653970381)
    ·
      refine ⟨4220999924561132495238893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11255999798829686653970381 4220999924561132495238893)
      ·
        refine ⟨1582874971710424685714585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4220999924561132495238893 1582874971710424685714585)
        ·
          refine ⟨1187156228782818514285939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1582874971710424685714585 1187156228782818514285939)
          ·
            refine ⟨1780734343174227771428909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187156228782818514285939 1780734343174227771428909)
            ·
              refine ⟨667775378690335414285841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1780734343174227771428909 667775378690335414285841)
              ·
                refine ⟨500831534017751560714381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667775378690335414285841 500831534017751560714381)
                ·
                  refine ⟨187811825256656835267893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500831534017751560714381 187811825256656835267893)
                  ·
                    rfl

theorem cell21_822965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_822965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_822965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_822965 prefixEnd_822965 := by exact prefixLift 822965
  have htrace : WordTrace (prefixWord ++ tailWord_822965) baseStart_822965 baseEnd_822965 := by
    simpa [prefixWord, tailWord_822965, baseEnd_822965] using wordTrace_append hprefix tailTrace_822965
  have hstable : (prefixWord ++ tailWord_822965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_822965).length < 2 ^ (prefixWord ++ tailWord_822965).sum := by decide
  have hdescent : baseEnd_822965 < baseStart_822965 := by decide
  rcases family_descends (prefixWord ++ tailWord_822965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823021 : List Nat := [1, 5, 1, 2, 1, 2, 1, 4, 4]
def baseStart_823021 : Nat := 118140960795 + 823021 * 2 ^ 59
def prefixEnd_823021 : Nat := 4983230072969 + 3 ^ 40 * 823021 * 2
def baseEnd_823021 : Nat := 187824605219613182334445

theorem tailTrace_823021 : CollatzResearch.WordTrace tailWord_823021 prefixEnd_823021 187824605219613182334445 := by
  unfold tailWord_823021
  simp only [CollatzResearch.WordTrace]
  refine ⟨30018041951342952641292917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20012027967561968427528611 30018041951342952641292917)
  ·
    refine ⟨2814191432938401810121211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30018041951342952641292917 2814191432938401810121211)
    ·
      refine ⟨4221287149407602715181817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2814191432938401810121211 4221287149407602715181817)
      ·
        refine ⟨3165965362055702036386363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4221287149407602715181817 3165965362055702036386363)
        ·
          refine ⟨4748948043083553054579545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3165965362055702036386363 4748948043083553054579545)
          ·
            refine ⟨3561711032312664790934659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4748948043083553054579545 3561711032312664790934659)
            ·
              refine ⟨5342566548468997186401989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3561711032312664790934659 5342566548468997186401989)
              ·
                refine ⟨1001731227837936972450373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5342566548468997186401989 1001731227837936972450373)
                ·
                  refine ⟨187824605219613182334445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1001731227837936972450373 187824605219613182334445)
                  ·
                    rfl

theorem cell21_823021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_823021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823021 prefixEnd_823021 := by exact prefixLift 823021
  have htrace : WordTrace (prefixWord ++ tailWord_823021) baseStart_823021 baseEnd_823021 := by
    simpa [prefixWord, tailWord_823021, baseEnd_823021] using wordTrace_append hprefix tailTrace_823021
  have hstable : (prefixWord ++ tailWord_823021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823021).length < 2 ^ (prefixWord ++ tailWord_823021).sum := by decide
  have hdescent : baseEnd_823021 < baseStart_823021 := by decide
  rcases family_descends (prefixWord ++ tailWord_823021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823111 : List Nat := [1, 1, 4, 1, 2, 1, 6, 5]
def baseStart_823111 : Nat := 118140960795 + 823111 * 2 ^ 59
def prefixEnd_823111 : Nat := 4983230072969 + 3 ^ 40 * 823111 * 2
def baseEnd_823111 : Nat := 62615048148597675278087

theorem tailTrace_823111 : CollatzResearch.WordTrace tailWord_823111 prefixEnd_823111 62615048148597675278087 := by
  unfold tailWord_823111
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021324521016898012069187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20014216347344598674712791 30021324521016898012069187)
  ·
    refine ⟨45031986781525347018103781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30021324521016898012069187 45031986781525347018103781)
    ·
      refine ⟨8443497521536002565894459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45031986781525347018103781 8443497521536002565894459)
      ·
        refine ⟨12665246282304003848841689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8443497521536002565894459 12665246282304003848841689)
        ·
          refine ⟨9498934711728002886631267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12665246282304003848841689 9498934711728002886631267)
          ·
            refine ⟨14248402067592004329946901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9498934711728002886631267 14248402067592004329946901)
            ·
              refine ⟨667893846918375202966261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14248402067592004329946901 667893846918375202966261)
              ·
                refine ⟨62615048148597675278087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 667893846918375202966261 62615048148597675278087)
                ·
                  rfl

theorem cell21_823111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 5].length) (baseStart_823111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823111 prefixEnd_823111 := by exact prefixLift 823111
  have htrace : WordTrace (prefixWord ++ tailWord_823111) baseStart_823111 baseEnd_823111 := by
    simpa [prefixWord, tailWord_823111, baseEnd_823111] using wordTrace_append hprefix tailTrace_823111
  have hstable : (prefixWord ++ tailWord_823111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823111).length < 2 ^ (prefixWord ++ tailWord_823111).sum := by decide
  have hdescent : baseEnd_823111 < baseStart_823111 := by decide
  rcases family_descends (prefixWord ++ tailWord_823111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823117 : List Nat := [1, 6, 1, 2, 1, 3, 1, 3, 3]
def baseStart_823117 : Nat := 118140960795 + 823117 * 2 ^ 59
def prefixEnd_823117 : Nat := 4983230072969 + 3 ^ 40 * 823117 * 2
def baseEnd_823117 : Nat := 187846513727538348734249

theorem tailTrace_823117 : CollatzResearch.WordTrace tailWord_823117 prefixEnd_823117 187846513727538348734249 := by
  unfold tailWord_823117
  simp only [CollatzResearch.WordTrace]
  refine ⟨30021543358995161036787605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20014362239330107357858403 30021543358995161036787605)
  ·
    refine ⟨1407259844952898173599419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30021543358995161036787605 1407259844952898173599419)
    ·
      refine ⟨2110889767429347260399129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407259844952898173599419 2110889767429347260399129)
      ·
        refine ⟨1583167325572010445299347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2110889767429347260399129 1583167325572010445299347)
        ·
          refine ⟨2374750988358015667949021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1583167325572010445299347 2374750988358015667949021)
          ·
            refine ⟨890531620634255875480883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2374750988358015667949021 890531620634255875480883)
            ·
              refine ⟨1335797430951383813221325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890531620634255875480883 1335797430951383813221325)
              ·
                refine ⟨500924036606768929957997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335797430951383813221325 500924036606768929957997)
                ·
                  refine ⟨187846513727538348734249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500924036606768929957997 187846513727538348734249)
                  ·
                    rfl

theorem cell21_823117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_823117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823117 prefixEnd_823117 := by exact prefixLift 823117
  have htrace : WordTrace (prefixWord ++ tailWord_823117) baseStart_823117 baseEnd_823117 := by
    simpa [prefixWord, tailWord_823117, baseEnd_823117] using wordTrace_append hprefix tailTrace_823117
  have hstable : (prefixWord ++ tailWord_823117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823117).length < 2 ^ (prefixWord ++ tailWord_823117).sum := by decide
  have hdescent : baseEnd_823117 < baseStart_823117 := by decide
  rcases family_descends (prefixWord ++ tailWord_823117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823246 : List Nat := [4, 1, 1, 1, 2, 2, 10]
def baseStart_823246 : Nat := 118140960795 + 823246 * 2 ^ 59
def prefixEnd_823246 : Nat := 4983230072969 + 3 ^ 40 * 823246 * 2
def baseEnd_823246 : Nat := 20875105920562532342665

theorem tailTrace_823246 : CollatzResearch.WordTrace tailWord_823246 prefixEnd_823246 20875105920562532342665 := by
  unfold tailWord_823246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753281046940977008529199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20017498917018544045489061 3753281046940977008529199)
  ·
    refine ⟨5629921570411465512793799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3753281046940977008529199 5629921570411465512793799)
    ·
      refine ⟨8444882355617198269190699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5629921570411465512793799 8444882355617198269190699)
      ·
        refine ⟨12667323533425797403786049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8444882355617198269190699 12667323533425797403786049)
        ·
          refine ⟨9500492650069348052839537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12667323533425797403786049 9500492650069348052839537)
          ·
            refine ⟨7125369487552011039629653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9500492650069348052839537 7125369487552011039629653)
            ·
              refine ⟨20875105920562532342665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7125369487552011039629653 20875105920562532342665)
              ·
                rfl

theorem cell21_823246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 10].length) (baseStart_823246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823246 prefixEnd_823246 := by exact prefixLift 823246
  have htrace : WordTrace (prefixWord ++ tailWord_823246) baseStart_823246 baseEnd_823246 := by
    simpa [prefixWord, tailWord_823246, baseEnd_823246] using wordTrace_append hprefix tailTrace_823246
  have hstable : (prefixWord ++ tailWord_823246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823246).length < 2 ^ (prefixWord ++ tailWord_823246).sum := by decide
  have hdescent : baseEnd_823246 < baseStart_823246 := by decide
  rcases family_descends (prefixWord ++ tailWord_823246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823291 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 6]
def baseStart_823291 : Nat := 118140960795 + 823291 * 2 ^ 59
def prefixEnd_823291 : Nat := 4983230072969 + 3 ^ 40 * 823291 * 2
def baseEnd_823291 : Nat := 187886222898152712833893

theorem tailTrace_823291 : CollatzResearch.WordTrace tailWord_823291 prefixEnd_823291 187886222898152712833893 := by
  unfold tailWord_823291
  simp only [CollatzResearch.WordTrace]
  refine ⟨30027889660364788753621727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20018593106909859169081151 30027889660364788753621727)
  ·
    refine ⟨45041834490547183130432591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30027889660364788753621727 45041834490547183130432591)
    ·
      refine ⟨67562751735820774695648887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45041834490547183130432591 67562751735820774695648887)
      ·
        refine ⟨101344127603731162043473331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67562751735820774695648887 101344127603731162043473331)
        ·
          refine ⟨152016191405596743065209997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101344127603731162043473331 152016191405596743065209997)
          ·
            refine ⟨57006071777098778649453749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152016191405596743065209997 57006071777098778649453749)
            ·
              refine ⟨5344319229103010498386289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57006071777098778649453749 5344319229103010498386289)
              ·
                refine ⟨4008239421827257873789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5344319229103010498386289 4008239421827257873789717)
                ·
                  refine ⟨187886222898152712833893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4008239421827257873789717 187886222898152712833893)
                  ·
                    rfl

theorem cell21_823291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_823291 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823291 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823291 prefixEnd_823291 := by exact prefixLift 823291
  have htrace : WordTrace (prefixWord ++ tailWord_823291) baseStart_823291 baseEnd_823291 := by
    simpa [prefixWord, tailWord_823291, baseEnd_823291] using wordTrace_append hprefix tailTrace_823291
  have hstable : (prefixWord ++ tailWord_823291).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823291).length < 2 ^ (prefixWord ++ tailWord_823291).sum := by decide
  have hdescent : baseEnd_823291 < baseStart_823291 := by decide
  rcases family_descends (prefixWord ++ tailWord_823291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823308 : List Nat := [2, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_823308 : Nat := 118140960795 + 823308 * 2 ^ 59
def prefixEnd_823308 : Nat := 4983230072969 + 3 ^ 40 * 823308 * 2
def baseEnd_823308 : Nat := 187890102529764461050525

theorem tailTrace_823308 : CollatzResearch.WordTrace tailWord_823308 prefixEnd_823308 187890102529764461050525 := by
  unfold tailWord_823308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15014254850651600328495289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20019006467535467104660385 15014254850651600328495289)
  ·
    refine ⟨11260691137988700246371467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15014254850651600328495289 11260691137988700246371467)
    ·
      refine ⟨16891036706983050369557201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11260691137988700246371467 16891036706983050369557201)
      ·
        refine ⟨12668277530237287777167901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16891036706983050369557201 12668277530237287777167901)
        ·
          refine ⟨4750604073838982916437963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12668277530237287777167901 4750604073838982916437963)
          ·
            refine ⟨7125906110758474374656945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4750604073838982916437963 7125906110758474374656945)
            ·
              refine ⟨5344429583068855780992709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7125906110758474374656945 5344429583068855780992709)
              ·
                refine ⟨1002080546825410458936133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5344429583068855780992709 1002080546825410458936133)
                ·
                  refine ⟨187890102529764461050525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002080546825410458936133 187890102529764461050525)
                  ·
                    rfl

theorem cell21_823308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_823308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823308 prefixEnd_823308 := by exact prefixLift 823308
  have htrace : WordTrace (prefixWord ++ tailWord_823308) baseStart_823308 baseEnd_823308 := by
    simpa [prefixWord, tailWord_823308, baseEnd_823308] using wordTrace_append hprefix tailTrace_823308
  have hstable : (prefixWord ++ tailWord_823308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823308).length < 2 ^ (prefixWord ++ tailWord_823308).sum := by decide
  have hdescent : baseEnd_823308 < baseStart_823308 := by decide
  rcases family_descends (prefixWord ++ tailWord_823308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823322 : List Nat := [3, 1, 1, 3, 1, 3, 1, 8]
def baseStart_823322 : Nat := 118140960795 + 823322 * 2 ^ 59
def prefixEnd_823322 : Nat := 4983230072969 + 3 ^ 40 * 823322 * 2
def baseEnd_823322 : Nat := 62631099173501182605721

theorem tailTrace_823322 : CollatzResearch.WordTrace tailWord_823322 prefixEnd_823322 62631099173501182605721 := by
  unfold tailWord_823322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7507255080813120262000055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20019346882168320698666813 7507255080813120262000055)
  ·
    refine ⟨11260882621219680393000083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7507255080813120262000055 11260882621219680393000083)
    ·
      refine ⟨16891323931829520589500125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11260882621219680393000083 16891323931829520589500125)
      ·
        refine ⟨6334246474436070221062547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16891323931829520589500125 6334246474436070221062547)
        ·
          refine ⟨9501369711654105331593821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6334246474436070221062547 9501369711654105331593821)
          ·
            refine ⟨3563013641870289499347683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9501369711654105331593821 3563013641870289499347683)
            ·
              refine ⟨5344520462805434249021525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563013641870289499347683 5344520462805434249021525)
              ·
                refine ⟨62631099173501182605721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5344520462805434249021525 62631099173501182605721)
                ·
                  rfl

theorem cell21_823322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_823322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823322 prefixEnd_823322 := by exact prefixLift 823322
  have htrace : WordTrace (prefixWord ++ tailWord_823322) baseStart_823322 baseEnd_823322 := by
    simpa [prefixWord, tailWord_823322, baseEnd_823322] using wordTrace_append hprefix tailTrace_823322
  have hstable : (prefixWord ++ tailWord_823322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823322).length < 2 ^ (prefixWord ++ tailWord_823322).sum := by decide
  have hdescent : baseEnd_823322 < baseStart_823322 := by decide
  rcases family_descends (prefixWord ++ tailWord_823322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823325 : List Nat := [1, 4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_823325 : Nat := 118140960795 + 823325 * 2 ^ 59
def prefixEnd_823325 : Nat := 4983230072969 + 3 ^ 40 * 823325 * 2
def baseEnd_823325 : Nat := 187893982161376209267157

theorem tailTrace_823325 : CollatzResearch.WordTrace tailWord_823325 prefixEnd_823325 187893982161376209267157 := by
  unfold tailWord_823325
  simp only [CollatzResearch.WordTrace]
  refine ⟨30029129742241612560359429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20019419828161075040239619 30029129742241612560359429)
  ·
    refine ⟨5630461826670302355067393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30029129742241612560359429 5630461826670302355067393)
    ·
      refine ⟨4222846370002726766300545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5630461826670302355067393 4222846370002726766300545)
      ·
        refine ⟨3167134777502045074725409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4222846370002726766300545 3167134777502045074725409)
        ·
          refine ⟨2375351083126533806044057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167134777502045074725409 2375351083126533806044057)
          ·
            refine ⟨1781513312344900354533043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375351083126533806044057 1781513312344900354533043)
            ·
              refine ⟨2672269968517350531799565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781513312344900354533043 2672269968517350531799565)
              ·
                refine ⟨1002101238194006449424837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672269968517350531799565 1002101238194006449424837)
                ·
                  refine ⟨187893982161376209267157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002101238194006449424837 187893982161376209267157)
                  ·
                    rfl

theorem cell21_823325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_823325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823325 prefixEnd_823325 := by exact prefixLift 823325
  have htrace : WordTrace (prefixWord ++ tailWord_823325) baseStart_823325 baseEnd_823325 := by
    simpa [prefixWord, tailWord_823325, baseEnd_823325] using wordTrace_append hprefix tailTrace_823325
  have hstable : (prefixWord ++ tailWord_823325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823325).length < 2 ^ (prefixWord ++ tailWord_823325).sum := by decide
  have hdescent : baseEnd_823325 < baseStart_823325 := by decide
  rcases family_descends (prefixWord ++ tailWord_823325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823384 : List Nat := [2, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_823384 : Nat := 118140960795 + 823384 * 2 ^ 59
def prefixEnd_823384 : Nat := 4983230072969 + 3 ^ 40 * 823384 * 2
def baseEnd_823384 : Nat := 187907446765205217783703

theorem tailTrace_823384 : CollatzResearch.WordTrace tailWord_823384 prefixEnd_823384 187907446765205217783703 := by
  unfold tailWord_823384
  simp only [CollatzResearch.WordTrace]
  refine ⟨15015640824513932818378603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20020854432685243757838137 15015640824513932818378603)
  ·
    refine ⟨22523461236770899227567905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15015640824513932818378603 22523461236770899227567905)
    ·
      refine ⟨16892595927578174420675929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22523461236770899227567905 16892595927578174420675929)
      ·
        refine ⟨12669446945683630815506947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16892595927578174420675929 12669446945683630815506947)
        ·
          refine ⟨19004170418525446223260421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12669446945683630815506947 19004170418525446223260421)
          ·
            refine ⟨3563281953473521166861329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19004170418525446223260421 3563281953473521166861329)
            ·
              refine ⟨2672461465105140875145997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3563281953473521166861329 2672461465105140875145997)
              ·
                refine ⟨1002173049414427828179749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2672461465105140875145997 1002173049414427828179749)
                ·
                  refine ⟨187907446765205217783703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002173049414427828179749 187907446765205217783703)
                  ·
                    rfl

theorem cell21_823384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_823384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823384 prefixEnd_823384 := by exact prefixLift 823384
  have htrace : WordTrace (prefixWord ++ tailWord_823384) baseStart_823384 baseEnd_823384 := by
    simpa [prefixWord, tailWord_823384, baseEnd_823384] using wordTrace_append hprefix tailTrace_823384
  have hstable : (prefixWord ++ tailWord_823384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823384).length < 2 ^ (prefixWord ++ tailWord_823384).sum := by decide
  have hdescent : baseEnd_823384 < baseStart_823384 := by decide
  rcases family_descends (prefixWord ++ tailWord_823384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823390 : List Nat := [4, 4, 1, 1, 2, 1, 3, 5]
def baseStart_823390 : Nat := 118140960795 + 823390 * 2 ^ 59
def prefixEnd_823390 : Nat := 4983230072969 + 3 ^ 40 * 823390 * 2
def baseEnd_823390 : Nat := 62636272015650180227897

theorem tailTrace_823390 : CollatzResearch.WordTrace tailWord_823390 prefixEnd_823390 62636272015650180227897 := by
  unfold tailWord_823390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753937560875766082684453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20021000324670752440983749 3753937560875766082684453)
  ·
    refine ⟨703863292664206140503335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3753937560875766082684453 703863292664206140503335)
    ·
      refine ⟨1055794938996309210755003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 703863292664206140503335 1055794938996309210755003)
      ·
        refine ⟨1583692408494463816132505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055794938996309210755003 1583692408494463816132505)
        ·
          refine ⟨1187769306370847862099379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583692408494463816132505 1187769306370847862099379)
          ·
            refine ⟨1781653959556271793149069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187769306370847862099379 1781653959556271793149069)
            ·
              refine ⟨668120234833601922430901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1781653959556271793149069 668120234833601922430901)
              ·
                refine ⟨62636272015650180227897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 668120234833601922430901 62636272015650180227897)
                ·
                  rfl

theorem cell21_823390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_823390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823390 prefixEnd_823390 := by exact prefixLift 823390
  have htrace : WordTrace (prefixWord ++ tailWord_823390) baseStart_823390 baseEnd_823390 := by
    simpa [prefixWord, tailWord_823390, baseEnd_823390] using wordTrace_append hprefix tailTrace_823390
  have hstable : (prefixWord ++ tailWord_823390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823390).length < 2 ^ (prefixWord ++ tailWord_823390).sum := by decide
  have hdescent : baseEnd_823390 < baseStart_823390 := by decide
  rcases family_descends (prefixWord ++ tailWord_823390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823429 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 5]
def baseStart_823429 : Nat := 118140960795 + 823429 * 2 ^ 59
def prefixEnd_823429 : Nat := 4983230072969 + 3 ^ 40 * 823429 * 2
def baseEnd_823429 : Nat := 187917716378295139533611

theorem tailTrace_823429 : CollatzResearch.WordTrace tailWord_823429 prefixEnd_823429 187917716378295139533611 := by
  unfold tailWord_823429
  simp only [CollatzResearch.WordTrace]
  refine ⟨30032922933864838322145341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20021948622576558881430227 30032922933864838322145341)
  ·
    refine ⟨11262346100199314370804503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30032922933864838322145341 11262346100199314370804503)
    ·
      refine ⟨16893519150298971556206755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11262346100199314370804503 16893519150298971556206755)
      ·
        refine ⟨25340278725448457334310133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16893519150298971556206755 25340278725448457334310133)
        ·
          refine ⟨2375651130510792875091575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25340278725448457334310133 2375651130510792875091575)
          ·
            refine ⟨3563476695766189312637363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2375651130510792875091575 3563476695766189312637363)
            ·
              refine ⟨5345215043649283968956045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3563476695766189312637363 5345215043649283968956045)
              ·
                refine ⟨2004455641368481488358517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5345215043649283968956045 2004455641368481488358517)
                ·
                  refine ⟨187917716378295139533611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2004455641368481488358517 187917716378295139533611)
                  ·
                    rfl

theorem cell21_823429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_823429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823429 prefixEnd_823429 := by exact prefixLift 823429
  have htrace : WordTrace (prefixWord ++ tailWord_823429) baseStart_823429 baseEnd_823429 := by
    simpa [prefixWord, tailWord_823429, baseEnd_823429] using wordTrace_append hprefix tailTrace_823429
  have hstable : (prefixWord ++ tailWord_823429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823429).length < 2 ^ (prefixWord ++ tailWord_823429).sum := by decide
  have hdescent : baseEnd_823429 < baseStart_823429 := by decide
  rcases family_descends (prefixWord ++ tailWord_823429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823719 : List Nat := [1, 1, 6, 1, 1, 4, 1, 6]
def baseStart_823719 : Nat := 118140960795 + 823719 * 2 ^ 59
def prefixEnd_823719 : Nat := 4983230072969 + 3 ^ 40 * 823719 * 2
def baseEnd_823719 : Nat := 62661299443106359899895

theorem tailTrace_823719 : CollatzResearch.WordTrace tailWord_823719 prefixEnd_823719 62661299443106359899895 := by
  unfold tailWord_823719
  simp only [CollatzResearch.WordTrace]
  refine ⟨30043500102814217850202211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20029000068542811900134807 30043500102814217850202211)
  ·
    refine ⟨45065250154221326775303317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30043500102814217850202211 45065250154221326775303317)
    ·
      refine ⟨2112433600979124692592343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45065250154221326775303317 2112433600979124692592343)
      ·
        refine ⟨3168650401468687038888515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2112433600979124692592343 3168650401468687038888515)
        ·
          refine ⟨4752975602203030558332773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3168650401468687038888515 4752975602203030558332773)
          ·
            refine ⟨891182925413068229687395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4752975602203030558332773 891182925413068229687395)
            ·
              refine ⟨1336774388119602344531093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891182925413068229687395 1336774388119602344531093)
              ·
                refine ⟨62661299443106359899895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1336774388119602344531093 62661299443106359899895)
                ·
                  rfl

theorem cell21_823719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 6].length) (baseStart_823719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823719 prefixEnd_823719 := by exact prefixLift 823719
  have htrace : WordTrace (prefixWord ++ tailWord_823719) baseStart_823719 baseEnd_823719 := by
    simpa [prefixWord, tailWord_823719, baseEnd_823719] using wordTrace_append hprefix tailTrace_823719
  have hstable : (prefixWord ++ tailWord_823719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823719).length < 2 ^ (prefixWord ++ tailWord_823719).sum := by decide
  have hdescent : baseEnd_823719 < baseStart_823719 := by decide
  rcases family_descends (prefixWord ++ tailWord_823719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823764 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_823764 : Nat := 118140960795 + 823764 * 2 ^ 59
def prefixEnd_823764 : Nat := 4983230072969 + 3 ^ 40 * 823764 * 2
def baseEnd_823764 : Nat := 187994167942409001449593

theorem tailTrace_823764 : CollatzResearch.WordTrace tailWord_823764 prefixEnd_823764 187994167942409001449593 := by
  unfold tailWord_823764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15022570693825595267795173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20030094258434127023726897 15022570693825595267795173)
  ·
    refine ⟨2816732005092299112711595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15022570693825595267795173 2816732005092299112711595)
    ·
      refine ⟨4225098007638448669067393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2816732005092299112711595 4225098007638448669067393)
      ·
        refine ⟨3168823505728836501800545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4225098007638448669067393 3168823505728836501800545)
        ·
          refine ⟨2376617629296627376350409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3168823505728836501800545 2376617629296627376350409)
          ·
            refine ⟨1782463221972470532262807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2376617629296627376350409 1782463221972470532262807)
            ·
              refine ⟨2673694832958705798394211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1782463221972470532262807 2673694832958705798394211)
              ·
                refine ⟨4010542249438058697591317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2673694832958705798394211 4010542249438058697591317)
                ·
                  refine ⟨187994167942409001449593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4010542249438058697591317 187994167942409001449593)
                  ·
                    rfl

theorem cell21_823764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_823764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823764 prefixEnd_823764 := by exact prefixLift 823764
  have htrace : WordTrace (prefixWord ++ tailWord_823764) baseStart_823764 baseEnd_823764 := by
    simpa [prefixWord, tailWord_823764, baseEnd_823764] using wordTrace_append hprefix tailTrace_823764
  have hstable : (prefixWord ++ tailWord_823764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823764).length < 2 ^ (prefixWord ++ tailWord_823764).sum := by decide
  have hdescent : baseEnd_823764 < baseStart_823764 := by decide
  rcases family_descends (prefixWord ++ tailWord_823764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823792 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 5]
def baseStart_823792 : Nat := 118140960795 + 823792 * 2 ^ 59
def prefixEnd_823792 : Nat := 4983230072969 + 3 ^ 40 * 823792 * 2
def baseEnd_823792 : Nat := 188000557923887174982869

theorem tailTrace_823792 : CollatzResearch.WordTrace tailWord_823792 prefixEnd_823792 188000557923887174982869 := by
  unfold tailWord_823792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15023081315774875658804815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20030775087699834211739753 15023081315774875658804815)
  ·
    refine ⟨22534621973662313488207223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15023081315774875658804815 22534621973662313488207223)
    ·
      refine ⟨33801932960493470232310835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22534621973662313488207223 33801932960493470232310835)
      ·
        refine ⟨50702899440740205348466253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33801932960493470232310835 50702899440740205348466253)
        ·
          refine ⟨19013587290277577005674845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50702899440740205348466253 19013587290277577005674845)
          ·
            refine ⟨7130095233854091377128067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19013587290277577005674845 7130095233854091377128067)
            ·
              refine ⟨10695142850781137065692101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7130095233854091377128067 10695142850781137065692101)
              ·
                refine ⟨2005339284521463199817269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10695142850781137065692101 2005339284521463199817269)
                ·
                  refine ⟨188000557923887174982869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2005339284521463199817269 188000557923887174982869)
                  ·
                    rfl

theorem cell21_823792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 5].length) (baseStart_823792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823792 prefixEnd_823792 := by exact prefixLift 823792
  have htrace : WordTrace (prefixWord ++ tailWord_823792) baseStart_823792 baseEnd_823792 := by
    simpa [prefixWord, tailWord_823792, baseEnd_823792] using wordTrace_append hprefix tailTrace_823792
  have hstable : (prefixWord ++ tailWord_823792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823792).length < 2 ^ (prefixWord ++ tailWord_823792).sum := by decide
  have hdescent : baseEnd_823792 < baseStart_823792 := by decide
  rcases family_descends (prefixWord ++ tailWord_823792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_823933 : List Nat := [1, 4, 1, 1, 5, 2, 1, 2, 4]
def baseStart_823933 : Nat := 118140960795 + 823933 * 2 ^ 59
def prefixEnd_823933 : Nat := 4983230072969 + 3 ^ 40 * 823933 * 2
def baseEnd_823933 : Nat := 188032736044902263132581

theorem tailTrace_823933 : CollatzResearch.WordTrace tailWord_823933 prefixEnd_823933 188032736044902263132581 := by
  unfold tailWord_823933
  simp only [CollatzResearch.WordTrace]
  refine ⟨30051305324038932398492453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20034203549359288265661635 30051305324038932398492453)
  ·
    refine ⟨5634619748257299824717335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30051305324038932398492453 5634619748257299824717335)
    ·
      refine ⟨8451929622385949737076003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5634619748257299824717335 8451929622385949737076003)
      ·
        refine ⟨12677894433578924605614005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8451929622385949737076003 12677894433578924605614005)
        ·
          refine ⟨1188552603148024181776313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12677894433578924605614005 1188552603148024181776313)
          ·
            refine ⟨891414452361018136332235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188552603148024181776313 891414452361018136332235)
            ·
              refine ⟨1337121678541527204498353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891414452361018136332235 1337121678541527204498353)
              ·
                refine ⟨1002841258906145403373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1337121678541527204498353 1002841258906145403373765)
                ·
                  refine ⟨188032736044902263132581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002841258906145403373765 188032736044902263132581)
                  ·
                    rfl

theorem cell21_823933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_823933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_823933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_823933 prefixEnd_823933 := by exact prefixLift 823933
  have htrace : WordTrace (prefixWord ++ tailWord_823933) baseStart_823933 baseEnd_823933 := by
    simpa [prefixWord, tailWord_823933, baseEnd_823933] using wordTrace_append hprefix tailTrace_823933
  have hstable : (prefixWord ++ tailWord_823933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_823933).length < 2 ^ (prefixWord ++ tailWord_823933).sum := by decide
  have hdescent : baseEnd_823933 < baseStart_823933 := by decide
  rcases family_descends (prefixWord ++ tailWord_823933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824054 : List Nat := [5, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_824054 : Nat := 118140960795 + 824054 * 2 ^ 59
def prefixEnd_824054 : Nat := 4983230072969 + 3 ^ 40 * 824054 * 2
def baseEnd_824054 : Nat := 188060349893432941615667

theorem tailTrace_824054 : CollatzResearch.WordTrace tailWord_824054 prefixEnd_824054 188060349893432941615667 := by
  unfold tailWord_824054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878482409787535628977951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20037145704400380042431477 1878482409787535628977951)
  ·
    refine ⟨2817723614681303443466927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1878482409787535628977951 2817723614681303443466927)
    ·
      refine ⟨4226585422021955165200391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2817723614681303443466927 4226585422021955165200391)
      ·
        refine ⟨6339878133032932747800587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4226585422021955165200391 6339878133032932747800587)
        ·
          refine ⟨9509817199549399121700881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6339878133032932747800587 9509817199549399121700881)
          ·
            refine ⟨7132362899662049341275661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9509817199549399121700881 7132362899662049341275661)
            ·
              refine ⟨2674636087373268502978373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7132362899662049341275661 2674636087373268502978373)
              ·
                refine ⟨501494266382487844308445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2674636087373268502978373 501494266382487844308445)
                ·
                  refine ⟨188060349893432941615667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501494266382487844308445 188060349893432941615667)
                  ·
                    rfl

theorem cell21_824054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_824054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824054 prefixEnd_824054 := by exact prefixLift 824054
  have htrace : WordTrace (prefixWord ++ tailWord_824054) baseStart_824054 baseEnd_824054 := by
    simpa [prefixWord, tailWord_824054, baseEnd_824054] using wordTrace_append hprefix tailTrace_824054
  have hstable : (prefixWord ++ tailWord_824054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824054).length < 2 ^ (prefixWord ++ tailWord_824054).sum := by decide
  have hdescent : baseEnd_824054 < baseStart_824054 := by decide
  rcases family_descends (prefixWord ++ tailWord_824054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824113 : List Nat := [1, 2, 2, 3, 2, 1, 1, 6, 3]
def baseStart_824113 : Nat := 118140960795 + 824113 * 2 ^ 59
def prefixEnd_824113 : Nat := 4983230072969 + 3 ^ 40 * 824113 * 2
def baseEnd_824113 : Nat := 188073814497261950132213

theorem tailTrace_824113 : CollatzResearch.WordTrace tailWord_824113 prefixEnd_824113 188073814497261950132213 := by
  unfold tailWord_824113
  simp only [CollatzResearch.WordTrace]
  refine ⟨30057870463386823140044993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20038580308924548760029995 30057870463386823140044993)
  ·
    refine ⟨22543402847540117355033745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30057870463386823140044993 22543402847540117355033745)
    ·
      refine ⟨16907552135655088016275309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22543402847540117355033745 16907552135655088016275309)
      ·
        refine ⟨6340332050870658006103241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16907552135655088016275309 6340332050870658006103241)
        ·
          refine ⟨4755249038152993504577431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6340332050870658006103241 4755249038152993504577431)
          ·
            refine ⟨7132873557229490256866147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4755249038152993504577431 7132873557229490256866147)
            ·
              refine ⟨10699310335844235385299221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7132873557229490256866147 10699310335844235385299221)
              ·
                refine ⟨501530171992698533685901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10699310335844235385299221 501530171992698533685901)
                ·
                  refine ⟨188073814497261950132213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501530171992698533685901 188073814497261950132213)
                  ·
                    rfl

theorem cell21_824113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 6, 3].length) (baseStart_824113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824113 prefixEnd_824113 := by exact prefixLift 824113
  have htrace : WordTrace (prefixWord ++ tailWord_824113) baseStart_824113 baseEnd_824113 := by
    simpa [prefixWord, tailWord_824113, baseEnd_824113] using wordTrace_append hprefix tailTrace_824113
  have hstable : (prefixWord ++ tailWord_824113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824113).length < 2 ^ (prefixWord ++ tailWord_824113).sum := by decide
  have hdescent : baseEnd_824113 < baseStart_824113 := by decide
  rcases family_descends (prefixWord ++ tailWord_824113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824223 : List Nat := [1, 1, 2, 5, 2, 3, 2, 2, 3]
def baseStart_824223 : Nat := 118140960795 + 824223 * 2 ^ 59
def prefixEnd_824223 : Nat := 4983230072969 + 3 ^ 40 * 824223 * 2
def baseEnd_824223 : Nat := 188098917995926203298655

theorem tailTrace_824223 : CollatzResearch.WordTrace tailWord_824223 prefixEnd_824223 188098917995926203298655 := by
  unfold tailWord_824223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30061882492988311926549323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20041254995325541284366215 30061882492988311926549323)
  ·
    refine ⟨45092823739482467889823985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30061882492988311926549323 45092823739482467889823985)
    ·
      refine ⟨33819617804611850917367989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45092823739482467889823985 33819617804611850917367989)
      ·
        refine ⟨3170589169182361023503249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33819617804611850917367989 3170589169182361023503249)
        ·
          refine ⟨2377941876886770767627437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3170589169182361023503249 2377941876886770767627437)
          ·
            refine ⟨891728203832539037860289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2377941876886770767627437 891728203832539037860289)
            ·
              refine ⟨668796152874404278395217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 891728203832539037860289 668796152874404278395217)
              ·
                refine ⟨501597114655803208796413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 668796152874404278395217 501597114655803208796413)
                ·
                  refine ⟨188098917995926203298655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501597114655803208796413 188098917995926203298655)
                  ·
                    rfl

theorem cell21_824223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3].length) (baseStart_824223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824223 prefixEnd_824223 := by exact prefixLift 824223
  have htrace : WordTrace (prefixWord ++ tailWord_824223) baseStart_824223 baseEnd_824223 := by
    simpa [prefixWord, tailWord_824223, baseEnd_824223] using wordTrace_append hprefix tailTrace_824223
  have hstable : (prefixWord ++ tailWord_824223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824223).length < 2 ^ (prefixWord ++ tailWord_824223).sum := by decide
  have hdescent : baseEnd_824223 < baseStart_824223 := by decide
  rcases family_descends (prefixWord ++ tailWord_824223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824248 : List Nat := [2, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_824248 : Nat := 118140960795 + 824248 * 2 ^ 59
def prefixEnd_824248 : Nat := 4983230072969 + 3 ^ 40 * 824248 * 2
def baseEnd_824248 : Nat := 188104623336531715381937

theorem tailTrace_824248 : CollatzResearch.WordTrace tailWord_824248 prefixEnd_824248 188104623336531715381937 := by
  unfold tailWord_824248
  simp only [CollatzResearch.WordTrace]
  refine ⟨15031397158948870598104699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20041862878598494130806265 15031397158948870598104699)
  ·
    refine ⟨22547095738423305897157049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15031397158948870598104699 22547095738423305897157049)
    ·
      refine ⟨16910321803817479422867787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22547095738423305897157049 16910321803817479422867787)
      ·
        refine ⟨25365482705726219134301681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16910321803817479422867787 25365482705726219134301681)
        ·
          refine ⟨19024112029294664350726261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25365482705726219134301681 19024112029294664350726261)
          ·
            refine ⟨1783510502746374782880587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19024112029294664350726261 1783510502746374782880587)
            ·
              refine ⟨2675265754119562174320881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783510502746374782880587 2675265754119562174320881)
              ·
                refine ⟨2006449315589671630740661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2675265754119562174320881 2006449315589671630740661)
                ·
                  refine ⟨188104623336531715381937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2006449315589671630740661 188104623336531715381937)
                  ·
                    rfl

theorem cell21_824248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_824248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824248 prefixEnd_824248 := by exact prefixLift 824248
  have htrace : WordTrace (prefixWord ++ tailWord_824248) baseStart_824248 baseEnd_824248 := by
    simpa [prefixWord, tailWord_824248, baseEnd_824248] using wordTrace_append hprefix tailTrace_824248
  have hstable : (prefixWord ++ tailWord_824248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824248).length < 2 ^ (prefixWord ++ tailWord_824248).sum := by decide
  have hdescent : baseEnd_824248 < baseStart_824248 := by decide
  rcases family_descends (prefixWord ++ tailWord_824248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824310 : List Nat := [5, 1, 1, 1, 3, 2, 1, 7]
def baseStart_824310 : Nat := 118140960795 + 824310 * 2 ^ 59
def prefixEnd_824310 : Nat := 4983230072969 + 3 ^ 40 * 824310 * 2
def baseEnd_824310 : Nat := 62706257527077795116159

theorem tailTrace_824310 : CollatzResearch.WordTrace tailWord_824310 prefixEnd_824310 62706257527077795116159 := by
  unfold tailWord_824310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1879065977729570361560399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20043370429115417189977589 1879065977729570361560399)
  ·
    refine ⟨2818598966594355542340599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1879065977729570361560399 2818598966594355542340599)
    ·
      refine ⟨4227898449891533313510899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2818598966594355542340599 4227898449891533313510899)
      ·
        refine ⟨6341847674837299970266349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4227898449891533313510899 6341847674837299970266349)
        ·
          refine ⟨2378192878063987488849881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6341847674837299970266349 2378192878063987488849881)
          ·
            refine ⟨1783644658547990616637411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2378192878063987488849881 1783644658547990616637411)
            ·
              refine ⟨2675466987821985924956117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783644658547990616637411 2675466987821985924956117)
              ·
                refine ⟨62706257527077795116159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2675466987821985924956117 62706257527077795116159)
                ·
                  rfl

theorem cell21_824310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_824310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824310 prefixEnd_824310 := by exact prefixLift 824310
  have htrace : WordTrace (prefixWord ++ tailWord_824310) baseStart_824310 baseEnd_824310 := by
    simpa [prefixWord, tailWord_824310, baseEnd_824310] using wordTrace_append hprefix tailTrace_824310
  have hstable : (prefixWord ++ tailWord_824310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824310).length < 2 ^ (prefixWord ++ tailWord_824310).sum := by decide
  have hdescent : baseEnd_824310 < baseStart_824310 := by decide
  rcases family_descends (prefixWord ++ tailWord_824310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824341 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 5]
def baseStart_824341 : Nat := 118140960795 + 824341 * 2 ^ 59
def prefixEnd_824341 : Nat := 4983230072969 + 3 ^ 40 * 824341 * 2
def baseEnd_824341 : Nat := 188125847203584220331747

theorem tailTrace_824341 : CollatzResearch.WordTrace tailWord_824341 prefixEnd_824341 188125847203584220331747 := by
  unfold tailWord_824341
  simp only [CollatzResearch.WordTrace]
  refine ⟨30066186306560818079344877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20044124204373878719563251 30066186306560818079344877)
  ·
    refine ⟨11274819864960306779754329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30066186306560818079344877 11274819864960306779754329)
    ·
      refine ⟨8456114898720230084815747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11274819864960306779754329 8456114898720230084815747)
      ·
        refine ⟨12684172348080345127223621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8456114898720230084815747 12684172348080345127223621)
        ·
          refine ⟨2378282315265064711354429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12684172348080345127223621 2378282315265064711354429)
          ·
            refine ⟨891855868224399266757911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2378282315265064711354429 891855868224399266757911)
            ·
              refine ⟨1337783802336598900136867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891855868224399266757911 1337783802336598900136867)
              ·
                refine ⟨2006675703504898350205301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337783802336598900136867 2006675703504898350205301)
                ·
                  refine ⟨188125847203584220331747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2006675703504898350205301 188125847203584220331747)
                  ·
                    rfl

theorem cell21_824341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_824341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824341 prefixEnd_824341 := by exact prefixLift 824341
  have htrace : WordTrace (prefixWord ++ tailWord_824341) baseStart_824341 baseEnd_824341 := by
    simpa [prefixWord, tailWord_824341, baseEnd_824341] using wordTrace_append hprefix tailTrace_824341
  have hstable : (prefixWord ++ tailWord_824341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824341).length < 2 ^ (prefixWord ++ tailWord_824341).sum := by decide
  have hdescent : baseEnd_824341 < baseStart_824341 := by decide
  rcases family_descends (prefixWord ++ tailWord_824341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824355 : List Nat := [1, 1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_824355 : Nat := 118140960795 + 824355 * 2 ^ 59
def prefixEnd_824355 : Nat := 4983230072969 + 3 ^ 40 * 824355 * 2
def baseEnd_824355 : Nat := 188129042194323307098385

theorem tailTrace_824355 : CollatzResearch.WordTrace tailWord_824355 prefixEnd_824355 188129042194323307098385 := by
  unfold tailWord_824355
  simp only [CollatzResearch.WordTrace]
  refine ⟨30066696928510098470354519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20044464619006732313569679 30066696928510098470354519)
  ·
    refine ⟨45100045392765147705531779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30066696928510098470354519 45100045392765147705531779)
    ·
      refine ⟨67650068089147721558297669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45100045392765147705531779 67650068089147721558297669)
      ·
        refine ⟨12684387766715197792180813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67650068089147721558297669 12684387766715197792180813)
        ·
          refine ⟨4756645412518199172067805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12684387766715197792180813 4756645412518199172067805)
          ·
            refine ⟨1783742029694324689525427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4756645412518199172067805 1783742029694324689525427)
            ·
              refine ⟨2675613044541487034288141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1783742029694324689525427 2675613044541487034288141)
              ·
                refine ⟨1003354891703057637858053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2675613044541487034288141 1003354891703057637858053)
                ·
                  refine ⟨188129042194323307098385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003354891703057637858053 188129042194323307098385)
                  ·
                    rfl

theorem cell21_824355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_824355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824355 prefixEnd_824355 := by exact prefixLift 824355
  have htrace : WordTrace (prefixWord ++ tailWord_824355) baseStart_824355 baseEnd_824355 := by
    simpa [prefixWord, tailWord_824355, baseEnd_824355] using wordTrace_append hprefix tailTrace_824355
  have hstable : (prefixWord ++ tailWord_824355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824355).length < 2 ^ (prefixWord ++ tailWord_824355).sum := by decide
  have hdescent : baseEnd_824355 < baseStart_824355 := by decide
  rcases family_descends (prefixWord ++ tailWord_824355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824476 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 5]
def baseStart_824476 : Nat := 118140960795 + 824476 * 2 ^ 59
def prefixEnd_824476 : Nat := 4983230072969 + 3 ^ 40 * 824476 * 2
def baseEnd_824476 : Nat := 188156656042853985581471

theorem tailTrace_824476 : CollatzResearch.WordTrace tailWord_824476 prefixEnd_824476 188156656042853985581471 := by
  unfold tailWord_824476
  simp only [CollatzResearch.WordTrace]
  refine ⟨15035555080535868067754641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20047406774047824090339521 15035555080535868067754641)
  ·
    refine ⟨11276666310401901050815981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15035555080535868067754641 11276666310401901050815981)
    ·
      refine ⟨4228749866400712894055993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11276666310401901050815981 4228749866400712894055993)
      ·
        refine ⟨3171562399800534670541995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4228749866400712894055993 3171562399800534670541995)
        ·
          refine ⟨4757343599700802005812993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3171562399800534670541995 4757343599700802005812993)
          ·
            refine ⟨3568007699775601504359745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4757343599700802005812993 3568007699775601504359745)
            ·
              refine ⟨2676005774831701128269809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3568007699775601504359745 2676005774831701128269809)
              ·
                refine ⟨2007004331123775846202357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2676005774831701128269809 2007004331123775846202357)
                ·
                  refine ⟨188156656042853985581471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2007004331123775846202357 188156656042853985581471)
                  ·
                    rfl

theorem cell21_824476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_824476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824476 prefixEnd_824476 := by exact prefixLift 824476
  have htrace : WordTrace (prefixWord ++ tailWord_824476) baseStart_824476 baseEnd_824476 := by
    simpa [prefixWord, tailWord_824476, baseEnd_824476] using wordTrace_append hprefix tailTrace_824476
  have hstable : (prefixWord ++ tailWord_824476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824476).length < 2 ^ (prefixWord ++ tailWord_824476).sum := by decide
  have hdescent : baseEnd_824476 < baseStart_824476 := by decide
  rcases family_descends (prefixWord ++ tailWord_824476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824479 : List Nat := [1, 1, 2, 6, 2, 2, 2, 5]
def baseStart_824479 : Nat := 118140960795 + 824479 * 2 ^ 59
def prefixEnd_824479 : Nat := 4983230072969 + 3 ^ 40 * 824479 * 2
def baseEnd_824479 : Nat := 62719113561242215677155

theorem tailTrace_824479 : CollatzResearch.WordTrace tailWord_824479 prefixEnd_824479 62719113561242215677155 := by
  unfold tailWord_824479
  simp only [CollatzResearch.WordTrace]
  refine ⟨30071219580060867647868491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20047479720040578431912327 30071219580060867647868491)
  ·
    refine ⟨45106829370091301471802737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30071219580060867647868491 45106829370091301471802737)
    ·
      refine ⟨33830122027568476103852053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45106829370091301471802737 33830122027568476103852053)
      ·
        refine ⟨1585786970042272317368065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33830122027568476103852053 1585786970042272317368065)
        ·
          refine ⟨1189340227531704238026049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1585786970042272317368065 1189340227531704238026049)
          ·
            refine ⟨892005170648778178519537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189340227531704238026049 892005170648778178519537)
            ·
              refine ⟨669003877986583633889653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892005170648778178519537 669003877986583633889653)
              ·
                refine ⟨62719113561242215677155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 669003877986583633889653 62719113561242215677155)
                ·
                  rfl

theorem cell21_824479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 5].length) (baseStart_824479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824479 prefixEnd_824479 := by exact prefixLift 824479
  have htrace : WordTrace (prefixWord ++ tailWord_824479) baseStart_824479 baseEnd_824479 := by
    simpa [prefixWord, tailWord_824479, baseEnd_824479] using wordTrace_append hprefix tailTrace_824479
  have hstable : (prefixWord ++ tailWord_824479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824479).length < 2 ^ (prefixWord ++ tailWord_824479).sum := by decide
  have hdescent : baseEnd_824479 < baseStart_824479 := by decide
  rcases family_descends (prefixWord ++ tailWord_824479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824535 : List Nat := [1, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_824535 : Nat := 118140960795 + 824535 * 2 ^ 59
def prefixEnd_824535 : Nat := 4983230072969 + 3 ^ 40 * 824535 * 2
def baseEnd_824535 : Nat := 188170120646682994098017

theorem tailTrace_824535 : CollatzResearch.WordTrace tailWord_824535 prefixEnd_824535 188170120646682994098017 := by
  unfold tailWord_824535
  simp only [CollatzResearch.WordTrace]
  refine ⟨30073262067857989211907059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20048841378571992807938039 30073262067857989211907059)
  ·
    refine ⟨45109893101786983817860589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30073262067857989211907059 45109893101786983817860589)
    ·
      refine ⟨16916209913170118931697721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45109893101786983817860589 16916209913170118931697721)
      ·
        refine ⟨12687157434877589198773291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16916209913170118931697721 12687157434877589198773291)
        ·
          refine ⟨19030736152316383798159937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12687157434877589198773291 19030736152316383798159937)
          ·
            refine ⟨14273052114237287848619953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19030736152316383798159937 14273052114237287848619953)
            ·
              refine ⟨10704789085677965886464965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14273052114237287848619953 10704789085677965886464965)
              ·
                refine ⟨2007147953564618603712181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10704789085677965886464965 2007147953564618603712181)
                ·
                  refine ⟨188170120646682994098017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2007147953564618603712181 188170120646682994098017)
                  ·
                    rfl

theorem cell21_824535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_824535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824535 prefixEnd_824535 := by exact prefixLift 824535
  have htrace : WordTrace (prefixWord ++ tailWord_824535) baseStart_824535 baseEnd_824535 := by
    simpa [prefixWord, tailWord_824535, baseEnd_824535] using wordTrace_append hprefix tailTrace_824535
  have hstable : (prefixWord ++ tailWord_824535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824535).length < 2 ^ (prefixWord ++ tailWord_824535).sum := by decide
  have hdescent : baseEnd_824535 < baseStart_824535 := by decide
  rcases family_descends (prefixWord ++ tailWord_824535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824656 : List Nat := [2, 1, 1, 1, 1, 5, 3, 7]
def baseStart_824656 : Nat := 118140960795 + 824656 * 2 ^ 59
def prefixEnd_824656 : Nat := 4983230072969 + 3 ^ 40 * 824656 * 2
def baseEnd_824656 : Nat := 62732578165071224193701

theorem tailTrace_824656 : CollatzResearch.WordTrace tailWord_824656 prefixEnd_824656 62732578165071224193701 := by
  unfold tailWord_824656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15038837650209813438530911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20051783533613084584707881 15038837650209813438530911)
  ·
    refine ⟨22558256475314720157796367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15038837650209813438530911 22558256475314720157796367)
    ·
      refine ⟨33837384712972080236694551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22558256475314720157796367 33837384712972080236694551)
      ·
        refine ⟨50756077069458120355041827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33837384712972080236694551 50756077069458120355041827)
        ·
          refine ⟨76134115604187180532562741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50756077069458120355041827 76134115604187180532562741)
          ·
            refine ⟨7137573337892548174927757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76134115604187180532562741 7137573337892548174927757)
            ·
              refine ⟨2676590001709705565597909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7137573337892548174927757 2676590001709705565597909)
              ·
                refine ⟨62732578165071224193701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2676590001709705565597909 62732578165071224193701)
                ·
                  rfl

theorem cell21_824656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 7].length) (baseStart_824656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824656 prefixEnd_824656 := by exact prefixLift 824656
  have htrace : WordTrace (prefixWord ++ tailWord_824656) baseStart_824656 baseEnd_824656 := by
    simpa [prefixWord, tailWord_824656, baseEnd_824656] using wordTrace_append hprefix tailTrace_824656
  have hstable : (prefixWord ++ tailWord_824656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824656).length < 2 ^ (prefixWord ++ tailWord_824656).sum := by decide
  have hdescent : baseEnd_824656 < baseStart_824656 := by decide
  rcases family_descends (prefixWord ++ tailWord_824656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824693 : List Nat := [1, 3, 4, 1, 3, 2, 2, 1, 4]
def baseStart_824693 : Nat := 118140960795 + 824693 * 2 ^ 59
def prefixEnd_824693 : Nat := 4983230072969 + 3 ^ 40 * 824693 * 2
def baseEnd_824693 : Nat := 188206178399309830464361

theorem tailTrace_824693 : CollatzResearch.WordTrace tailWord_824693 prefixEnd_824693 188206178399309830464361 := by
  unfold tailWord_824693
  simp only [CollatzResearch.WordTrace]
  refine ⟨30079024801285582196158733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20052683200857054797439155 30079024801285582196158733)
  ·
    refine ⟨11279634300482093323559525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30079024801285582196158733 11279634300482093323559525)
    ·
      refine ⟨2114931431340392498167411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11279634300482093323559525 2114931431340392498167411)
      ·
        refine ⟨3172397147010588747251117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2114931431340392498167411 3172397147010588747251117)
        ·
          refine ⟨1189648930128970780219169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3172397147010588747251117 1189648930128970780219169)
          ·
            refine ⟨892236697596728085164377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1189648930128970780219169 892236697596728085164377)
            ·
              refine ⟨669177523197546063873283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892236697596728085164377 669177523197546063873283)
              ·
                refine ⟨1003766284796319095809925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669177523197546063873283 1003766284796319095809925)
                ·
                  refine ⟨188206178399309830464361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003766284796319095809925 188206178399309830464361)
                  ·
                    rfl

theorem cell21_824693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_824693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824693 prefixEnd_824693 := by exact prefixLift 824693
  have htrace : WordTrace (prefixWord ++ tailWord_824693) baseStart_824693 baseEnd_824693 := by
    simpa [prefixWord, tailWord_824693, baseEnd_824693] using wordTrace_append hprefix tailTrace_824693
  have hstable : (prefixWord ++ tailWord_824693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824693).length < 2 ^ (prefixWord ++ tailWord_824693).sum := by decide
  have hdescent : baseEnd_824693 < baseStart_824693 := by decide
  rcases family_descends (prefixWord ++ tailWord_824693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824735 : List Nat := [1, 1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_824735 : Nat := 118140960795 + 824735 * 2 ^ 59
def prefixEnd_824735 : Nat := 4983230072969 + 3 ^ 40 * 824735 * 2
def baseEnd_824735 : Nat := 188215763371527090764275

theorem tailTrace_824735 : CollatzResearch.WordTrace tailWord_824735 prefixEnd_824735 188215763371527090764275 := by
  unfold tailWord_824735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30080556667133423369187659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20053704444755615579458439 30080556667133423369187659)
  ·
    refine ⟨45120835000700135053781489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30080556667133423369187659 45120835000700135053781489)
    ·
      refine ⟨33840626250525101290336117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45120835000700135053781489 33840626250525101290336117)
      ·
        refine ⟨3172558710986728245969011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33840626250525101290336117 3172558710986728245969011)
        ·
          refine ⟨4758838066480092368953517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172558710986728245969011 4758838066480092368953517)
          ·
            refine ⟨1784564274930034638357569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4758838066480092368953517 1784564274930034638357569)
            ·
              refine ⟨1338423206197525978768177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1784564274930034638357569 1338423206197525978768177)
              ·
                refine ⟨1003817404648144484076133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338423206197525978768177 1003817404648144484076133)
                ·
                  refine ⟨188215763371527090764275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003817404648144484076133 188215763371527090764275)
                  ·
                    rfl

theorem cell21_824735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_824735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824735 prefixEnd_824735 := by exact prefixLift 824735
  have htrace : WordTrace (prefixWord ++ tailWord_824735) baseStart_824735 baseEnd_824735 := by
    simpa [prefixWord, tailWord_824735, baseEnd_824735] using wordTrace_append hprefix tailTrace_824735
  have hstable : (prefixWord ++ tailWord_824735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824735).length < 2 ^ (prefixWord ++ tailWord_824735).sum := by decide
  have hdescent : baseEnd_824735 < baseStart_824735 := by decide
  rcases family_descends (prefixWord ++ tailWord_824735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824738 : List Nat := [3, 3, 1, 2, 1, 2, 4, 2, 3]
def baseStart_824738 : Nat := 118140960795 + 824738 * 2 ^ 59
def prefixEnd_824738 : Nat := 4983230072969 + 3 ^ 40 * 824738 * 2
def baseEnd_824738 : Nat := 188216448012399752214269

theorem tailTrace_824738 : CollatzResearch.WordTrace tailWord_824738 prefixEnd_824738 188216448012399752214269 := by
  unfold tailWord_824738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520166521530638720386717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20053777390748369921031245 7520166521530638720386717)
  ·
    refine ⟨2820062445573989520145019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7520166521530638720386717 2820062445573989520145019)
    ·
      refine ⟨4230093668360984280217529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820062445573989520145019 4230093668360984280217529)
      ·
        refine ⟨3172570251270738210163147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4230093668360984280217529 3172570251270738210163147)
        ·
          refine ⟨4758855376906107315244721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172570251270738210163147 4758855376906107315244721)
          ·
            refine ⟨3569141532679580486433541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4758855376906107315244721 3569141532679580486433541)
            ·
              refine ⟨669214037377421341206289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3569141532679580486433541 669214037377421341206289)
              ·
                refine ⟨501910528033066005904717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669214037377421341206289 501910528033066005904717)
                ·
                  refine ⟨188216448012399752214269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501910528033066005904717 188216448012399752214269)
                  ·
                    rfl

theorem cell21_824738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_824738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824738 prefixEnd_824738 := by exact prefixLift 824738
  have htrace : WordTrace (prefixWord ++ tailWord_824738) baseStart_824738 baseEnd_824738 := by
    simpa [prefixWord, tailWord_824738, baseEnd_824738] using wordTrace_append hprefix tailTrace_824738
  have hstable : (prefixWord ++ tailWord_824738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824738).length < 2 ^ (prefixWord ++ tailWord_824738).sum := by decide
  have hdescent : baseEnd_824738 < baseStart_824738 := by decide
  rcases family_descends (prefixWord ++ tailWord_824738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824777 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_824777 : Nat := 118140960795 + 824777 * 2 ^ 59
def prefixEnd_824777 : Nat := 4983230072969 + 3 ^ 40 * 824777 * 2
def baseEnd_824777 : Nat := 188225348343744351064189

theorem tailTrace_824777 : CollatzResearch.WordTrace tailWord_824777 prefixEnd_824777 188225348343744351064189 := by
  unfold tailWord_824777
  simp only [CollatzResearch.WordTrace]
  refine ⟨30082088532981264542216585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20054725688654176361477723 30082088532981264542216585)
  ·
    refine ⟨22561566399735948406662439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30082088532981264542216585 22561566399735948406662439)
    ·
      refine ⟨33842349599603922609993659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22561566399735948406662439 33842349599603922609993659)
      ·
        refine ⟨50763524399405883914990489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33842349599603922609993659 50763524399405883914990489)
        ·
          refine ⟨38072643299554412936242867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50763524399405883914990489 38072643299554412936242867)
          ·
            refine ⟨57108964949331619404364301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38072643299554412936242867 57108964949331619404364301)
            ·
              refine ⟨21415861855999357276636613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57108964949331619404364301 21415861855999357276636613)
              ·
                refine ⟨4015474097999879489369365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21415861855999357276636613 4015474097999879489369365)
                ·
                  refine ⟨188225348343744351064189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4015474097999879489369365 188225348343744351064189)
                  ·
                    rfl

theorem cell21_824777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_824777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824777 prefixEnd_824777 := by exact prefixLift 824777
  have htrace : WordTrace (prefixWord ++ tailWord_824777) baseStart_824777 baseEnd_824777 := by
    simpa [prefixWord, tailWord_824777, baseEnd_824777] using wordTrace_append hprefix tailTrace_824777
  have hstable : (prefixWord ++ tailWord_824777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824777).length < 2 ^ (prefixWord ++ tailWord_824777).sum := by decide
  have hdescent : baseEnd_824777 < baseStart_824777 := by decide
  rcases family_descends (prefixWord ++ tailWord_824777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824794 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 6]
def baseStart_824794 : Nat := 118140960795 + 824794 * 2 ^ 59
def prefixEnd_824794 : Nat := 4983230072969 + 3 ^ 40 * 824794 * 2
def baseEnd_824794 : Nat := 188229227975356099280821

theorem tailTrace_824794 : CollatzResearch.WordTrace tailWord_824794 prefixEnd_824794 188229227975356099280821 := by
  unfold tailWord_824794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7520677143479919111396359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20055139049279784297056957 7520677143479919111396359)
  ·
    refine ⟨11281015715219878667094539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7520677143479919111396359 11281015715219878667094539)
    ·
      refine ⟨16921523572829818000641809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11281015715219878667094539 16921523572829818000641809)
      ·
        refine ⟨12691142679622363500481357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16921523572829818000641809 12691142679622363500481357)
        ·
          refine ⟨4759178504858386312680509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12691142679622363500481357 4759178504858386312680509)
          ·
            refine ⟨1784691939321894867255191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4759178504858386312680509 1784691939321894867255191)
            ·
              refine ⟨2677037908982842300882787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784691939321894867255191 2677037908982842300882787)
              ·
                refine ⟨4015556863474263451324181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677037908982842300882787 4015556863474263451324181)
                ·
                  refine ⟨188229227975356099280821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4015556863474263451324181 188229227975356099280821)
                  ·
                    rfl

theorem cell21_824794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_824794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824794 prefixEnd_824794 := by exact prefixLift 824794
  have htrace : WordTrace (prefixWord ++ tailWord_824794) baseStart_824794 baseEnd_824794 := by
    simpa [prefixWord, tailWord_824794, baseEnd_824794] using wordTrace_append hprefix tailTrace_824794
  have hstable : (prefixWord ++ tailWord_824794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824794).length < 2 ^ (prefixWord ++ tailWord_824794).sum := by decide
  have hdescent : baseEnd_824794 < baseStart_824794 := by decide
  rcases family_descends (prefixWord ++ tailWord_824794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824797 : List Nat := [1, 4, 3, 1, 1, 2, 2, 4, 3]
def baseStart_824797 : Nat := 118140960795 + 824797 * 2 ^ 59
def prefixEnd_824797 : Nat := 4983230072969 + 3 ^ 40 * 824797 * 2
def baseEnd_824797 : Nat := 188229912616228760730815

theorem tailTrace_824797 : CollatzResearch.WordTrace tailWord_824797 prefixEnd_824797 188229912616228760730815 := by
  unfold tailWord_824797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30082817992908807957944645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20055211995272538638629763 30082817992908807957944645)
  ·
    refine ⟨5640528373670401492114621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30082817992908807957944645 5640528373670401492114621)
    ·
      refine ⟨2115198140126400559542983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5640528373670401492114621 2115198140126400559542983)
      ·
        refine ⟨3172797210189600839314475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2115198140126400559542983 3172797210189600839314475)
        ·
          refine ⟨4759195815284401258971713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3172797210189600839314475 4759195815284401258971713)
          ·
            refine ⟨3569396861463300944228785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4759195815284401258971713 3569396861463300944228785)
            ·
              refine ⟨2677047646097475708171589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569396861463300944228785 2677047646097475708171589)
              ·
                refine ⟨501946433643276695282173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2677047646097475708171589 501946433643276695282173)
                ·
                  refine ⟨188229912616228760730815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501946433643276695282173 188229912616228760730815)
                  ·
                    rfl

theorem cell21_824797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_824797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824797 prefixEnd_824797 := by exact prefixLift 824797
  have htrace : WordTrace (prefixWord ++ tailWord_824797) baseStart_824797 baseEnd_824797 := by
    simpa [prefixWord, tailWord_824797, baseEnd_824797] using wordTrace_append hprefix tailTrace_824797
  have hstable : (prefixWord ++ tailWord_824797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824797).length < 2 ^ (prefixWord ++ tailWord_824797).sum := by decide
  have hdescent : baseEnd_824797 < baseStart_824797 := by decide
  rcases family_descends (prefixWord ++ tailWord_824797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824808 : List Nat := [2, 1, 4, 1, 1, 2, 2, 8]
def baseStart_824808 : Nat := 118140960795 + 824808 * 2 ^ 59
def prefixEnd_824808 : Nat := 4983230072969 + 3 ^ 40 * 824808 * 2
def baseEnd_824808 : Nat := 62744140988698395349153

theorem tailTrace_824808 : CollatzResearch.WordTrace tailWord_824808 prefixEnd_824808 62744140988698395349153 := by
  unfold tailWord_824808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15041609597934478418297539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20055479463912637891063385 15041609597934478418297539)
  ·
    refine ⟨22562414396901717627446309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15041609597934478418297539 22562414396901717627446309)
    ·
      refine ⟨4230452699419072055146183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22562414396901717627446309 4230452699419072055146183)
      ·
        refine ⟨6345679049128608082719275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4230452699419072055146183 6345679049128608082719275)
        ·
          refine ⟨9518518573692912124078913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6345679049128608082719275 9518518573692912124078913)
          ·
            refine ⟨7138888930269684093059185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9518518573692912124078913 7138888930269684093059185)
            ·
              refine ⟨5354166697702263069794389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7138888930269684093059185 5354166697702263069794389)
              ·
                refine ⟨62744140988698395349153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5354166697702263069794389 62744140988698395349153)
                ·
                  rfl

theorem cell21_824808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_824808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824808 prefixEnd_824808 := by exact prefixLift 824808
  have htrace : WordTrace (prefixWord ++ tailWord_824808) baseStart_824808 baseEnd_824808 := by
    simpa [prefixWord, tailWord_824808, baseEnd_824808] using wordTrace_append hprefix tailTrace_824808
  have hstable : (prefixWord ++ tailWord_824808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824808).length < 2 ^ (prefixWord ++ tailWord_824808).sum := by decide
  have hdescent : baseEnd_824808 < baseStart_824808 := by decide
  rcases family_descends (prefixWord ++ tailWord_824808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824862 : List Nat := [4, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_824862 : Nat := 118140960795 + 824862 * 2 ^ 59
def prefixEnd_824862 : Nat := 4983230072969 + 3 ^ 40 * 824862 * 2
def baseEnd_824862 : Nat := 188244746501803092147349

theorem tailTrace_824862 : CollatzResearch.WordTrace tailWord_824862 prefixEnd_824862 188244746501803092147349 := by
  unfold tailWord_824862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760648592209165507382605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20056792491782216039373893 3760648592209165507382605)
  ·
    refine ⟨1410243222078437065268477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3760648592209165507382605 1410243222078437065268477)
    ·
      refine ⟨528841208279413899475679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1410243222078437065268477 528841208279413899475679)
      ·
        refine ⟨793261812419120849213519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528841208279413899475679 793261812419120849213519)
        ·
          refine ⟨1189892718628681273820279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793261812419120849213519 1189892718628681273820279)
          ·
            refine ⟨1784839077943021910730419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1189892718628681273820279 1784839077943021910730419)
            ·
              refine ⟨2677258616914532866095629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1784839077943021910730419 2677258616914532866095629)
              ·
                refine ⟨1003971981342949824785861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2677258616914532866095629 1003971981342949824785861)
                ·
                  refine ⟨188244746501803092147349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1003971981342949824785861 188244746501803092147349)
                  ·
                    rfl

theorem cell21_824862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_824862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824862 prefixEnd_824862 := by exact prefixLift 824862
  have htrace : WordTrace (prefixWord ++ tailWord_824862) baseStart_824862 baseEnd_824862 := by
    simpa [prefixWord, tailWord_824862, baseEnd_824862] using wordTrace_append hprefix tailTrace_824862
  have hstable : (prefixWord ++ tailWord_824862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824862).length < 2 ^ (prefixWord ++ tailWord_824862).sum := by decide
  have hdescent : baseEnd_824862 < baseStart_824862 := by decide
  rcases family_descends (prefixWord ++ tailWord_824862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824949 : List Nat := [1, 3, 4, 2, 1, 1, 1, 5, 3]
def baseStart_824949 : Nat := 118140960795 + 824949 * 2 ^ 59
def prefixEnd_824949 : Nat := 4983230072969 + 3 ^ 40 * 824949 * 2
def baseEnd_824949 : Nat := 188264601087110274197171

theorem tailTrace_824949 : CollatzResearch.WordTrace tailWord_824949 prefixEnd_824949 188264601087110274197171 := by
  unfold tailWord_824949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30088361888358137917477901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20058907925572091944985267 30088361888358137917477901)
  ·
    refine ⟨11283135708134301719054213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30088361888358137917477901 11283135708134301719054213)
    ·
      refine ⟨2115587945275181572322665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11283135708134301719054213 2115587945275181572322665)
      ·
        refine ⟨1586690958956386179241999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2115587945275181572322665 1586690958956386179241999)
        ·
          refine ⟨2380036438434579268862999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586690958956386179241999 2380036438434579268862999)
          ·
            refine ⟨3570054657651868903294499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2380036438434579268862999 3570054657651868903294499)
            ·
              refine ⟨5355081986477803354941749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3570054657651868903294499 5355081986477803354941749)
              ·
                refine ⟨502038936232294064525789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5355081986477803354941749 502038936232294064525789)
                ·
                  refine ⟨188264601087110274197171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502038936232294064525789 188264601087110274197171)
                  ·
                    rfl

theorem cell21_824949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_824949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824949 prefixEnd_824949 := by exact prefixLift 824949
  have htrace : WordTrace (prefixWord ++ tailWord_824949) baseStart_824949 baseEnd_824949 := by
    simpa [prefixWord, tailWord_824949, baseEnd_824949] using wordTrace_append hprefix tailTrace_824949
  have hstable : (prefixWord ++ tailWord_824949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824949).length < 2 ^ (prefixWord ++ tailWord_824949).sum := by decide
  have hdescent : baseEnd_824949 < baseStart_824949 := by decide
  rcases family_descends (prefixWord ++ tailWord_824949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_824994 : List Nat := [3, 3, 1, 4, 1, 1, 1, 7]
def baseStart_824994 : Nat := 118140960795 + 824994 * 2 ^ 59
def prefixEnd_824994 : Nat := 4983230072969 + 3 ^ 40 * 824994 * 2
def baseEnd_824994 : Nat := 62758290233400065315693

theorem tailTrace_824994 : CollatzResearch.WordTrace tailWord_824994 prefixEnd_824994 62758290233400065315693 := by
  unfold tailWord_824994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522500793298777650716509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20060002115463407068577357 7522500793298777650716509)
  ·
    refine ⟨2820937797487041619018691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7522500793298777650716509 2820937797487041619018691)
    ·
      refine ⟨4231406696230562428528037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820937797487041619018691 4231406696230562428528037)
      ·
        refine ⟨793388755543230455349007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4231406696230562428528037 793388755543230455349007)
        ·
          refine ⟨1190083133314845683023511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793388755543230455349007 1190083133314845683023511)
          ·
            refine ⟨1785124699972268524535267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190083133314845683023511 1785124699972268524535267)
            ·
              refine ⟨2677687049958402786802901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785124699972268524535267 2677687049958402786802901)
              ·
                refine ⟨62758290233400065315693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2677687049958402786802901 62758290233400065315693)
                ·
                  rfl

theorem cell21_824994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_824994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_824994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_824994 prefixEnd_824994 := by exact prefixLift 824994
  have htrace : WordTrace (prefixWord ++ tailWord_824994) baseStart_824994 baseEnd_824994 := by
    simpa [prefixWord, tailWord_824994, baseEnd_824994] using wordTrace_append hprefix tailTrace_824994
  have hstable : (prefixWord ++ tailWord_824994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_824994).length < 2 ^ (prefixWord ++ tailWord_824994).sum := by decide
  have hdescent : baseEnd_824994 < baseStart_824994 := by decide
  rcases family_descends (prefixWord ++ tailWord_824994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825000 : List Nat := [2, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_825000 : Nat := 118140960795 + 825000 * 2 ^ 59
def prefixEnd_825000 : Nat := 4983230072969 + 3 ^ 40 * 825000 * 2
def baseEnd_825000 : Nat := 188276239981945518847067

theorem tailTrace_825000 : CollatzResearch.WordTrace tailWord_825000 prefixEnd_825000 188276239981945518847067 := by
  unfold tailWord_825000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045111005586686813792227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20060148007448915751722969 15045111005586686813792227)
  ·
    refine ⟨22567666508380030220688341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15045111005586686813792227 22567666508380030220688341)
    ·
      refine ⟨528929683790156958297383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22567666508380030220688341 528929683790156958297383)
      ·
        refine ⟨793394525685235437446075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528929683790156958297383 793394525685235437446075)
        ·
          refine ⟨1190091788527853156169113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793394525685235437446075 1190091788527853156169113)
          ·
            refine ⟨892568841395889867126835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190091788527853156169113 892568841395889867126835)
            ·
              refine ⟨1338853262093834800690253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892568841395889867126835 1338853262093834800690253)
              ·
                refine ⟨502069973285188050258845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338853262093834800690253 502069973285188050258845)
                ·
                  refine ⟨188276239981945518847067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502069973285188050258845 188276239981945518847067)
                  ·
                    rfl

theorem cell21_825000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_825000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825000 prefixEnd_825000 := by exact prefixLift 825000
  have htrace : WordTrace (prefixWord ++ tailWord_825000) baseStart_825000 baseEnd_825000 := by
    simpa [prefixWord, tailWord_825000, baseEnd_825000] using wordTrace_append hprefix tailTrace_825000
  have hstable : (prefixWord ++ tailWord_825000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825000).length < 2 ^ (prefixWord ++ tailWord_825000).sum := by decide
  have hdescent : baseEnd_825000 < baseStart_825000 := by decide
  rcases family_descends (prefixWord ++ tailWord_825000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825008 : List Nat := [2, 1, 1, 1, 2, 1, 7, 3, 3]
def baseStart_825008 : Nat := 118140960795 + 825008 * 2 ^ 59
def prefixEnd_825008 : Nat := 4983230072969 + 3 ^ 40 * 825008 * 2
def baseEnd_825008 : Nat := 188278065690939282713717

theorem tailTrace_825008 : CollatzResearch.WordTrace tailWord_825008 prefixEnd_825008 188278065690939282713717 := by
  unfold tailWord_825008
  simp only [CollatzResearch.WordTrace]
  refine ⟨15045256897572195496937839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20060342530096260662583785 15045256897572195496937839)
  ·
    refine ⟨22567885346358293245406759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15045256897572195496937839 22567885346358293245406759)
    ·
      refine ⟨33851828019537439868110139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22567885346358293245406759 33851828019537439868110139)
      ·
        refine ⟨50777742029306159802165209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33851828019537439868110139 50777742029306159802165209)
        ·
          refine ⟨38083306521979619851623907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50777742029306159802165209 38083306521979619851623907)
          ·
            refine ⟨57124959782969429777435861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38083306521979619851623907 57124959782969429777435861)
            ·
              refine ⟨1338866244913346010408653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57124959782969429777435861 1338866244913346010408653)
              ·
                refine ⟨502074841842504753903245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1338866244913346010408653 502074841842504753903245)
                ·
                  refine ⟨188278065690939282713717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502074841842504753903245 188278065690939282713717)
                  ·
                    rfl

theorem cell21_825008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 3, 3].length) (baseStart_825008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825008 prefixEnd_825008 := by exact prefixLift 825008
  have htrace : WordTrace (prefixWord ++ tailWord_825008) baseStart_825008 baseEnd_825008 := by
    simpa [prefixWord, tailWord_825008, baseEnd_825008] using wordTrace_append hprefix tailTrace_825008
  have hstable : (prefixWord ++ tailWord_825008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825008).length < 2 ^ (prefixWord ++ tailWord_825008).sum := by decide
  have hdescent : baseEnd_825008 < baseStart_825008 := by decide
  rcases family_descends (prefixWord ++ tailWord_825008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825022 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_825022 : Nat := 118140960795 + 825022 * 2 ^ 59
def prefixEnd_825022 : Nat := 4983230072969 + 3 ^ 40 * 825022 * 2
def baseEnd_825022 : Nat := 188281260681678369480355

theorem tailTrace_825022 : CollatzResearch.WordTrace tailWord_825022 prefixEnd_825022 188281260681678369480355 := by
  unfold tailWord_825022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761378052136708923110665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20060682944729114256590213 3761378052136708923110665)
  ·
    refine ⟨2821033539102531692332999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3761378052136708923110665 2821033539102531692332999)
    ·
      refine ⟨4231550308653797538499499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2821033539102531692332999 4231550308653797538499499)
      ·
        refine ⟨6347325462980696307749249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231550308653797538499499 6347325462980696307749249)
        ·
          refine ⟨4760494097235522230811937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6347325462980696307749249 4760494097235522230811937)
          ·
            refine ⟨3570370572926641673108953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4760494097235522230811937 3570370572926641673108953)
            ·
              refine ⟨2677777929694981254831715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570370572926641673108953 2677777929694981254831715)
              ·
                refine ⟨4016666894542471882247573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677777929694981254831715 4016666894542471882247573)
                ·
                  refine ⟨188281260681678369480355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4016666894542471882247573 188281260681678369480355)
                  ·
                    rfl

theorem cell21_825022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_825022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825022 prefixEnd_825022 := by exact prefixLift 825022
  have htrace : WordTrace (prefixWord ++ tailWord_825022) baseStart_825022 baseEnd_825022 := by
    simpa [prefixWord, tailWord_825022, baseEnd_825022] using wordTrace_append hprefix tailTrace_825022
  have hstable : (prefixWord ++ tailWord_825022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825022).length < 2 ^ (prefixWord ++ tailWord_825022).sum := by decide
  have hdescent : baseEnd_825022 < baseStart_825022 := by decide
  rcases family_descends (prefixWord ++ tailWord_825022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825076 : List Nat := [2, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_825076 : Nat := 118140960795 + 825076 * 2 ^ 59
def prefixEnd_825076 : Nat := 4983230072969 + 3 ^ 40 * 825076 * 2
def baseEnd_825076 : Nat := 188293584217386275580245

theorem tailTrace_825076 : CollatzResearch.WordTrace tailWord_825076 prefixEnd_825076 188293584217386275580245 := by
  unfold tailWord_825076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046496979449019303675541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20061995972598692404900721 15046496979449019303675541)
  ·
    refine ⟨705304545911672779859791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15046496979449019303675541 705304545911672779859791)
    ·
      refine ⟨1057956818867509169789687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705304545911672779859791 1057956818867509169789687)
      ·
        refine ⟨1586935228301263754684531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057956818867509169789687 1586935228301263754684531)
        ·
          refine ⟨2380402842451895632026797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586935228301263754684531 2380402842451895632026797)
          ·
            refine ⟨892651065919460862010049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2380402842451895632026797 892651065919460862010049)
            ·
              refine ⟨669488299439595646507537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 892651065919460862010049 669488299439595646507537)
              ·
                refine ⟨502116224579696734880653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669488299439595646507537 502116224579696734880653)
                ·
                  refine ⟨188293584217386275580245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502116224579696734880653 188293584217386275580245)
                  ·
                    rfl

theorem cell21_825076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_825076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825076 prefixEnd_825076 := by exact prefixLift 825076
  have htrace : WordTrace (prefixWord ++ tailWord_825076) baseStart_825076 baseEnd_825076 := by
    simpa [prefixWord, tailWord_825076, baseEnd_825076] using wordTrace_append hprefix tailTrace_825076
  have hstable : (prefixWord ++ tailWord_825076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825076).length < 2 ^ (prefixWord ++ tailWord_825076).sum := by decide
  have hdescent : baseEnd_825076 < baseStart_825076 := by decide
  rcases family_descends (prefixWord ++ tailWord_825076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825084 : List Nat := [2, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_825084 : Nat := 118140960795 + 825084 * 2 ^ 59
def prefixEnd_825084 : Nat := 4983230072969 + 3 ^ 40 * 825084 * 2
def baseEnd_825084 : Nat := 188295409926380039446895

theorem tailTrace_825084 : CollatzResearch.WordTrace tailWord_825084 prefixEnd_825084 188295409926380039446895 := by
  unfold tailWord_825084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046642871434527986821153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20062190495246037315761537 15046642871434527986821153)
  ·
    refine ⟨11284982153575895990115865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15046642871434527986821153 11284982153575895990115865)
    ·
      refine ⟨8463736615181921992586899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11284982153575895990115865 8463736615181921992586899)
      ·
        refine ⟨12695604922772882988880349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8463736615181921992586899 12695604922772882988880349)
        ·
          refine ⟨4760851846039831120830131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12695604922772882988880349 4760851846039831120830131)
          ·
            refine ⟨7141277769059746681245197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760851846039831120830131 7141277769059746681245197)
            ·
              refine ⟨2677979163397405005466949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141277769059746681245197 2677979163397405005466949)
              ·
                refine ⟨502121093137013438525053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2677979163397405005466949 502121093137013438525053)
                ·
                  refine ⟨188295409926380039446895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502121093137013438525053 188295409926380039446895)
                  ·
                    rfl

theorem cell21_825084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_825084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825084 prefixEnd_825084 := by exact prefixLift 825084
  have htrace : WordTrace (prefixWord ++ tailWord_825084) baseStart_825084 baseEnd_825084 := by
    simpa [prefixWord, tailWord_825084, baseEnd_825084] using wordTrace_append hprefix tailTrace_825084
  have hstable : (prefixWord ++ tailWord_825084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825084).length < 2 ^ (prefixWord ++ tailWord_825084).sum := by decide
  have hdescent : baseEnd_825084 < baseStart_825084 := by decide
  rcases family_descends (prefixWord ++ tailWord_825084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825098 : List Nat := [3, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_825098 : Nat := 118140960795 + 825098 * 2 ^ 59
def prefixEnd_825098 : Nat := 4983230072969 + 3 ^ 40 * 825098 * 2
def baseEnd_825098 : Nat := 188298604917119126213533

theorem tailTrace_825098 : CollatzResearch.WordTrace tailWord_825098 prefixEnd_825098 188298604917119126213533 := by
  unfold tailWord_825098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7523449091204584091162987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20062530909878890909767965 7523449091204584091162987)
  ·
    refine ⟨11285173636806876136744481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7523449091204584091162987 11285173636806876136744481)
    ·
      refine ⟨8463880227605157102558361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11285173636806876136744481 8463880227605157102558361)
      ·
        refine ⟨6347910170703867826918771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8463880227605157102558361 6347910170703867826918771)
        ·
          refine ⟨9521865256055801740378157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347910170703867826918771 9521865256055801740378157)
          ·
            refine ⟨3570699471020925652641809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9521865256055801740378157 3570699471020925652641809)
            ·
              refine ⟨2678024603265694239481357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3570699471020925652641809 2678024603265694239481357)
              ·
                refine ⟨1004259226224635339805509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2678024603265694239481357 1004259226224635339805509)
                ·
                  refine ⟨188298604917119126213533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004259226224635339805509 188298604917119126213533)
                  ·
                    rfl

theorem cell21_825098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_825098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825098 prefixEnd_825098 := by exact prefixLift 825098
  have htrace : WordTrace (prefixWord ++ tailWord_825098) baseStart_825098 baseEnd_825098 := by
    simpa [prefixWord, tailWord_825098, baseEnd_825098] using wordTrace_append hprefix tailTrace_825098
  have hstable : (prefixWord ++ tailWord_825098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825098).length < 2 ^ (prefixWord ++ tailWord_825098).sum := by decide
  have hdescent : baseEnd_825098 < baseStart_825098 := by decide
  rcases family_descends (prefixWord ++ tailWord_825098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825194 : List Nat := [3, 1, 3, 4, 2, 1, 1, 1, 5]
def baseStart_825194 : Nat := 118140960795 + 825194 * 2 ^ 59
def prefixEnd_825194 : Nat := 4983230072969 + 3 ^ 40 * 825194 * 2
def baseEnd_825194 : Nat := 188320513425044292613337

theorem tailTrace_825194 : CollatzResearch.WordTrace tailWord_825194 prefixEnd_825194 188320513425044292613337 := by
  unfold tailWord_825194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524324443117636190036659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20064865181647029840097757 7524324443117636190036659)
  ·
    refine ⟨11286486664676454285054989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7524324443117636190036659 11286486664676454285054989)
    ·
      refine ⟨4232432499253670356895621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11286486664676454285054989 4232432499253670356895621)
      ·
        refine ⟨793581093610063191917929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4232432499253670356895621 793581093610063191917929)
        ·
          refine ⟨595185820207547393938447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 793581093610063191917929 595185820207547393938447)
          ·
            refine ⟨892778730311321090907671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595185820207547393938447 892778730311321090907671)
            ·
              refine ⟨1339168095466981636361507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892778730311321090907671 1339168095466981636361507)
              ·
                refine ⟨2008752143200472454542261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339168095466981636361507 2008752143200472454542261)
                ·
                  refine ⟨188320513425044292613337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2008752143200472454542261 188320513425044292613337)
                  ·
                    rfl

theorem cell21_825194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 1, 5].length) (baseStart_825194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825194 prefixEnd_825194 := by exact prefixLift 825194
  have htrace : WordTrace (prefixWord ++ tailWord_825194) baseStart_825194 baseEnd_825194 := by
    simpa [prefixWord, tailWord_825194, baseEnd_825194] using wordTrace_append hprefix tailTrace_825194
  have hstable : (prefixWord ++ tailWord_825194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825194).length < 2 ^ (prefixWord ++ tailWord_825194).sum := by decide
  have hdescent : baseEnd_825194 < baseStart_825194 := by decide
  rcases family_descends (prefixWord ++ tailWord_825194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825247 : List Nat := [1, 1, 2, 5, 12]
def baseStart_825247 : Nat := 118140960795 + 825247 * 2 ^ 59
def prefixEnd_825247 : Nat := 4983230072969 + 3 ^ 40 * 825247 * 2
def baseEnd_825247 : Nat := 2325093935149728126295

theorem tailTrace_825247 : CollatzResearch.WordTrace tailWord_825247 prefixEnd_825247 2325093935149728126295 := by
  unfold tailWord_825247
  simp only [CollatzResearch.WordTrace]
  refine ⟨30099230841278534811825995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20066153894185689874550663 30099230841278534811825995)
  ·
    refine ⟨45148846261917802217738993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30099230841278534811825995 45148846261917802217738993)
    ·
      refine ⟨33861634696438351663304245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45148846261917802217738993 33861634696438351663304245)
      ·
        refine ⟨3174528252791095468434773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33861634696438351663304245 3174528252791095468434773)
        ·
          refine ⟨2325093935149728126295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3174528252791095468434773 2325093935149728126295)
          ·
            rfl

theorem cell21_825247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 12].length) (baseStart_825247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825247 prefixEnd_825247 := by exact prefixLift 825247
  have htrace : WordTrace (prefixWord ++ tailWord_825247) baseStart_825247 baseEnd_825247 := by
    simpa [prefixWord, tailWord_825247, baseEnd_825247] using wordTrace_append hprefix tailTrace_825247
  have hstable : (prefixWord ++ tailWord_825247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825247).length < 2 ^ (prefixWord ++ tailWord_825247).sum := by decide
  have hdescent : baseEnd_825247 < baseStart_825247 := by decide
  rcases family_descends (prefixWord ++ tailWord_825247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825399 : List Nat := [1, 1, 3, 1, 2, 2, 4, 7]
def baseStart_825399 : Nat := 118140960795 + 825399 * 2 ^ 59
def prefixEnd_825399 : Nat := 4983230072969 + 3 ^ 40 * 825399 * 2
def baseEnd_825399 : Nat := 62789099072669830565417

theorem tailTrace_825399 : CollatzResearch.WordTrace tailWord_825399 prefixEnd_825399 62789099072669830565417 := by
  unfold tailWord_825399
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104774736727864771359251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20069849824485243180906167 30104774736727864771359251)
  ·
    refine ⟨45157162105091797157038877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104774736727864771359251 45157162105091797157038877)
    ·
      refine ⟨16933935789409423933889579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45157162105091797157038877 16933935789409423933889579)
      ·
        refine ⟨25400903684114135900834369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16933935789409423933889579 25400903684114135900834369)
        ·
          refine ⟨19050677763085601925625777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25400903684114135900834369 19050677763085601925625777)
          ·
            refine ⟨14288008322314201444219333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19050677763085601925625777 14288008322314201444219333)
            ·
              refine ⟨2679001560433912770791125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14288008322314201444219333 2679001560433912770791125)
              ·
                refine ⟨62789099072669830565417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2679001560433912770791125 62789099072669830565417)
                ·
                  rfl

theorem cell21_825399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_825399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825399 prefixEnd_825399 := by exact prefixLift 825399
  have htrace : WordTrace (prefixWord ++ tailWord_825399) baseStart_825399 baseEnd_825399 := by
    simpa [prefixWord, tailWord_825399, baseEnd_825399] using wordTrace_append hprefix tailTrace_825399
  have hstable : (prefixWord ++ tailWord_825399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825399).length < 2 ^ (prefixWord ++ tailWord_825399).sum := by decide
  have hdescent : baseEnd_825399 < baseStart_825399 := by decide
  rcases family_descends (prefixWord ++ tailWord_825399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825475 : List Nat := [1, 1, 1, 3, 3, 4, 8]
def baseStart_825475 : Nat := 118140960795 + 825475 * 2 ^ 59
def prefixEnd_825475 : Nat := 4983230072969 + 3 ^ 40 * 825475 * 2
def baseEnd_825475 : Nat := 20931626828161138714381

theorem tailTrace_825475 : CollatzResearch.WordTrace tailWord_825475 prefixEnd_825475 20931626828161138714381 := by
  unfold tailWord_825475
  simp only [CollatzResearch.WordTrace]
  refine ⟨30107546684452529751125879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20071697789635019834083919 30107546684452529751125879)
  ·
    refine ⟨45161320026678794626688819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30107546684452529751125879 45161320026678794626688819)
    ·
      refine ⟨67741980040018191940033229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45161320026678794626688819 67741980040018191940033229)
      ·
        refine ⟨25403242515006821977512461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67741980040018191940033229 25403242515006821977512461)
        ·
          refine ⟨9526215943127558241567173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25403242515006821977512461 9526215943127558241567173)
          ·
            refine ⟨1786165489336417170293845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9526215943127558241567173 1786165489336417170293845)
            ·
              refine ⟨20931626828161138714381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1786165489336417170293845 20931626828161138714381)
              ·
                rfl

theorem cell21_825475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 8].length) (baseStart_825475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825475 prefixEnd_825475 := by exact prefixLift 825475
  have htrace : WordTrace (prefixWord ++ tailWord_825475) baseStart_825475 baseEnd_825475 := by
    simpa [prefixWord, tailWord_825475, baseEnd_825475] using wordTrace_append hprefix tailTrace_825475
  have hstable : (prefixWord ++ tailWord_825475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825475).length < 2 ^ (prefixWord ++ tailWord_825475).sum := by decide
  have hdescent : baseEnd_825475 < baseStart_825475 := by decide
  rcases family_descends (prefixWord ++ tailWord_825475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825495 : List Nat := [1, 1, 3, 3, 4, 1, 3, 1, 4]
def baseStart_825495 : Nat := 118140960795 + 825495 * 2 ^ 59
def prefixEnd_825495 : Nat := 4983230072969 + 3 ^ 40 * 825495 * 2
def baseEnd_825495 : Nat := 188389205725934658096055

theorem tailTrace_825495 : CollatzResearch.WordTrace tailWord_825495 prefixEnd_825495 188389205725934658096055 := by
  unfold tailWord_825495
  simp only [CollatzResearch.WordTrace]
  refine ⟨30108276144380073166853939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20072184096253382111235959 30108276144380073166853939)
  ·
    refine ⟨45162414216570109750280909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30108276144380073166853939 45162414216570109750280909)
    ·
      refine ⟨16935905331213791156355341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45162414216570109750280909 16935905331213791156355341)
      ·
        refine ⟨6350964499205171683633253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16935905331213791156355341 6350964499205171683633253)
        ·
          refine ⟨1190805843600969690681235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6350964499205171683633253 1190805843600969690681235)
          ·
            refine ⟨1786208765401454536021853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190805843600969690681235 1786208765401454536021853)
            ·
              refine ⟨669828287025545451008195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786208765401454536021853 669828287025545451008195)
              ·
                refine ⟨1004742430538318176512293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669828287025545451008195 1004742430538318176512293)
                ·
                  refine ⟨188389205725934658096055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004742430538318176512293 188389205725934658096055)
                  ·
                    rfl

theorem cell21_825495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4].length) (baseStart_825495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825495 prefixEnd_825495 := by exact prefixLift 825495
  have htrace : WordTrace (prefixWord ++ tailWord_825495) baseStart_825495 baseEnd_825495 := by
    simpa [prefixWord, tailWord_825495, baseEnd_825495] using wordTrace_append hprefix tailTrace_825495
  have hstable : (prefixWord ++ tailWord_825495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825495).length < 2 ^ (prefixWord ++ tailWord_825495).sum := by decide
  have hdescent : baseEnd_825495 < baseStart_825495 := by decide
  rcases family_descends (prefixWord ++ tailWord_825495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825540 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_825540 : Nat := 118140960795 + 825540 * 2 ^ 59
def prefixEnd_825540 : Nat := 4983230072969 + 3 ^ 40 * 825540 * 2
def baseEnd_825540 : Nat := 188399475339024579845963

theorem tailTrace_825540 : CollatzResearch.WordTrace tailWord_825540 prefixEnd_825540 188399475339024579845963 := by
  unfold tailWord_825540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15054958714608522926121037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20073278286144697234828049 15054958714608522926121037)
  ·
    refine ⟨5645609517978196097295389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15054958714608522926121037 5645609517978196097295389)
    ·
      refine ⟨2117103569241823536485771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5645609517978196097295389 2117103569241823536485771)
      ·
        refine ⟨3175655353862735304728657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2117103569241823536485771 3175655353862735304728657)
        ·
          refine ⟨2381741515397051478546493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175655353862735304728657 2381741515397051478546493)
          ·
            refine ⟨893153068273894304454935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2381741515397051478546493 893153068273894304454935)
            ·
              refine ⟨1339729602410841456682403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893153068273894304454935 1339729602410841456682403)
              ·
                refine ⟨2009594403616262185023605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339729602410841456682403 2009594403616262185023605)
                ·
                  refine ⟨188399475339024579845963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2009594403616262185023605 188399475339024579845963)
                  ·
                    rfl

theorem cell21_825540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_825540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825540 prefixEnd_825540 := by exact prefixLift 825540
  have htrace : WordTrace (prefixWord ++ tailWord_825540) baseStart_825540 baseEnd_825540 := by
    simpa [prefixWord, tailWord_825540, baseEnd_825540] using wordTrace_append hprefix tailTrace_825540
  have hstable : (prefixWord ++ tailWord_825540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825540).length < 2 ^ (prefixWord ++ tailWord_825540).sum := by decide
  have hdescent : baseEnd_825540 < baseStart_825540 := by decide
  rcases family_descends (prefixWord ++ tailWord_825540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825551 : List Nat := [1, 1, 2, 1, 1, 3, 6, 6]
def baseStart_825551 : Nat := 118140960795 + 825551 * 2 ^ 59
def prefixEnd_825551 : Nat := 4983230072969 + 3 ^ 40 * 825551 * 2
def baseEnd_825551 : Nat := 62800661896297001720869

theorem tailTrace_825551 : CollatzResearch.WordTrace tailWord_825551 prefixEnd_825551 62800661896297001720869 := by
  unfold tailWord_825551
  simp only [CollatzResearch.WordTrace]
  refine ⟨30110318632177194730892507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20073545754784796487261671 30110318632177194730892507)
  ·
    refine ⟨45165477948265792096338761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30110318632177194730892507 45165477948265792096338761)
    ·
      refine ⟨33874108461199344072254071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45165477948265792096338761 33874108461199344072254071)
      ·
        refine ⟨50811162691799016108381107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33874108461199344072254071 50811162691799016108381107)
        ·
          refine ⟨76216744037698524162571661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50811162691799016108381107 76216744037698524162571661)
          ·
            refine ⟨28581279014136946560964373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76216744037698524162571661 28581279014136946560964373)
            ·
              refine ⟨1339747453787669370045205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28581279014136946560964373 1339747453787669370045205)
              ·
                refine ⟨62800661896297001720869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1339747453787669370045205 62800661896297001720869)
                ·
                  rfl

theorem cell21_825551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_825551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825551 prefixEnd_825551 := by exact prefixLift 825551
  have htrace : WordTrace (prefixWord ++ tailWord_825551) baseStart_825551 baseEnd_825551 := by
    simpa [prefixWord, tailWord_825551, baseEnd_825551] using wordTrace_append hprefix tailTrace_825551
  have hstable : (prefixWord ++ tailWord_825551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825551).length < 2 ^ (prefixWord ++ tailWord_825551).sum := by decide
  have hdescent : baseEnd_825551 < baseStart_825551 := by decide
  rcases family_descends (prefixWord ++ tailWord_825551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825554 : List Nat := [3, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_825554 : Nat := 118140960795 + 825554 * 2 ^ 59
def prefixEnd_825554 : Nat := 4983230072969 + 3 ^ 40 * 825554 * 2
def baseEnd_825554 : Nat := 188402670329763666612601

theorem tailTrace_825554 : CollatzResearch.WordTrace tailWord_825554 prefixEnd_825554 188402670329763666612601 := by
  unfold tailWord_825554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7527607012791581560812929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20073618700777550828834477 7527607012791581560812929)
  ·
    refine ⟨5645705259593686170609697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7527607012791581560812929 5645705259593686170609697)
    ·
      refine ⟨4234278944695264627957273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5645705259593686170609697 4234278944695264627957273)
      ·
        refine ⟨3175709208521448470967955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4234278944695264627957273 3175709208521448470967955)
        ·
          refine ⟨4763563812782172706451933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3175709208521448470967955 4763563812782172706451933)
          ·
            refine ⟨1786336429793314764919475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4763563812782172706451933 1786336429793314764919475)
            ·
              refine ⟨2679504644689972147379213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786336429793314764919475 2679504644689972147379213)
              ·
                refine ⟨1004814241758739555267205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2679504644689972147379213 1004814241758739555267205)
                ·
                  refine ⟨188402670329763666612601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004814241758739555267205 188402670329763666612601)
                  ·
                    rfl

theorem cell21_825554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_825554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825554 prefixEnd_825554 := by exact prefixLift 825554
  have htrace : WordTrace (prefixWord ++ tailWord_825554) baseStart_825554 baseEnd_825554 := by
    simpa [prefixWord, tailWord_825554, baseEnd_825554] using wordTrace_append hprefix tailTrace_825554
  have hstable : (prefixWord ++ tailWord_825554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825554).length < 2 ^ (prefixWord ++ tailWord_825554).sum := by decide
  have hdescent : baseEnd_825554 < baseStart_825554 := by decide
  rcases family_descends (prefixWord ++ tailWord_825554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825599 : List Nat := [1, 1, 2, 2, 1, 4, 3, 4, 3]
def baseStart_825599 : Nat := 118140960795 + 825599 * 2 ^ 59
def prefixEnd_825599 : Nat := 4983230072969 + 3 ^ 40 * 825599 * 2
def baseEnd_825599 : Nat := 188412939942853588362509

theorem tailTrace_825599 : CollatzResearch.WordTrace tailWord_825599 prefixEnd_825599 188412939942853588362509 := by
  unfold tailWord_825599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30112069336003298928639851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20074712890668865952426567 30112069336003298928639851)
  ·
    refine ⟨45168104004004948392959777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30112069336003298928639851 45168104004004948392959777)
    ·
      refine ⟨33876078003003711294719833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45168104004004948392959777 33876078003003711294719833)
      ·
        refine ⟨25407058502252783471039875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33876078003003711294719833 25407058502252783471039875)
        ·
          refine ⟨38110587753379175206559813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407058502252783471039875 38110587753379175206559813)
          ·
            refine ⟨7145735203758595351229965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38110587753379175206559813 7145735203758595351229965)
            ·
              refine ⟨2679650701409473256711237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7145735203758595351229965 2679650701409473256711237)
              ·
                refine ⟨502434506514276235633357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2679650701409473256711237 502434506514276235633357)
                ·
                  refine ⟨188412939942853588362509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502434506514276235633357 188412939942853588362509)
                  ·
                    rfl

theorem cell21_825599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 4, 3].length) (baseStart_825599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825599 prefixEnd_825599 := by exact prefixLift 825599
  have htrace : WordTrace (prefixWord ++ tailWord_825599) baseStart_825599 baseEnd_825599 := by
    simpa [prefixWord, tailWord_825599, baseEnd_825599] using wordTrace_append hprefix tailTrace_825599
  have hstable : (prefixWord ++ tailWord_825599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825599).length < 2 ^ (prefixWord ++ tailWord_825599).sum := by decide
  have hdescent : baseEnd_825599 < baseStart_825599 := by decide
  rcases family_descends (prefixWord ++ tailWord_825599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825658 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 5]
def baseStart_825658 : Nat := 118140960795 + 825658 * 2 ^ 59
def prefixEnd_825658 : Nat := 4983230072969 + 3 ^ 40 * 825658 * 2
def baseEnd_825658 : Nat := 188426404546682596879055

theorem tailTrace_825658 : CollatzResearch.WordTrace tailWord_825658 prefixEnd_825658 188426404546682596879055 := by
  unfold tailWord_825658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528555310697388001259407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20076147495193034670025085 7528555310697388001259407)
  ·
    refine ⟨11292832966046082001889111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7528555310697388001259407 11292832966046082001889111)
    ·
      refine ⟨16939249449069123002833667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11292832966046082001889111 16939249449069123002833667)
      ·
        refine ⟨25408874173603684504250501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16939249449069123002833667 25408874173603684504250501)
        ·
          refine ⟨4764163907550690844546969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25408874173603684504250501 4764163907550690844546969)
          ·
            refine ⟨3573122930663018133410227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764163907550690844546969 3573122930663018133410227)
            ·
              refine ⟨5359684395994527200115341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573122930663018133410227 5359684395994527200115341)
              ·
                refine ⟨2009881648497947700043253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5359684395994527200115341 2009881648497947700043253)
                ·
                  refine ⟨188426404546682596879055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2009881648497947700043253 188426404546682596879055)
                  ·
                    rfl

theorem cell21_825658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_825658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825658 prefixEnd_825658 := by exact prefixLift 825658
  have htrace : WordTrace (prefixWord ++ tailWord_825658) baseStart_825658 baseEnd_825658 := by
    simpa [prefixWord, tailWord_825658, baseEnd_825658] using wordTrace_append hprefix tailTrace_825658
  have hstable : (prefixWord ++ tailWord_825658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825658).length < 2 ^ (prefixWord ++ tailWord_825658).sum := by decide
  have hdescent : baseEnd_825658 < baseStart_825658 := by decide
  rcases family_descends (prefixWord ++ tailWord_825658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825703 : List Nat := [1, 1, 5, 1, 3, 1, 9]
def baseStart_825703 : Nat := 118140960795 + 825703 * 2 ^ 59
def prefixEnd_825703 : Nat := 4983230072969 + 3 ^ 40 * 825703 * 2
def baseEnd_825703 : Nat := 20937408239974724292107

theorem tailTrace_825703 : CollatzResearch.WordTrace tailWord_825703 prefixEnd_825703 20937408239974724292107 := by
  unfold tailWord_825703
  simp only [CollatzResearch.WordTrace]
  refine ⟨30115862527626524690425763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20077241685084349793617175 30115862527626524690425763)
  ·
    refine ⟨45173793791439787035638645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30115862527626524690425763 45173793791439787035638645)
    ·
      refine ⟨4235043167947480034591123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45173793791439787035638645 4235043167947480034591123)
      ·
        refine ⟨6352564751921220051886685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235043167947480034591123 6352564751921220051886685)
        ·
          refine ⟨2382211781970457519457507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6352564751921220051886685 2382211781970457519457507)
          ·
            refine ⟨3573317672955686279186261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382211781970457519457507 3573317672955686279186261)
            ·
              refine ⟨20937408239974724292107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3573317672955686279186261 20937408239974724292107)
              ·
                rfl

theorem cell21_825703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 9].length) (baseStart_825703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825703 prefixEnd_825703 := by exact prefixLift 825703
  have htrace : WordTrace (prefixWord ++ tailWord_825703) baseStart_825703 baseEnd_825703 := by
    simpa [prefixWord, tailWord_825703, baseEnd_825703] using wordTrace_append hprefix tailTrace_825703
  have hstable : (prefixWord ++ tailWord_825703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825703).length < 2 ^ (prefixWord ++ tailWord_825703).sum := by decide
  have hdescent : baseEnd_825703 < baseStart_825703 := by decide
  rcases family_descends (prefixWord ++ tailWord_825703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825765 : List Nat := [1, 3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_825765 : Nat := 118140960795 + 825765 * 2 ^ 59
def prefixEnd_825765 : Nat := 4983230072969 + 3 ^ 40 * 825765 * 2
def baseEnd_825765 : Nat := 188450823404474188595503

theorem tailTrace_825765 : CollatzResearch.WordTrace tailWord_825765 prefixEnd_825765 188450823404474188595503 := by
  unfold tailWord_825765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30118123853401909279182749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20078749235601272852788499 30118123853401909279182749)
  ·
    refine ⟨11294296445025715979693531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30118123853401909279182749 11294296445025715979693531)
    ·
      refine ⟨16941444667538573969540297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11294296445025715979693531 16941444667538573969540297)
      ·
        refine ⟨12706083500653930477155223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16941444667538573969540297 12706083500653930477155223)
        ·
          refine ⟨19059125250980895715732835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706083500653930477155223 19059125250980895715732835)
          ·
            refine ⟨28588687876471343573599253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19059125250980895715732835 28588687876471343573599253)
            ·
              refine ⟨1340094744209594230012465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28588687876471343573599253 1340094744209594230012465)
              ·
                refine ⟨1005071058157195672509349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340094744209594230012465 1005071058157195672509349)
                ·
                  refine ⟨188450823404474188595503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005071058157195672509349 188450823404474188595503)
                  ·
                    rfl

theorem cell21_825765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_825765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825765 prefixEnd_825765 := by exact prefixLift 825765
  have htrace : WordTrace (prefixWord ++ tailWord_825765) baseStart_825765 baseEnd_825765 := by
    simpa [prefixWord, tailWord_825765, baseEnd_825765] using wordTrace_append hprefix tailTrace_825765
  have hstable : (prefixWord ++ tailWord_825765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825765).length < 2 ^ (prefixWord ++ tailWord_825765).sum := by decide
  have hdescent : baseEnd_825765 < baseStart_825765 := by decide
  rcases family_descends (prefixWord ++ tailWord_825765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825824 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_825824 : Nat := 118140960795 + 825824 * 2 ^ 59
def prefixEnd_825824 : Nat := 4983230072969 + 3 ^ 40 * 825824 * 2
def baseEnd_825824 : Nat := 188464288008303197112049

theorem tailTrace_825824 : CollatzResearch.WordTrace tailWord_825824 prefixEnd_825824 188464288008303197112049 := by
  unfold tailWord_825824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15060137880094081177790263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20080183840125441570387017 15060137880094081177790263)
  ·
    refine ⟨22590206820141121766685395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15060137880094081177790263 22590206820141121766685395)
    ·
      refine ⟨33885310230211682650028093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22590206820141121766685395 33885310230211682650028093)
      ·
        refine ⟨12706991336329380993760535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33885310230211682650028093 12706991336329380993760535)
        ·
          refine ⟨19060487004494071490640803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706991336329380993760535 19060487004494071490640803)
          ·
            refine ⟨28590730506741107235961205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19060487004494071490640803 28590730506741107235961205)
            ·
              refine ⟨2680380985006978803371363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28590730506741107235961205 2680380985006978803371363)
              ·
                refine ⟨4020571477510468205057045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680380985006978803371363 4020571477510468205057045)
                ·
                  refine ⟨188464288008303197112049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4020571477510468205057045 188464288008303197112049)
                  ·
                    rfl

theorem cell21_825824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_825824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825824 prefixEnd_825824 := by exact prefixLift 825824
  have htrace : WordTrace (prefixWord ++ tailWord_825824) baseStart_825824 baseEnd_825824 := by
    simpa [prefixWord, tailWord_825824, baseEnd_825824] using wordTrace_append hprefix tailTrace_825824
  have hstable : (prefixWord ++ tailWord_825824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825824).length < 2 ^ (prefixWord ++ tailWord_825824).sum := by decide
  have hdescent : baseEnd_825824 < baseStart_825824 := by decide
  rcases family_descends (prefixWord ++ tailWord_825824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825827 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_825827 : Nat := 118140960795 + 825827 * 2 ^ 59
def prefixEnd_825827 : Nat := 4983230072969 + 3 ^ 40 * 825827 * 2
def baseEnd_825827 : Nat := 188464972649175858562043

theorem tailTrace_825827 : CollatzResearch.WordTrace tailWord_825827 prefixEnd_825827 188464972649175858562043 := by
  unfold tailWord_825827
  simp only [CollatzResearch.WordTrace]
  refine ⟨30120385179177293867939735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20080256786118195911959823 30120385179177293867939735)
  ·
    refine ⟨45180577768765940801909603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30120385179177293867939735 45180577768765940801909603)
    ·
      refine ⟨67770866653148911202864405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45180577768765940801909603 67770866653148911202864405)
      ·
        refine ⟨3176759374366355212634269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67770866653148911202864405 3176759374366355212634269)
        ·
          refine ⟨1191284765387383204737851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3176759374366355212634269 1191284765387383204737851)
          ·
            refine ⟨1786927148081074807106777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191284765387383204737851 1786927148081074807106777)
            ·
              refine ⟨1340195361060806105330083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786927148081074807106777 1340195361060806105330083)
              ·
                refine ⟨2010293041591209157995125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340195361060806105330083 2010293041591209157995125)
                ·
                  refine ⟨188464972649175858562043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2010293041591209157995125 188464972649175858562043)
                  ·
                    rfl

theorem cell21_825827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_825827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825827 prefixEnd_825827 := by exact prefixLift 825827
  have htrace : WordTrace (prefixWord ++ tailWord_825827) baseStart_825827 baseEnd_825827 := by
    simpa [prefixWord, tailWord_825827, baseEnd_825827] using wordTrace_append hprefix tailTrace_825827
  have hstable : (prefixWord ++ tailWord_825827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825827).length < 2 ^ (prefixWord ++ tailWord_825827).sum := by decide
  have hdescent : baseEnd_825827 < baseStart_825827 := by decide
  rcases family_descends (prefixWord ++ tailWord_825827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825892 : List Nat := [2, 3, 1, 5, 1, 2, 2, 1, 4]
def baseStart_825892 : Nat := 118140960795 + 825892 * 2 ^ 59
def prefixEnd_825892 : Nat := 4983230072969 + 3 ^ 40 * 825892 * 2
def baseEnd_825892 : Nat := 188479806534750189978577

theorem tailTrace_825892 : CollatzResearch.WordTrace tailWord_825892 prefixEnd_825892 188479806534750189978577 := by
  unfold tailWord_825892
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061377961970904984527965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20081837282627873312703953 15061377961970904984527965)
  ·
    refine ⟨5648016735739089369197987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15061377961970904984527965 5648016735739089369197987)
    ·
      refine ⟨8472025103608634053796981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648016735739089369197987 8472025103608634053796981)
      ·
        refine ⟨794252353463309442543467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8472025103608634053796981 794252353463309442543467)
        ·
          refine ⟨1191378530194964163815201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794252353463309442543467 1191378530194964163815201)
          ·
            refine ⟨893533897646223122861401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191378530194964163815201 893533897646223122861401)
            ·
              refine ⟨670150423234667342146051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893533897646223122861401 670150423234667342146051)
              ·
                refine ⟨1005225634852001013219077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670150423234667342146051 1005225634852001013219077)
                ·
                  refine ⟨188479806534750189978577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005225634852001013219077 188479806534750189978577)
                  ·
                    rfl

theorem cell21_825892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_825892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825892 prefixEnd_825892 := by exact prefixLift 825892
  have htrace : WordTrace (prefixWord ++ tailWord_825892) baseStart_825892 baseEnd_825892 := by
    simpa [prefixWord, tailWord_825892, baseEnd_825892] using wordTrace_append hprefix tailTrace_825892
  have hstable : (prefixWord ++ tailWord_825892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825892).length < 2 ^ (prefixWord ++ tailWord_825892).sum := by decide
  have hdescent : baseEnd_825892 < baseStart_825892 := by decide
  rcases family_descends (prefixWord ++ tailWord_825892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825962 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_825962 : Nat := 118140960795 + 825962 * 2 ^ 59
def prefixEnd_825962 : Nat := 4983230072969 + 3 ^ 40 * 825962 * 2
def baseEnd_825962 : Nat := 188495781488445623811767

theorem tailTrace_825962 : CollatzResearch.WordTrace tailWord_825962 prefixEnd_825962 188495781488445623811767 := by
  unfold tailWord_825962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531327258422052981026035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20083539355792141282736093 7531327258422052981026035)
  ·
    refine ⟨11296990887633079471539053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7531327258422052981026035 11296990887633079471539053)
    ·
      refine ⟨4236371582862404801827145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11296990887633079471539053 4236371582862404801827145)
      ·
        refine ⟨3177278687146803601370359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4236371582862404801827145 3177278687146803601370359)
        ·
          refine ⟨4765918030720205402055539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177278687146803601370359 4765918030720205402055539)
          ·
            refine ⟨7148877046080308103083309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765918030720205402055539 7148877046080308103083309)
            ·
              refine ⟨2680828892280115538656241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7148877046080308103083309 2680828892280115538656241)
              ·
                refine ⟨2010621669210086653992181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680828892280115538656241 2010621669210086653992181)
                ·
                  refine ⟨188495781488445623811767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2010621669210086653992181 188495781488445623811767)
                  ·
                    rfl

theorem cell21_825962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_825962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_825962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_825962 prefixEnd_825962 := by exact prefixLift 825962
  have htrace : WordTrace (prefixWord ++ tailWord_825962) baseStart_825962 baseEnd_825962 := by
    simpa [prefixWord, tailWord_825962, baseEnd_825962] using wordTrace_append hprefix tailTrace_825962
  have hstable : (prefixWord ++ tailWord_825962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825962).length < 2 ^ (prefixWord ++ tailWord_825962).sum := by decide
  have hdescent : baseEnd_825962 < baseStart_825962 := by decide
  rcases family_descends (prefixWord ++ tailWord_825962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826061 : List Nat := [1, 6, 2, 1, 3, 1, 2, 1, 4]
def baseStart_826061 : Nat := 118140960795 + 826061 * 2 ^ 59
def prefixEnd_826061 : Nat := 4983230072969 + 3 ^ 40 * 826061 * 2
def baseEnd_826061 : Nat := 188518374637243451661565

theorem tailTrace_826061 : CollatzResearch.WordTrace tailWord_826061 prefixEnd_826061 188518374637243451661565 := by
  unfold tailWord_826061
  simp only [CollatzResearch.WordTrace]
  refine ⟨30128919860329551831958037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20085946573553034554638691 30128919860329551831958037)
  ·
    refine ⟨1412293118452947742123033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30128919860329551831958037 1412293118452947742123033)
    ·
      refine ⟨1059219838839710806592275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1412293118452947742123033 1059219838839710806592275)
      ·
        refine ⟨1588829758259566209888413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059219838839710806592275 1588829758259566209888413)
        ·
          refine ⟨595811159347337328708155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1588829758259566209888413 595811159347337328708155)
          ·
            refine ⟨893716739021005993062233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595811159347337328708155 893716739021005993062233)
            ·
              refine ⟨670287554265754494796675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893716739021005993062233 670287554265754494796675)
              ·
                refine ⟨1005431331398631742195013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670287554265754494796675 1005431331398631742195013)
                ·
                  refine ⟨188518374637243451661565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005431331398631742195013 188518374637243451661565)
                  ·
                    rfl

theorem cell21_826061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_826061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826061 prefixEnd_826061 := by exact prefixLift 826061
  have htrace : WordTrace (prefixWord ++ tailWord_826061) baseStart_826061 baseEnd_826061 := by
    simpa [prefixWord, tailWord_826061, baseEnd_826061] using wordTrace_append hprefix tailTrace_826061
  have hstable : (prefixWord ++ tailWord_826061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826061).length < 2 ^ (prefixWord ++ tailWord_826061).sum := by decide
  have hdescent : baseEnd_826061 < baseStart_826061 := by decide
  rcases family_descends (prefixWord ++ tailWord_826061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826083 : List Nat := [1, 1, 1, 7, 1, 1, 2, 7]
def baseStart_826083 : Nat := 118140960795 + 826083 * 2 ^ 59
def prefixEnd_826083 : Nat := 4983230072969 + 3 ^ 40 * 826083 * 2
def baseEnd_826083 : Nat := 62841131778992100764951

theorem tailTrace_826083 : CollatzResearch.WordTrace tailWord_826083 prefixEnd_826083 62841131778992100764951 := by
  unfold tailWord_826083
  simp only [CollatzResearch.WordTrace]
  refine ⟨30129722266249849589258903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20086481510833233059505935 30129722266249849589258903)
  ·
    refine ⟨45194583399374774383888355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30129722266249849589258903 45194583399374774383888355)
    ·
      refine ⟨67791875099062161575832533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45194583399374774383888355 67791875099062161575832533)
      ·
        refine ⟨1588872072634269411933575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 67791875099062161575832533 1588872072634269411933575)
        ·
          refine ⟨2383308108951404117900363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588872072634269411933575 2383308108951404117900363)
          ·
            refine ⟨3574962163427106176850545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383308108951404117900363 3574962163427106176850545)
            ·
              refine ⟨2681221622570329632637909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574962163427106176850545 2681221622570329632637909)
              ·
                refine ⟨62841131778992100764951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2681221622570329632637909 62841131778992100764951)
                ·
                  rfl

theorem cell21_826083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_826083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826083 prefixEnd_826083 := by exact prefixLift 826083
  have htrace : WordTrace (prefixWord ++ tailWord_826083) baseStart_826083 baseEnd_826083 := by
    simpa [prefixWord, tailWord_826083, baseEnd_826083] using wordTrace_append hprefix tailTrace_826083
  have hstable : (prefixWord ++ tailWord_826083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826083).length < 2 ^ (prefixWord ++ tailWord_826083).sum := by decide
  have hdescent : baseEnd_826083 < baseStart_826083 := by decide
  rcases family_descends (prefixWord ++ tailWord_826083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826100 : List Nat := [2, 6, 1, 1, 11]
def baseStart_826100 : Nat := 118140960795 + 826100 * 2 ^ 59
def prefixEnd_826100 : Nat := 4983230072969 + 3 ^ 40 * 826100 * 2
def baseEnd_826100 : Nat := 2327497221834420376685

theorem tailTrace_826100 : CollatzResearch.WordTrace tailWord_826100 prefixEnd_826100 2327497221834420376685 := by
  unfold tailWord_826100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065171153594130746313877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20086894871458840995085169 15065171153594130746313877)
  ·
    refine ⟨706179897824724878733463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15065171153594130746313877 706179897824724878733463)
    ·
      refine ⟨1059269846737087318100195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706179897824724878733463 1059269846737087318100195)
      ·
        refine ⟨1588904770105630977150293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059269846737087318100195 1588904770105630977150293)
        ·
          refine ⟨2327497221834420376685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1588904770105630977150293 2327497221834420376685)
          ·
            rfl

theorem cell21_826100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 11].length) (baseStart_826100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826100 prefixEnd_826100 := by exact prefixLift 826100
  have htrace : WordTrace (prefixWord ++ tailWord_826100) baseStart_826100 baseEnd_826100 := by
    simpa [prefixWord, tailWord_826100, baseEnd_826100] using wordTrace_append hprefix tailTrace_826100
  have hstable : (prefixWord ++ tailWord_826100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826100).length < 2 ^ (prefixWord ++ tailWord_826100).sum := by decide
  have hdescent : baseEnd_826100 < baseStart_826100 := by decide
  rcases family_descends (prefixWord ++ tailWord_826100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826148 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 3]
def baseStart_826148 : Nat := 118140960795 + 826148 * 2 ^ 59
def prefixEnd_826148 : Nat := 4983230072969 + 3 ^ 40 * 826148 * 2
def baseEnd_826148 : Nat := 188538229222550633711387

theorem tailTrace_826148 : CollatzResearch.WordTrace tailWord_826148 prefixEnd_826148 188538229222550633711387 := by
  unfold tailWord_826148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15066046505507182845187549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20088062007342910460250065 15066046505507182845187549)
  ·
    refine ⟨5649767439565193566945331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15066046505507182845187549 5649767439565193566945331)
    ·
      refine ⟨8474651159347790350417997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649767439565193566945331 8474651159347790350417997)
      ·
        refine ⟨3177994184755421381406749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8474651159347790350417997 3177994184755421381406749)
        ·
          refine ⟨1191747819283283018027531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3177994184755421381406749 1191747819283283018027531)
          ·
            refine ⟨1787621728924924527041297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191747819283283018027531 1787621728924924527041297)
            ·
              refine ⟨1340716296693693395280973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787621728924924527041297 1340716296693693395280973)
              ·
                refine ⟨502768611260135023230365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340716296693693395280973 502768611260135023230365)
                ·
                  refine ⟨188538229222550633711387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 502768611260135023230365 188538229222550633711387)
                  ·
                    rfl

theorem cell21_826148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_826148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826148 prefixEnd_826148 := by exact prefixLift 826148
  have htrace : WordTrace (prefixWord ++ tailWord_826148) baseStart_826148 baseEnd_826148 := by
    simpa [prefixWord, tailWord_826148, baseEnd_826148] using wordTrace_append hprefix tailTrace_826148
  have hstable : (prefixWord ++ tailWord_826148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826148).length < 2 ^ (prefixWord ++ tailWord_826148).sum := by decide
  have hdescent : baseEnd_826148 < baseStart_826148 := by decide
  rcases family_descends (prefixWord ++ tailWord_826148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826193 : List Nat := [1, 2, 2, 1, 7, 1, 2, 5]
def baseStart_826193 : Nat := 118140960795 + 826193 * 2 ^ 59
def prefixEnd_826193 : Nat := 4983230072969 + 3 ^ 40 * 826193 * 2
def baseEnd_826193 : Nat := 62849499611880185153765

theorem tailTrace_826193 : CollatzResearch.WordTrace tailWord_826193 prefixEnd_826193 62849499611880185153765 := by
  unfold tailWord_826193
  simp only [CollatzResearch.WordTrace]
  refine ⟨30133734295851338375763233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20089156197234225583842155 30133734295851338375763233)
  ·
    refine ⟨22600300721888503781822425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30133734295851338375763233 22600300721888503781822425)
    ·
      refine ⟨16950225541416377836366819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22600300721888503781822425 16950225541416377836366819)
      ·
        refine ⟨25425338312124566754550229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16950225541416377836366819 25425338312124566754550229)
        ·
          refine ⟨595906366690419533309771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25425338312124566754550229 595906366690419533309771)
          ·
            refine ⟨893859550035629299964657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595906366690419533309771 893859550035629299964657)
            ·
              refine ⟨670394662526721974973493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893859550035629299964657 670394662526721974973493)
              ·
                refine ⟨62849499611880185153765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 670394662526721974973493 62849499611880185153765)
                ·
                  rfl

theorem cell21_826193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 5].length) (baseStart_826193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826193 prefixEnd_826193 := by exact prefixLift 826193
  have htrace : WordTrace (prefixWord ++ tailWord_826193) baseStart_826193 baseEnd_826193 := by
    simpa [prefixWord, tailWord_826193, baseEnd_826193] using wordTrace_append hprefix tailTrace_826193
  have hstable : (prefixWord ++ tailWord_826193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826193).length < 2 ^ (prefixWord ++ tailWord_826193).sum := by decide
  have hdescent : baseEnd_826193 < baseStart_826193 := by decide
  rcases family_descends (prefixWord ++ tailWord_826193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826407 : List Nat := [1, 1, 7, 1, 1, 3, 2, 1, 4]
def baseStart_826407 : Nat := 118140960795 + 826407 * 2 ^ 59
def prefixEnd_826407 : Nat := 4983230072969 + 3 ^ 40 * 826407 * 2
def baseEnd_826407 : Nat := 188597336551223738894191

theorem tailTrace_826407 : CollatzResearch.WordTrace tailWord_826407 prefixEnd_826407 188597336551223738894191 := by
  unfold tailWord_826407
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141539517076052924053475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20094359678050701949368983 30141539517076052924053475)
  ·
    refine ⟨45212309275614079386080213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30141539517076052924053475 45212309275614079386080213)
    ·
      refine ⟨1059663498647204985611255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 45212309275614079386080213 1059663498647204985611255)
      ·
        refine ⟨1589495247970807478416883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059663498647204985611255 1589495247970807478416883)
        ·
          refine ⟨2384242871956211217625325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589495247970807478416883 2384242871956211217625325)
          ·
            refine ⟨894091076983579206609497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2384242871956211217625325 894091076983579206609497)
            ·
              refine ⟨670568307737684404957123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894091076983579206609497 670568307737684404957123)
              ·
                refine ⟨1005852461606526607435685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670568307737684404957123 1005852461606526607435685)
                ·
                  refine ⟨188597336551223738894191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005852461606526607435685 188597336551223738894191)
                  ·
                    rfl

theorem cell21_826407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4].length) (baseStart_826407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826407 prefixEnd_826407 := by exact prefixLift 826407
  have htrace : WordTrace (prefixWord ++ tailWord_826407) baseStart_826407 baseEnd_826407 := by
    simpa [prefixWord, tailWord_826407, baseEnd_826407] using wordTrace_append hprefix tailTrace_826407
  have hstable : (prefixWord ++ tailWord_826407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826407).length < 2 ^ (prefixWord ++ tailWord_826407).sum := by decide
  have hdescent : baseEnd_826407 < baseStart_826407 := by decide
  rcases family_descends (prefixWord ++ tailWord_826407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826477 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 7]
def baseStart_826477 : Nat := 118140960795 + 826477 * 2 ^ 59
def prefixEnd_826477 : Nat := 4983230072969 + 3 ^ 40 * 826477 * 2
def baseEnd_826477 : Nat := 188613311504919172727381

theorem tailTrace_826477 : CollatzResearch.WordTrace tailWord_826477 prefixEnd_826477 188613311504919172727381 := by
  unfold tailWord_826477
  simp only [CollatzResearch.WordTrace]
  refine ⟨30144092626822454879101685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20096061751214969919401123 30144092626822454879101685)
  ·
    refine ⟨2826008683764605144915783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30144092626822454879101685 2826008683764605144915783)
    ·
      refine ⟨4239013025646907717373675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826008683764605144915783 4239013025646907717373675)
      ·
        refine ⟨6358519538470361576060513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239013025646907717373675 6358519538470361576060513)
        ·
          refine ⟨4768889653852771182045385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6358519538470361576060513 4768889653852771182045385)
          ·
            refine ⟨3576667240389578386534039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768889653852771182045385 3576667240389578386534039)
            ·
              refine ⟨5365000860584367579801059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576667240389578386534039 5365000860584367579801059)
              ·
                refine ⟨8047501290876551369701589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365000860584367579801059 8047501290876551369701589)
                ·
                  refine ⟨188613311504919172727381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8047501290876551369701589 188613311504919172727381)
                  ·
                    rfl

theorem cell21_826477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_826477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826477 prefixEnd_826477 := by exact prefixLift 826477
  have htrace : WordTrace (prefixWord ++ tailWord_826477) baseStart_826477 baseEnd_826477 := by
    simpa [prefixWord, tailWord_826477, baseEnd_826477] using wordTrace_append hprefix tailTrace_826477
  have hstable : (prefixWord ++ tailWord_826477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826477).length < 2 ^ (prefixWord ++ tailWord_826477).sum := by decide
  have hdescent : baseEnd_826477 < baseStart_826477 := by decide
  rcases family_descends (prefixWord ++ tailWord_826477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826525 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 4]
def baseStart_826525 : Nat := 118140960795 + 826525 * 2 ^ 59
def prefixEnd_826525 : Nat := 4983230072969 + 3 ^ 40 * 826525 * 2
def baseEnd_826525 : Nat := 188624265758881755927283

theorem tailTrace_826525 : CollatzResearch.WordTrace tailWord_826525 prefixEnd_826525 188624265758881755927283 := by
  unfold tailWord_826525
  simp only [CollatzResearch.WordTrace]
  refine ⟨30145843330648559076849029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20097228887099039384566019 30145843330648559076849029)
  ·
    refine ⟨5652345624496604826909193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30145843330648559076849029 5652345624496604826909193)
    ·
      refine ⟨4239259218372453620181895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5652345624496604826909193 4239259218372453620181895)
      ·
        refine ⟨6358888827558680430272843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239259218372453620181895 6358888827558680430272843)
        ·
          refine ⟨9538333241338020645409265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358888827558680430272843 9538333241338020645409265)
          ·
            refine ⟨7153749931003515484056949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9538333241338020645409265 7153749931003515484056949)
            ·
              refine ⟨670664056031579576630339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7153749931003515484056949 670664056031579576630339)
              ·
                refine ⟨1005996084047369364945509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670664056031579576630339 1005996084047369364945509)
                ·
                  refine ⟨188624265758881755927283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1005996084047369364945509 188624265758881755927283)
                  ·
                    rfl

theorem cell21_826525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_826525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826525 prefixEnd_826525 := by exact prefixLift 826525
  have htrace : WordTrace (prefixWord ++ tailWord_826525) baseStart_826525 baseEnd_826525 := by
    simpa [prefixWord, tailWord_826525, baseEnd_826525] using wordTrace_append hprefix tailTrace_826525
  have hstable : (prefixWord ++ tailWord_826525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826525).length < 2 ^ (prefixWord ++ tailWord_826525).sum := by decide
  have hdescent : baseEnd_826525 < baseStart_826525 := by decide
  rcases family_descends (prefixWord ++ tailWord_826525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826562 : List Nat := [3, 5, 1, 1, 2, 1, 3, 2, 3]
def baseStart_826562 : Nat := 118140960795 + 826562 * 2 ^ 59
def prefixEnd_826562 : Nat := 4983230072969 + 3 ^ 40 * 826562 * 2
def baseEnd_826562 : Nat := 188632709662977913810541

theorem tailTrace_826562 : CollatzResearch.WordTrace tailWord_826562 prefixEnd_826562 188632709662977913810541 := by
  unfold tailWord_826562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536798207878628598986485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20098128554343009597297293 7536798207878628598986485)
  ·
    refine ⟨706574831988621431154983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7536798207878628598986485 706574831988621431154983)
    ·
      refine ⟨1059862247982932146732475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706574831988621431154983 1059862247982932146732475)
      ·
        refine ⟨1589793371974398220098713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059862247982932146732475 1589793371974398220098713)
        ·
          refine ⟨1192345028980798665074035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589793371974398220098713 1192345028980798665074035)
          ·
            refine ⟨1788517543471197997611053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192345028980798665074035 1788517543471197997611053)
            ·
              refine ⟨670694078801699249104145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1788517543471197997611053 670694078801699249104145)
              ·
                refine ⟨503020559101274436828109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670694078801699249104145 503020559101274436828109)
                ·
                  refine ⟨188632709662977913810541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503020559101274436828109 188632709662977913810541)
                  ·
                    rfl

theorem cell21_826562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_826562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826562 prefixEnd_826562 := by exact prefixLift 826562
  have htrace : WordTrace (prefixWord ++ tailWord_826562) baseStart_826562 baseEnd_826562 := by
    simpa [prefixWord, tailWord_826562, baseEnd_826562] using wordTrace_append hprefix tailTrace_826562
  have hstable : (prefixWord ++ tailWord_826562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826562).length < 2 ^ (prefixWord ++ tailWord_826562).sum := by decide
  have hdescent : baseEnd_826562 < baseStart_826562 := by decide
  rcases family_descends (prefixWord ++ tailWord_826562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826570 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_826570 : Nat := 118140960795 + 826570 * 2 ^ 59
def prefixEnd_826570 : Nat := 4983230072969 + 3 ^ 40 * 826570 * 2
def baseEnd_826570 : Nat := 188634535371971677677191

theorem tailTrace_826570 : CollatzResearch.WordTrace tailWord_826570 prefixEnd_826570 188634535371971677677191 := by
  unfold tailWord_826570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536871153871382940559291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20098323076990354508158109 7536871153871382940559291)
  ·
    refine ⟨11305306730807074410838937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7536871153871382940559291 11305306730807074410838937)
    ·
      refine ⟨8478980048105305808129203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11305306730807074410838937 8478980048105305808129203)
      ·
        refine ⟨12718470072157958712193805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478980048105305808129203 12718470072157958712193805)
        ·
          refine ⟨4769426277059234517072677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12718470072157958712193805 4769426277059234517072677)
          ·
            refine ⟨894267426948606471951127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4769426277059234517072677 894267426948606471951127)
            ·
              refine ⟨1341401140422909707926691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894267426948606471951127 1341401140422909707926691)
              ·
                refine ⟨2012101710634364561890037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341401140422909707926691 2012101710634364561890037)
                ·
                  refine ⟨188634535371971677677191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2012101710634364561890037 188634535371971677677191)
                  ·
                    rfl

theorem cell21_826570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_826570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826570 prefixEnd_826570 := by exact prefixLift 826570
  have htrace : WordTrace (prefixWord ++ tailWord_826570) baseStart_826570 baseEnd_826570 := by
    simpa [prefixWord, tailWord_826570, baseEnd_826570] using wordTrace_append hprefix tailTrace_826570
  have hstable : (prefixWord ++ tailWord_826570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826570).length < 2 ^ (prefixWord ++ tailWord_826570).sum := by decide
  have hdescent : baseEnd_826570 < baseStart_826570 := by decide
  rcases family_descends (prefixWord ++ tailWord_826570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826573 : List Nat := [1, 6, 2, 2, 1, 1, 2, 6]
def baseStart_826573 : Nat := 118140960795 + 826573 * 2 ^ 59
def prefixEnd_826573 : Nat := 4983230072969 + 3 ^ 40 * 826573 * 2
def baseEnd_826573 : Nat := 62878406670948113042395

theorem tailTrace_826573 : CollatzResearch.WordTrace tailWord_826573 prefixEnd_826573 62878406670948113042395 := by
  unfold tailWord_826573
  simp only [CollatzResearch.WordTrace]
  refine ⟨30147594034474663274596373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20098396022983108849730915 30147594034474663274596373)
  ·
    refine ⟨1413168470365999840996705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30147594034474663274596373 1413168470365999840996705)
    ·
      refine ⟨1059876352774499880747529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1413168470365999840996705 1059876352774499880747529)
      ·
        refine ⟨794907264580874910560647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059876352774499880747529 794907264580874910560647)
        ·
          refine ⟨1192360896871312365840971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794907264580874910560647 1192360896871312365840971)
          ·
            refine ⟨1788541345306968548761457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192360896871312365840971 1788541345306968548761457)
            ·
              refine ⟨1341406008980226411571093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788541345306968548761457 1341406008980226411571093)
              ·
                refine ⟨62878406670948113042395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1341406008980226411571093 62878406670948113042395)
                ·
                  rfl

theorem cell21_826573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 6].length) (baseStart_826573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826573 prefixEnd_826573 := by exact prefixLift 826573
  have htrace : WordTrace (prefixWord ++ tailWord_826573) baseStart_826573 baseEnd_826573 := by
    simpa [prefixWord, tailWord_826573, baseEnd_826573] using wordTrace_append hprefix tailTrace_826573
  have hstable : (prefixWord ++ tailWord_826573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826573).length < 2 ^ (prefixWord ++ tailWord_826573).sum := by decide
  have hdescent : baseEnd_826573 < baseStart_826573 := by decide
  rcases family_descends (prefixWord ++ tailWord_826573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826632 : List Nat := [2, 1, 3, 2, 5, 1, 1, 6]
def baseStart_826632 : Nat := 118140960795 + 826632 * 2 ^ 59
def prefixEnd_826632 : Nat := 4983230072969 + 3 ^ 40 * 826632 * 2
def baseEnd_826632 : Nat := 62882894872224449214577

theorem tailTrace_826632 : CollatzResearch.WordTrace tailWord_826632 prefixEnd_826632 62882894872224449214577 := by
  unfold tailWord_826632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074872970630458175497075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20099830627507277567329433 15074872970630458175497075)
  ·
    refine ⟨22612309455945687263245613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15074872970630458175497075 22612309455945687263245613)
    ·
      refine ⟨8479616045979632723717105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22612309455945687263245613 8479616045979632723717105)
      ·
        refine ⟨6359712034484724542787829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8479616045979632723717105 6359712034484724542787829)
        ·
          refine ⟨596223003232942925886359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6359712034484724542787829 596223003232942925886359)
          ·
            refine ⟨894334504849414388829539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596223003232942925886359 894334504849414388829539)
            ·
              refine ⟨1341501757274121583244309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894334504849414388829539 1341501757274121583244309)
              ·
                refine ⟨62882894872224449214577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1341501757274121583244309 62882894872224449214577)
                ·
                  rfl

theorem cell21_826632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_826632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826632 prefixEnd_826632 := by exact prefixLift 826632
  have htrace : WordTrace (prefixWord ++ tailWord_826632) baseStart_826632 baseEnd_826632 := by
    simpa [prefixWord, tailWord_826632, baseEnd_826632] using wordTrace_append hprefix tailTrace_826632
  have hstable : (prefixWord ++ tailWord_826632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826632).length < 2 ^ (prefixWord ++ tailWord_826632).sum := by decide
  have hdescent : baseEnd_826632 < baseStart_826632 := by decide
  rcases family_descends (prefixWord ++ tailWord_826632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826674 : List Nat := [3, 2, 1, 1, 4, 2, 8]
def baseStart_826674 : Nat := 118140960795 + 826674 * 2 ^ 59
def prefixEnd_826674 : Nat := 4983230072969 + 3 ^ 40 * 826674 * 2
def baseEnd_826674 : Nat := 20962029954321178660405

theorem tailTrace_826674 : CollatzResearch.WordTrace tailWord_826674 prefixEnd_826674 20962029954321178660405 := by
  unfold tailWord_826674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537819451777189381005769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20100851871405838349348717 7537819451777189381005769)
  ·
    refine ⟨5653364588832892035754327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7537819451777189381005769 5653364588832892035754327)
    ·
      refine ⟨8480046883249338053631491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653364588832892035754327 8480046883249338053631491)
      ·
        refine ⟨12720070324874007080447237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480046883249338053631491 12720070324874007080447237)
        ·
          refine ⟨2385013185913876327583857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12720070324874007080447237 2385013185913876327583857)
          ·
            refine ⟨1788759889435407245687893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385013185913876327583857 1788759889435407245687893)
            ·
              refine ⟨20962029954321178660405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1788759889435407245687893 20962029954321178660405)
              ·
                rfl

theorem cell21_826674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 8].length) (baseStart_826674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826674 prefixEnd_826674 := by exact prefixLift 826674
  have htrace : WordTrace (prefixWord ++ tailWord_826674) baseStart_826674 baseEnd_826674 := by
    simpa [prefixWord, tailWord_826674, baseEnd_826674] using wordTrace_append hprefix tailTrace_826674
  have hstable : (prefixWord ++ tailWord_826674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826674).length < 2 ^ (prefixWord ++ tailWord_826674).sum := by decide
  have hdescent : baseEnd_826674 < baseStart_826674 := by decide
  rcases family_descends (prefixWord ++ tailWord_826674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826677 : List Nat := [1, 3, 3, 1, 2, 4, 1, 2, 4]
def baseStart_826677 : Nat := 118140960795 + 826677 * 2 ^ 59
def prefixEnd_826677 : Nat := 4983230072969 + 3 ^ 40 * 826677 * 2
def baseEnd_826677 : Nat := 188658954229763269393639

theorem tailTrace_826677 : CollatzResearch.WordTrace tailWord_826677 prefixEnd_826677 188658954229763269393639 := by
  unfold tailWord_826677
  simp only [CollatzResearch.WordTrace]
  refine ⟨30151387226097889036382285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20100924817398592690921523 30151387226097889036382285)
  ·
    refine ⟨11306770209786708388643357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30151387226097889036382285 11306770209786708388643357)
    ·
      refine ⟨4240038828670015645741259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11306770209786708388643357 4240038828670015645741259)
      ·
        refine ⟨6360058243005023468611889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240038828670015645741259 6360058243005023468611889)
        ·
          refine ⟨4770043682253767601458917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6360058243005023468611889 4770043682253767601458917)
          ·
            refine ⟨894383190422581425273547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4770043682253767601458917 894383190422581425273547)
            ·
              refine ⟨1341574785633872137910321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894383190422581425273547 1341574785633872137910321)
              ·
                refine ⟨1006181089225404103432741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341574785633872137910321 1006181089225404103432741)
                ·
                  refine ⟨188658954229763269393639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006181089225404103432741 188658954229763269393639)
                  ·
                    rfl

theorem cell21_826677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_826677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826677 prefixEnd_826677 := by exact prefixLift 826677
  have htrace : WordTrace (prefixWord ++ tailWord_826677) baseStart_826677 baseEnd_826677 := by
    simpa [prefixWord, tailWord_826677, baseEnd_826677] using wordTrace_append hprefix tailTrace_826677
  have hstable : (prefixWord ++ tailWord_826677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826677).length < 2 ^ (prefixWord ++ tailWord_826677).sum := by decide
  have hdescent : baseEnd_826677 < baseStart_826677 := by decide
  rcases family_descends (prefixWord ++ tailWord_826677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826753 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 4]
def baseStart_826753 : Nat := 118140960795 + 826753 * 2 ^ 59
def prefixEnd_826753 : Nat := 4983230072969 + 3 ^ 40 * 826753 * 2
def baseEnd_826753 : Nat := 188676298465204026126817

theorem tailTrace_826753 : CollatzResearch.WordTrace tailWord_826753 prefixEnd_826753 188676298465204026126817 := by
  unfold tailWord_826753
  simp only [CollatzResearch.WordTrace]
  refine ⟨30154159173822554016148913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20102772782548369344099275 30154159173822554016148913)
  ·
    refine ⟨22615619380366915512111685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30154159173822554016148913 22615619380366915512111685)
    ·
      refine ⟨4240428633818796658520941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22615619380366915512111685 4240428633818796658520941)
      ·
        refine ⟨1590160737682048746945353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4240428633818796658520941 1590160737682048746945353)
        ·
          refine ⟨1192620553261536560209015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1590160737682048746945353 1192620553261536560209015)
          ·
            refine ⟨1788930829892304840313523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192620553261536560209015 1788930829892304840313523)
            ·
              refine ⟨2683396244838457260470285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788930829892304840313523 2683396244838457260470285)
              ·
                refine ⟨1006273591814421472676357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683396244838457260470285 1006273591814421472676357)
                ·
                  refine ⟨188676298465204026126817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006273591814421472676357 188676298465204026126817)
                  ·
                    rfl

theorem cell21_826753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_826753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826753 prefixEnd_826753 := by exact prefixLift 826753
  have htrace : WordTrace (prefixWord ++ tailWord_826753) baseStart_826753 baseEnd_826753 := by
    simpa [prefixWord, tailWord_826753, baseEnd_826753] using wordTrace_append hprefix tailTrace_826753
  have hstable : (prefixWord ++ tailWord_826753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826753).length < 2 ^ (prefixWord ++ tailWord_826753).sum := by decide
  have hdescent : baseEnd_826753 < baseStart_826753 := by decide
  rcases family_descends (prefixWord ++ tailWord_826753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826764 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_826764 : Nat := 118140960795 + 826764 * 2 ^ 59
def prefixEnd_826764 : Nat := 4983230072969 + 3 ^ 40 * 826764 * 2
def baseEnd_826764 : Nat := 188678808815070451443461

theorem tailTrace_826764 : CollatzResearch.WordTrace tailWord_826764 prefixEnd_826764 188678808815070451443461 := by
  unfold tailWord_826764
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077280188391351447399673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20103040251188468596532897 15077280188391351447399673)
  ·
    refine ⟨11307960141293513585549755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15077280188391351447399673 11307960141293513585549755)
    ·
      refine ⟨16961940211940270378324633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11307960141293513585549755 16961940211940270378324633)
      ·
        refine ⟨12721455158955202783743475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16961940211940270378324633 12721455158955202783743475)
        ·
          refine ⟨19082182738432804175615213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721455158955202783743475 19082182738432804175615213)
          ·
            refine ⟨7155818526912301565855705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19082182738432804175615213 7155818526912301565855705)
            ·
              refine ⟨5366863895184226174391779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7155818526912301565855705 5366863895184226174391779)
              ·
                refine ⟨8050295842776339261587669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366863895184226174391779 8050295842776339261587669)
                ·
                  refine ⟨188678808815070451443461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8050295842776339261587669 188678808815070451443461)
                  ·
                    rfl

theorem cell21_826764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_826764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826764 prefixEnd_826764 := by exact prefixLift 826764
  have htrace : WordTrace (prefixWord ++ tailWord_826764) baseStart_826764 baseEnd_826764 := by
    simpa [prefixWord, tailWord_826764, baseEnd_826764] using wordTrace_append hprefix tailTrace_826764
  have hstable : (prefixWord ++ tailWord_826764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826764).length < 2 ^ (prefixWord ++ tailWord_826764).sum := by decide
  have hdescent : baseEnd_826764 < baseStart_826764 := by decide
  rcases family_descends (prefixWord ++ tailWord_826764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826891 : List Nat := [1, 1, 1, 1, 8, 2, 1, 3, 3]
def baseStart_826891 : Nat := 118140960795 + 826891 * 2 ^ 59
def prefixEnd_826891 : Nat := 4983230072969 + 3 ^ 40 * 826891 * 2
def baseEnd_826891 : Nat := 188707791945346452826535

theorem tailTrace_826891 : CollatzResearch.WordTrace tailWord_826891 prefixEnd_826891 188707791945346452826535 := by
  unfold tailWord_826891
  simp only [CollatzResearch.WordTrace]
  refine ⟨30159192447322603584672527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20106128298215069056448351 30159192447322603584672527)
  ·
    refine ⟨45238788670983905377008791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30159192447322603584672527 45238788670983905377008791)
    ·
      refine ⟨67858183006475858065513187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45238788670983905377008791 67858183006475858065513187)
      ·
        refine ⟨101787274509713787098269781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67858183006475858065513187 101787274509713787098269781)
        ·
          refine ⟨1192819623160708442557849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 101787274509713787098269781 1192819623160708442557849)
          ·
            refine ⟨894614717370531331918387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192819623160708442557849 894614717370531331918387)
            ·
              refine ⟨1341922076055796997877581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894614717370531331918387 1341922076055796997877581)
              ·
                refine ⟨503220778520923874204093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1341922076055796997877581 503220778520923874204093)
                ·
                  refine ⟨188707791945346452826535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503220778520923874204093 188707791945346452826535)
                  ·
                    rfl

theorem cell21_826891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 3, 3].length) (baseStart_826891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826891 prefixEnd_826891 := by exact prefixLift 826891
  have htrace : WordTrace (prefixWord ++ tailWord_826891) baseStart_826891 baseEnd_826891 := by
    simpa [prefixWord, tailWord_826891, baseEnd_826891] using wordTrace_append hprefix tailTrace_826891
  have hstable : (prefixWord ++ tailWord_826891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826891).length < 2 ^ (prefixWord ++ tailWord_826891).sum := by decide
  have hdescent : baseEnd_826891 < baseStart_826891 := by decide
  rcases family_descends (prefixWord ++ tailWord_826891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826964 : List Nat := [2, 4, 1, 1, 1, 2, 4, 2, 4]
def baseStart_826964 : Nat := 118140960795 + 826964 * 2 ^ 59
def prefixEnd_826964 : Nat := 4983230072969 + 3 ^ 40 * 826964 * 2
def baseEnd_826964 : Nat := 188724451539914548109719

theorem tailTrace_826964 : CollatzResearch.WordTrace tailWord_826964 prefixEnd_826964 188724451539914548109719 := by
  unfold tailWord_826964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080927488029068526039973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20107903317372091368053297 15080927488029068526039973)
  ·
    refine ⟨2827673904005450348632495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15080927488029068526039973 2827673904005450348632495)
    ·
      refine ⟨4241510856008175522948743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827673904005450348632495 4241510856008175522948743)
      ·
        refine ⟨6362266284012263284423115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241510856008175522948743 6362266284012263284423115)
        ·
          refine ⟨9543399426018394926634673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362266284012263284423115 9543399426018394926634673)
          ·
            refine ⟨7157549569513796194976005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9543399426018394926634673 7157549569513796194976005)
            ·
              refine ⟨1342040544283836786558001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7157549569513796194976005 1342040544283836786558001)
              ·
                refine ⟨1006530408212877589918501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342040544283836786558001 1006530408212877589918501)
                ·
                  refine ⟨188724451539914548109719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006530408212877589918501 188724451539914548109719)
                  ·
                    rfl

theorem cell21_826964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_826964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826964 prefixEnd_826964 := by exact prefixLift 826964
  have htrace : WordTrace (prefixWord ++ tailWord_826964) baseStart_826964 baseEnd_826964 := by
    simpa [prefixWord, tailWord_826964, baseEnd_826964] using wordTrace_append hprefix tailTrace_826964
  have hstable : (prefixWord ++ tailWord_826964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826964).length < 2 ^ (prefixWord ++ tailWord_826964).sum := by decide
  have hdescent : baseEnd_826964 < baseStart_826964 := by decide
  rcases family_descends (prefixWord ++ tailWord_826964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826967 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 3]
def baseStart_826967 : Nat := 118140960795 + 826967 * 2 ^ 59
def prefixEnd_826967 : Nat := 4983230072969 + 3 ^ 40 * 826967 * 2
def baseEnd_826967 : Nat := 188725136180787209559713

theorem tailTrace_826967 : CollatzResearch.WordTrace tailWord_826967 prefixEnd_826967 188725136180787209559713 := by
  unfold tailWord_826967
  simp only [CollatzResearch.WordTrace]
  refine ⟨30161964395047268564439155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20107976263364845709626103 30161964395047268564439155)
  ·
    refine ⟨45242946592570902846658733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30161964395047268564439155 45242946592570902846658733)
    ·
      refine ⟨16966104972214088567497025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45242946592570902846658733 16966104972214088567497025)
      ·
        refine ⟨12724578729160566425622769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16966104972214088567497025 12724578729160566425622769)
        ·
          refine ⟨9543434046870424819217077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12724578729160566425622769 9543434046870424819217077)
          ·
            refine ⟨894696941894102326801601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9543434046870424819217077 894696941894102326801601)
            ·
              refine ⟨671022706420576745101201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894696941894102326801601 671022706420576745101201)
              ·
                refine ⟨503267029815432558825901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671022706420576745101201 503267029815432558825901)
                ·
                  refine ⟨188725136180787209559713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503267029815432558825901 188725136180787209559713)
                  ·
                    rfl

theorem cell21_826967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3].length) (baseStart_826967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826967 prefixEnd_826967 := by exact prefixLift 826967
  have htrace : WordTrace (prefixWord ++ tailWord_826967) baseStart_826967 baseEnd_826967 := by
    simpa [prefixWord, tailWord_826967, baseEnd_826967] using wordTrace_append hprefix tailTrace_826967
  have hstable : (prefixWord ++ tailWord_826967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826967).length < 2 ^ (prefixWord ++ tailWord_826967).sum := by decide
  have hdescent : baseEnd_826967 < baseStart_826967 := by decide
  rcases family_descends (prefixWord ++ tailWord_826967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826992 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_826992 : Nat := 118140960795 + 826992 * 2 ^ 59
def prefixEnd_826992 : Nat := 4983230072969 + 3 ^ 40 * 826992 * 2
def baseEnd_826992 : Nat := 188730841521392721642995

theorem tailTrace_826992 : CollatzResearch.WordTrace tailWord_826992 prefixEnd_826992 188730841521392721642995 := by
  unfold tailWord_826992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15081438109978348917049615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20108584146637798556066153 15081438109978348917049615)
  ·
    refine ⟨22622157164967523375574423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15081438109978348917049615 22622157164967523375574423)
    ·
      refine ⟨33933235747451285063361635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22622157164967523375574423 33933235747451285063361635)
      ·
        refine ⟨50899853621176927595042453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33933235747451285063361635 50899853621176927595042453)
        ·
          refine ⟨2385930638492668481017615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50899853621176927595042453 2385930638492668481017615)
          ·
            refine ⟨3578895957739002721526423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385930638492668481017615 3578895957739002721526423)
            ·
              refine ⟨5368343936608504082289635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578895957739002721526423 5368343936608504082289635)
              ·
                refine ⟨8052515904912756123434453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368343936608504082289635 8052515904912756123434453)
                ·
                  refine ⟨188730841521392721642995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8052515904912756123434453 188730841521392721642995)
                  ·
                    rfl

theorem cell21_826992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_826992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_826992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_826992 prefixEnd_826992 := by exact prefixLift 826992
  have htrace : WordTrace (prefixWord ++ tailWord_826992) baseStart_826992 baseEnd_826992 := by
    simpa [prefixWord, tailWord_826992, baseEnd_826992] using wordTrace_append hprefix tailTrace_826992
  have hstable : (prefixWord ++ tailWord_826992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826992).length < 2 ^ (prefixWord ++ tailWord_826992).sum := by decide
  have hdescent : baseEnd_826992 < baseStart_826992 := by decide
  rcases family_descends (prefixWord ++ tailWord_826992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827026 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 5]
def baseStart_827026 : Nat := 118140960795 + 827026 * 2 ^ 59
def prefixEnd_827026 : Nat := 4983230072969 + 3 ^ 40 * 827026 * 2
def baseEnd_827026 : Nat := 188738600784616218076259

theorem tailTrace_827026 : CollatzResearch.WordTrace tailWord_827026 prefixEnd_827026 188738600784616218076259 := by
  unfold tailWord_827026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541029075458380410209233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20109410867889014427224621 7541029075458380410209233)
  ·
    refine ⟨5655771806593785307656925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7541029075458380410209233 5655771806593785307656925)
    ·
      refine ⟨2120914427472669490371347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5655771806593785307656925 2120914427472669490371347)
      ·
        refine ⟨3181371641209004235557021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120914427472669490371347 3181371641209004235557021)
        ·
          refine ⟨1193014365453376588333883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3181371641209004235557021 1193014365453376588333883)
          ·
            refine ⟨1789521548180064882500825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193014365453376588333883 1789521548180064882500825)
            ·
              refine ⟨1342141161135048661875619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789521548180064882500825 1342141161135048661875619)
              ·
                refine ⟨2013211741702572992813429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342141161135048661875619 2013211741702572992813429)
                ·
                  refine ⟨188738600784616218076259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2013211741702572992813429 188738600784616218076259)
                  ·
                    rfl

theorem cell21_827026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_827026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827026 prefixEnd_827026 := by exact prefixLift 827026
  have htrace : WordTrace (prefixWord ++ tailWord_827026) baseStart_827026 baseEnd_827026 := by
    simpa [prefixWord, tailWord_827026, baseEnd_827026] using wordTrace_append hprefix tailTrace_827026
  have hstable : (prefixWord ++ tailWord_827026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827026).length < 2 ^ (prefixWord ++ tailWord_827026).sum := by decide
  have hdescent : baseEnd_827026 < baseStart_827026 := by decide
  rcases family_descends (prefixWord ++ tailWord_827026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827037 : List Nat := [1, 4, 2, 1, 1, 1, 1, 10]
def baseStart_827037 : Nat := 118140960795 + 827037 * 2 ^ 59
def prefixEnd_827037 : Nat := 4983230072969 + 3 ^ 40 * 827037 * 2
def baseEnd_827037 : Nat := 62913703711494214464301

theorem tailTrace_827037 : CollatzResearch.WordTrace tailWord_827037 prefixEnd_827037 62913703711494214464301 := by
  unfold tailWord_827037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164517504793670519487365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20109678336529113679658243 30164517504793670519487365)
  ·
    refine ⟨5655847032148813222403881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30164517504793670519487365 5655847032148813222403881)
    ·
      refine ⟨4241885274111609916802911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5655847032148813222403881 4241885274111609916802911)
      ·
        refine ⟨6362827911167414875204367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241885274111609916802911 6362827911167414875204367)
        ·
          refine ⟨9544241866751122312806551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6362827911167414875204367 9544241866751122312806551)
          ·
            refine ⟨14316362800126683469209827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544241866751122312806551 14316362800126683469209827)
            ·
              refine ⟨21474544200190025203814741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14316362800126683469209827 21474544200190025203814741)
              ·
                refine ⟨62913703711494214464301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21474544200190025203814741 62913703711494214464301)
                ·
                  rfl

theorem cell21_827037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_827037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827037 prefixEnd_827037 := by exact prefixLift 827037
  have htrace : WordTrace (prefixWord ++ tailWord_827037) baseStart_827037 baseEnd_827037 := by
    simpa [prefixWord, tailWord_827037, baseEnd_827037] using wordTrace_append hprefix tailTrace_827037
  have hstable : (prefixWord ++ tailWord_827037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827037).length < 2 ^ (prefixWord ++ tailWord_827037).sum := by decide
  have hdescent : baseEnd_827037 < baseStart_827037 := by decide
  rcases family_descends (prefixWord ++ tailWord_827037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827144 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 5]
def baseStart_827144 : Nat := 118140960795 + 827144 * 2 ^ 59
def prefixEnd_827144 : Nat := 4983230072969 + 3 ^ 40 * 827144 * 2
def baseEnd_827144 : Nat := 188765529992274235109351

theorem tailTrace_827144 : CollatzResearch.WordTrace tailWord_827144 prefixEnd_827144 188765529992274235109351 := by
  unfold tailWord_827144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084210057703013896816243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20112280076937351862421657 15084210057703013896816243)
  ·
    refine ⟨22626315086554520845224365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15084210057703013896816243 22626315086554520845224365)
    ·
      refine ⟨8484868157457945316959137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22626315086554520845224365 8484868157457945316959137)
      ·
        refine ⟨6363651118093458987719353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8484868157457945316959137 6363651118093458987719353)
        ·
          refine ⟨4772738338570094240789515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6363651118093458987719353 4772738338570094240789515)
          ·
            refine ⟨7159107507855141361184273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772738338570094240789515 7159107507855141361184273)
            ·
              refine ⟨5369330630891356020888205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7159107507855141361184273 5369330630891356020888205)
              ·
                refine ⟨2013498986584258507833077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5369330630891356020888205 2013498986584258507833077)
                ·
                  refine ⟨188765529992274235109351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2013498986584258507833077 188765529992274235109351)
                  ·
                    rfl

theorem cell21_827144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_827144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827144 prefixEnd_827144 := by exact prefixLift 827144
  have htrace : WordTrace (prefixWord ++ tailWord_827144) baseStart_827144 baseEnd_827144 := by
    simpa [prefixWord, tailWord_827144, baseEnd_827144] using wordTrace_append hprefix tailTrace_827144
  have hstable : (prefixWord ++ tailWord_827144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827144).length < 2 ^ (prefixWord ++ tailWord_827144).sum := by decide
  have hdescent : baseEnd_827144 < baseStart_827144 := by decide
  rcases family_descends (prefixWord ++ tailWord_827144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827192 : List Nat := [2, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_827192 : Nat := 118140960795 + 827192 * 2 ^ 59
def prefixEnd_827192 : Nat := 4983230072969 + 3 ^ 40 * 827192 * 2
def baseEnd_827192 : Nat := 188776484246236818309253

theorem tailTrace_827192 : CollatzResearch.WordTrace tailWord_827192 prefixEnd_827192 188776484246236818309253 := by
  unfold tailWord_827192
  simp only [CollatzResearch.WordTrace]
  refine ⟨15085085409616065995689915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20113447212821421327586553 15085085409616065995689915)
  ·
    refine ⟨22627628114424098993534873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15085085409616065995689915 22627628114424098993534873)
    ·
      refine ⟨16970721085818074245151155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22627628114424098993534873 16970721085818074245151155)
      ·
        refine ⟨25456081628727111367726733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16970721085818074245151155 25456081628727111367726733)
        ·
          refine ⟨9546030610772666762897525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25456081628727111367726733 9546030610772666762897525)
          ·
            refine ⟨894940369759937509021643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9546030610772666762897525 894940369759937509021643)
            ·
              refine ⟨1342410554639906263532465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894940369759937509021643 1342410554639906263532465)
              ·
                refine ⟨1006807915979929697649349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342410554639906263532465 1006807915979929697649349)
                ·
                  refine ⟨188776484246236818309253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006807915979929697649349 188776484246236818309253)
                  ·
                    rfl

theorem cell21_827192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_827192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827192 prefixEnd_827192 := by exact prefixLift 827192
  have htrace : WordTrace (prefixWord ++ tailWord_827192) baseStart_827192 baseEnd_827192 := by
    simpa [prefixWord, tailWord_827192, baseEnd_827192] using wordTrace_append hprefix tailTrace_827192
  have hstable : (prefixWord ++ tailWord_827192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827192).length < 2 ^ (prefixWord ++ tailWord_827192).sum := by decide
  have hdescent : baseEnd_827192 < baseStart_827192 := by decide
  rcases family_descends (prefixWord ++ tailWord_827192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827223 : List Nat := [1, 1, 3, 2, 5, 2, 2, 5]
def baseStart_827223 : Nat := 118140960795 + 827223 * 2 ^ 59
def prefixEnd_827223 : Nat := 4983230072969 + 3 ^ 40 * 827223 * 2
def baseEnd_827223 : Nat := 62927852956195884430841

theorem tailTrace_827223 : CollatzResearch.WordTrace tailWord_827223 prefixEnd_827223 62927852956195884430841 := by
  unfold tailWord_827223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171301482119824285758323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20114200988079882857172215 30171301482119824285758323)
  ·
    refine ⟨45256952223179736428637485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30171301482119824285758323 45256952223179736428637485)
    ·
      refine ⟨16971357083692401160739057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45256952223179736428637485 16971357083692401160739057)
      ·
        refine ⟨12728517812769300870554293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16971357083692401160739057 12728517812769300870554293)
        ·
          refine ⟨1193298544947121956614465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12728517812769300870554293 1193298544947121956614465)
          ·
            refine ⟨894973908710341467460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193298544947121956614465 894973908710341467460849)
            ·
              refine ⟨671230431532756100595637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 894973908710341467460849 671230431532756100595637)
              ·
                refine ⟨62927852956195884430841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671230431532756100595637 62927852956195884430841)
                ·
                  rfl

theorem cell21_827223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 5].length) (baseStart_827223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827223 prefixEnd_827223 := by exact prefixLift 827223
  have htrace : WordTrace (prefixWord ++ tailWord_827223) baseStart_827223 baseEnd_827223 := by
    simpa [prefixWord, tailWord_827223, baseEnd_827223] using wordTrace_append hprefix tailTrace_827223
  have hstable : (prefixWord ++ tailWord_827223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827223).length < 2 ^ (prefixWord ++ tailWord_827223).sum := by decide
  have hdescent : baseEnd_827223 < baseStart_827223 := by decide
  rcases family_descends (prefixWord ++ tailWord_827223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827268 : List Nat := [2, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_827268 : Nat := 118140960795 + 827268 * 2 ^ 59
def prefixEnd_827268 : Nat := 4983230072969 + 3 ^ 40 * 827268 * 2
def baseEnd_827268 : Nat := 188793828481677575042431

theorem tailTrace_827268 : CollatzResearch.WordTrace tailWord_827268 prefixEnd_827268 188793828481677575042431 := by
  unfold tailWord_827268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086471383478398485573229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20115295177971197980764305 15086471383478398485573229)
  ·
    refine ⟨5657426768804399432089961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15086471383478398485573229 5657426768804399432089961)
    ·
      refine ⟨4243070076603299574067471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5657426768804399432089961 4243070076603299574067471)
      ·
        refine ⟨6364605114904949361101207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243070076603299574067471 6364605114904949361101207)
        ·
          refine ⟨9546907672357424041651811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364605114904949361101207 9546907672357424041651811)
          ·
            refine ⟨14320361508536136062477717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546907672357424041651811 14320361508536136062477717)
            ·
              refine ⟨671266945712631377928643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14320361508536136062477717 671266945712631377928643)
              ·
                refine ⟨1006900418568947066892965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671266945712631377928643 1006900418568947066892965)
                ·
                  refine ⟨188793828481677575042431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1006900418568947066892965 188793828481677575042431)
                  ·
                    rfl

theorem cell21_827268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_827268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827268 prefixEnd_827268 := by exact prefixLift 827268
  have htrace : WordTrace (prefixWord ++ tailWord_827268) baseStart_827268 baseEnd_827268 := by
    simpa [prefixWord, tailWord_827268, baseEnd_827268] using wordTrace_append hprefix tailTrace_827268
  have hstable : (prefixWord ++ tailWord_827268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827268).length < 2 ^ (prefixWord ++ tailWord_827268).sum := by decide
  have hdescent : baseEnd_827268 < baseStart_827268 := by decide
  rcases family_descends (prefixWord ++ tailWord_827268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827282 : List Nat := [3, 2, 3, 2, 1, 1, 2, 7]
def baseStart_827282 : Nat := 118140960795 + 827282 * 2 ^ 59
def prefixEnd_827282 : Nat := 4983230072969 + 3 ^ 40 * 827282 * 2
def baseEnd_827282 : Nat := 62932341157472220603023

theorem tailTrace_827282 : CollatzResearch.WordTrace tailWord_827282 prefixEnd_827282 62932341157472220603023 := by
  unfold tailWord_827282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543363347226519340539025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20115635592604051574770733 7543363347226519340539025)
  ·
    refine ⟨5657522510419889505404269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7543363347226519340539025 5657522510419889505404269)
    ·
      refine ⟨2121570941407458564526601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5657522510419889505404269 2121570941407458564526601)
      ·
        refine ⟨1591178206055593923394951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121570941407458564526601 1591178206055593923394951)
        ·
          refine ⟨2386767309083390885092427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591178206055593923394951 2386767309083390885092427)
          ·
            refine ⟨3580150963625086327638641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386767309083390885092427 3580150963625086327638641)
            ·
              refine ⟨2685113222718814745728981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3580150963625086327638641 2685113222718814745728981)
              ·
                refine ⟨62932341157472220603023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2685113222718814745728981 62932341157472220603023)
                ·
                  rfl

theorem cell21_827282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_827282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827282 prefixEnd_827282 := by exact prefixLift 827282
  have htrace : WordTrace (prefixWord ++ tailWord_827282) baseStart_827282 baseEnd_827282 := by
    simpa [prefixWord, tailWord_827282, baseEnd_827282] using wordTrace_append hprefix tailTrace_827282
  have hstable : (prefixWord ++ tailWord_827282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827282).length < 2 ^ (prefixWord ++ tailWord_827282).sum := by decide
  have hdescent : baseEnd_827282 < baseStart_827282 := by decide
  rcases family_descends (prefixWord ++ tailWord_827282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827316 : List Nat := [2, 5, 2, 1, 2, 2, 1, 6]
def baseStart_827316 : Nat := 118140960795 + 827316 * 2 ^ 59
def prefixEnd_827316 : Nat := 4983230072969 + 3 ^ 40 * 827316 * 2
def baseEnd_827316 : Nat := 62934927578546719414111

theorem tailTrace_827316 : CollatzResearch.WordTrace tailWord_827316 prefixEnd_827316 62934927578546719414111 := by
  unfold tailWord_827316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087346735391450584446901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20116462313855267445929201 15087346735391450584446901)
  ·
    refine ⟨1414438756442948492291897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15087346735391450584446901 1414438756442948492291897)
    ·
      refine ⟨1060829067332211369218923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1414438756442948492291897 1060829067332211369218923)
      ·
        refine ⟨1591243600998317053828385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1060829067332211369218923 1591243600998317053828385)
        ·
          refine ⟨1193432700748737790371289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591243600998317053828385 1193432700748737790371289)
          ·
            refine ⟨895074525561553342778467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193432700748737790371289 895074525561553342778467)
            ·
              refine ⟨1342611788342330014167701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895074525561553342778467 1342611788342330014167701)
              ·
                refine ⟨62934927578546719414111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1342611788342330014167701 62934927578546719414111)
                ·
                  rfl

theorem cell21_827316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_827316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827316 prefixEnd_827316 := by exact prefixLift 827316
  have htrace : WordTrace (prefixWord ++ tailWord_827316) baseStart_827316 baseEnd_827316 := by
    simpa [prefixWord, tailWord_827316, baseEnd_827316] using wordTrace_append hprefix tailTrace_827316
  have hstable : (prefixWord ++ tailWord_827316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827316).length < 2 ^ (prefixWord ++ tailWord_827316).sum := by decide
  have hdescent : baseEnd_827316 < baseStart_827316 := by decide
  rcases family_descends (prefixWord ++ tailWord_827316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827398 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_827398 : Nat := 118140960795 + 827398 * 2 ^ 59
def prefixEnd_827398 : Nat := 4983230072969 + 3 ^ 40 * 827398 * 2
def baseEnd_827398 : Nat := 188823496252826237875499

theorem tailTrace_827398 : CollatzResearch.WordTrace tailWord_827398 prefixEnd_827398 188823496252826237875499 := by
  unfold tailWord_827398
  simp only [CollatzResearch.WordTrace]
  refine ⟨943052633015182161668089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20118456170990552782252565 943052633015182161668089)
  ·
    refine ⟨707289474761386621251067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 943052633015182161668089 707289474761386621251067)
    ·
      refine ⟨1060934212142079931876601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707289474761386621251067 1060934212142079931876601)
      ·
        refine ⟨795700659106559948907451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1060934212142079931876601 795700659106559948907451)
        ·
          refine ⟨1193550988659839923361177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795700659106559948907451 1193550988659839923361177)
          ·
            refine ⟨895163241494879942520883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193550988659839923361177 895163241494879942520883)
            ·
              refine ⟨1342744862242319913781325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895163241494879942520883 1342744862242319913781325)
              ·
                refine ⟨503529323340869967667997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1342744862242319913781325 503529323340869967667997)
                ·
                  refine ⟨188823496252826237875499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503529323340869967667997 188823496252826237875499)
                  ·
                    rfl

theorem cell21_827398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_827398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827398 prefixEnd_827398 := by exact prefixLift 827398
  have htrace : WordTrace (prefixWord ++ tailWord_827398) baseStart_827398 baseEnd_827398 := by
    simpa [prefixWord, tailWord_827398, baseEnd_827398] using wordTrace_append hprefix tailTrace_827398
  have hstable : (prefixWord ++ tailWord_827398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827398).length < 2 ^ (prefixWord ++ tailWord_827398).sum := by decide
  have hdescent : baseEnd_827398 < baseStart_827398 := by decide
  rcases family_descends (prefixWord ++ tailWord_827398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827434 : List Nat := [3, 1, 4, 1, 2, 2, 2, 6]
def baseStart_827434 : Nat := 118140960795 + 827434 * 2 ^ 59
def prefixEnd_827434 : Nat := 4983230072969 + 3 ^ 40 * 827434 * 2
def baseEnd_827434 : Nat := 62943903981099391758475

theorem tailTrace_827434 : CollatzResearch.WordTrace tailWord_827434 prefixEnd_827434 62943903981099391758475 := by
  unfold tailWord_827434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544749321088851830422339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20119331522903604881126237 7544749321088851830422339)
  ·
    refine ⟨11317123981633277745633509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7544749321088851830422339 11317123981633277745633509)
    ·
      refine ⟨2121960746556239577306283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11317123981633277745633509 2121960746556239577306283)
      ·
        refine ⟨3182941119834359365959425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121960746556239577306283 3182941119834359365959425)
        ·
          refine ⟨2387205839875769524469569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182941119834359365959425 2387205839875769524469569)
          ·
            refine ⟨1790404379906827143352177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2387205839875769524469569 1790404379906827143352177)
            ·
              refine ⟨1342803284930120357514133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790404379906827143352177 1342803284930120357514133)
              ·
                refine ⟨62943903981099391758475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1342803284930120357514133 62943903981099391758475)
                ·
                  rfl

theorem cell21_827434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_827434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827434 prefixEnd_827434 := by exact prefixLift 827434
  have htrace : WordTrace (prefixWord ++ tailWord_827434) baseStart_827434 baseEnd_827434 := by
    simpa [prefixWord, tailWord_827434, baseEnd_827434] using wordTrace_append hprefix tailTrace_827434
  have hstable : (prefixWord ++ tailWord_827434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827434).length < 2 ^ (prefixWord ++ tailWord_827434).sum := by decide
  have hdescent : baseEnd_827434 < baseStart_827434 := by decide
  rcases family_descends (prefixWord ++ tailWord_827434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827493 : List Nat := [1, 3, 1, 3, 2, 2, 3, 6]
def baseStart_827493 : Nat := 118140960795 + 827493 * 2 ^ 59
def prefixEnd_827493 : Nat := 4983230072969 + 3 ^ 40 * 827493 * 2
def baseEnd_827493 : Nat := 62948392182375727930657

theorem tailTrace_827493 : CollatzResearch.WordTrace tailWord_827493 prefixEnd_827493 62948392182375727930657 := by
  unfold tailWord_827493
  simp only [CollatzResearch.WordTrace]
  refine ⟨30181149191141660398087133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20120766127427773598724755 30181149191141660398087133)
  ·
    refine ⟨11317930946678122649282675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30181149191141660398087133 11317930946678122649282675)
    ·
      refine ⟨16976896420017183973924013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11317930946678122649282675 16976896420017183973924013)
      ·
        refine ⟨6366336157506443990221505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16976896420017183973924013 6366336157506443990221505)
        ·
          refine ⟨4774752118129832992666129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6366336157506443990221505 4774752118129832992666129)
          ·
            refine ⟨3581064088597374744499597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4774752118129832992666129 3581064088597374744499597)
            ·
              refine ⟨1342899033224015529187349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3581064088597374744499597 1342899033224015529187349)
              ·
                refine ⟨62948392182375727930657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1342899033224015529187349 62948392182375727930657)
                ·
                  rfl

theorem cell21_827493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_827493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827493 prefixEnd_827493 := by exact prefixLift 827493
  have htrace : WordTrace (prefixWord ++ tailWord_827493) baseStart_827493 baseEnd_827493 := by
    simpa [prefixWord, tailWord_827493, baseEnd_827493] using wordTrace_append hprefix tailTrace_827493
  have hstable : (prefixWord ++ tailWord_827493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827493).length < 2 ^ (prefixWord ++ tailWord_827493).sum := by decide
  have hdescent : baseEnd_827493 < baseStart_827493 := by decide
  rcases family_descends (prefixWord ++ tailWord_827493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827606 : List Nat := [5, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_827606 : Nat := 118140960795 + 827606 * 2 ^ 59
def prefixEnd_827606 : Nat := 4983230072969 + 3 ^ 40 * 827606 * 2
def baseEnd_827606 : Nat := 188870964686664098408407

theorem tailTrace_827606 : CollatzResearch.WordTrace tailWord_827606 prefixEnd_827606 188870964686664098408407 := by
  unfold tailWord_827606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886579414983267543559417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20123513759821520464633781 1886579414983267543559417)
  ·
    refine ⟨1414934561237450657669563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1886579414983267543559417 1414934561237450657669563)
    ·
      refine ⟨2122401841856175986504345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414934561237450657669563 2122401841856175986504345)
      ·
        refine ⟨1591801381392131989878259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2122401841856175986504345 1591801381392131989878259)
        ·
          refine ⟨2387702072088197984817389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591801381392131989878259 2387702072088197984817389)
          ·
            refine ⟨895388277033074244306521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2387702072088197984817389 895388277033074244306521)
            ·
              refine ⟨671541207774805683229891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895388277033074244306521 671541207774805683229891)
              ·
                refine ⟨1007311811662208524844837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671541207774805683229891 1007311811662208524844837)
                ·
                  refine ⟨188870964686664098408407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007311811662208524844837 188870964686664098408407)
                  ·
                    rfl

theorem cell21_827606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_827606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827606 prefixEnd_827606 := by exact prefixLift 827606
  have htrace : WordTrace (prefixWord ++ tailWord_827606) baseStart_827606 baseEnd_827606 := by
    simpa [prefixWord, tailWord_827606, baseEnd_827606] using wordTrace_append hprefix tailTrace_827606
  have hstable : (prefixWord ++ tailWord_827606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827606).length < 2 ^ (prefixWord ++ tailWord_827606).sum := by decide
  have hdescent : baseEnd_827606 < baseStart_827606 := by decide
  rcases family_descends (prefixWord ++ tailWord_827606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827628 : List Nat := [2, 2, 1, 1, 2, 3, 1, 9]
def baseStart_827628 : Nat := 118140960795 + 827628 * 2 ^ 59
def prefixEnd_827628 : Nat := 4983230072969 + 3 ^ 40 * 827628 * 2
def baseEnd_827628 : Nat := 62958661795465649680565

theorem tailTrace_827628 : CollatzResearch.WordTrace tailWord_827628 prefixEnd_827628 62958661795465649680565 := by
  unfold tailWord_827628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093036522826289227125769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20124048697101718969501025 15093036522826289227125769)
  ·
    refine ⟨11319777392119716920344327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15093036522826289227125769 11319777392119716920344327)
    ·
      refine ⟨16979666088179575380516491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319777392119716920344327 16979666088179575380516491)
      ·
        refine ⟨25469499132269363070774737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16979666088179575380516491 25469499132269363070774737)
        ·
          refine ⟨19102124349202022303081053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25469499132269363070774737 19102124349202022303081053)
          ·
            refine ⟨7163296630950758363655395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19102124349202022303081053 7163296630950758363655395)
            ·
              refine ⟨10744944946426137545483093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7163296630950758363655395 10744944946426137545483093)
              ·
                refine ⟨62958661795465649680565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10744944946426137545483093 62958661795465649680565)
                ·
                  rfl

theorem cell21_827628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_827628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827628 prefixEnd_827628 := by exact prefixLift 827628
  have htrace : WordTrace (prefixWord ++ tailWord_827628) baseStart_827628 baseEnd_827628 := by
    simpa [prefixWord, tailWord_827628, baseEnd_827628] using wordTrace_append hprefix tailTrace_827628
  have hstable : (prefixWord ++ tailWord_827628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827628).length < 2 ^ (prefixWord ++ tailWord_827628).sum := by decide
  have hdescent : baseEnd_827628 < baseStart_827628 := by decide
  rcases family_descends (prefixWord ++ tailWord_827628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827659 : List Nat := [1, 1, 1, 1, 5, 2, 2, 3, 5]
def baseStart_827659 : Nat := 118140960795 + 827659 * 2 ^ 59
def prefixEnd_827659 : Nat := 4983230072969 + 3 ^ 40 * 827659 * 2
def baseEnd_827659 : Nat := 188883060008747784024965

theorem tailTrace_827659 : CollatzResearch.WordTrace tailWord_827659 prefixEnd_827659 188883060008747784024965 := by
  unfold tailWord_827659
  simp only [CollatzResearch.WordTrace]
  refine ⟨30187203708540270748630031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20124802472360180499086687 30187203708540270748630031)
  ·
    refine ⟨45280805562810406122945047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30187203708540270748630031 45280805562810406122945047)
    ·
      refine ⟨67921208344215609184417571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45280805562810406122945047 67921208344215609184417571)
      ·
        refine ⟨101881812516323413776626357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67921208344215609184417571 101881812516323413776626357)
        ·
          refine ⟨9551419923405320041558721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101881812516323413776626357 9551419923405320041558721)
          ·
            refine ⟨7163564942553990031169041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9551419923405320041558721 7163564942553990031169041)
            ·
              refine ⟨5372673706915492523376781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7163564942553990031169041 5372673706915492523376781)
              ·
                refine ⟨2014752640093309696266293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5372673706915492523376781 2014752640093309696266293)
                ·
                  refine ⟨188883060008747784024965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2014752640093309696266293 188883060008747784024965)
                  ·
                    rfl

theorem cell21_827659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_827659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827659 prefixEnd_827659 := by exact prefixLift 827659
  have htrace : WordTrace (prefixWord ++ tailWord_827659) baseStart_827659 baseEnd_827659 := by
    simpa [prefixWord, tailWord_827659, baseEnd_827659] using wordTrace_append hprefix tailTrace_827659
  have hstable : (prefixWord ++ tailWord_827659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827659).length < 2 ^ (prefixWord ++ tailWord_827659).sum := by decide
  have hdescent : baseEnd_827659 < baseStart_827659 := by decide
  rcases family_descends (prefixWord ++ tailWord_827659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827735 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 5]
def baseStart_827735 : Nat := 118140960795 + 827735 * 2 ^ 59
def prefixEnd_827735 : Nat := 4983230072969 + 3 ^ 40 * 827735 * 2
def baseEnd_827735 : Nat := 188900404244188540758143

theorem tailTrace_827735 : CollatzResearch.WordTrace tailWord_827735 prefixEnd_827735 188900404244188540758143 := by
  unfold tailWord_827735
  simp only [CollatzResearch.WordTrace]
  refine ⟨30189975656264935728396659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20126650437509957152264439 30189975656264935728396659)
  ·
    refine ⟨45284963484397403592594989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30189975656264935728396659 45284963484397403592594989)
    ·
      refine ⟨16981861306649026347223121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45284963484397403592594989 16981861306649026347223121)
      ·
        refine ⟨12736395979986769760417341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16981861306649026347223121 12736395979986769760417341)
        ·
          refine ⟨4776148492495038660156503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12736395979986769760417341 4776148492495038660156503)
          ·
            refine ⟨7164222738742557990234755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776148492495038660156503 7164222738742557990234755)
            ·
              refine ⟨10746334108113836985352133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164222738742557990234755 10746334108113836985352133)
              ·
                refine ⟨2014937645271344434753525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10746334108113836985352133 2014937645271344434753525)
                ·
                  refine ⟨188900404244188540758143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2014937645271344434753525 188900404244188540758143)
                  ·
                    rfl

theorem cell21_827735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_827735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827735 prefixEnd_827735 := by exact prefixLift 827735
  have htrace : WordTrace (prefixWord ++ tailWord_827735) baseStart_827735 baseEnd_827735 := by
    simpa [prefixWord, tailWord_827735, baseEnd_827735] using wordTrace_append hprefix tailTrace_827735
  have hstable : (prefixWord ++ tailWord_827735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827735).length < 2 ^ (prefixWord ++ tailWord_827735).sum := by decide
  have hdescent : baseEnd_827735 < baseStart_827735 := by decide
  rcases family_descends (prefixWord ++ tailWord_827735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827862 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_827862 : Nat := 118140960795 + 827862 * 2 ^ 59
def prefixEnd_827862 : Nat := 4983230072969 + 3 ^ 40 * 827862 * 2
def baseEnd_827862 : Nat := 188929387374464542141217

theorem tailTrace_827862 : CollatzResearch.WordTrace tailWord_827862 prefixEnd_827862 188929387374464542141217 := by
  unfold tailWord_827862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887162982925302276141865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20129738484536557612179893 1887162982925302276141865)
  ·
    refine ⟨1415372237193976707106399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1887162982925302276141865 1415372237193976707106399)
    ·
      refine ⟨2123058355790965060659599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415372237193976707106399 2123058355790965060659599)
      ·
        refine ⟨3184587533686447590989399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123058355790965060659599 3184587533686447590989399)
        ·
          refine ⟨4776881300529671386484099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184587533686447590989399 4776881300529671386484099)
          ·
            refine ⟨7165321950794507079726149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776881300529671386484099 7165321950794507079726149)
            ·
              refine ⟨1343497865773970077448653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7165321950794507079726149 1343497865773970077448653)
              ·
                refine ⟨503811699665238779043245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343497865773970077448653 503811699665238779043245)
                ·
                  refine ⟨188929387374464542141217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503811699665238779043245 188929387374464542141217)
                  ·
                    rfl

theorem cell21_827862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_827862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827862 prefixEnd_827862 := by exact prefixLift 827862
  have htrace : WordTrace (prefixWord ++ tailWord_827862) baseStart_827862 baseEnd_827862 := by
    simpa [prefixWord, tailWord_827862, baseEnd_827862] using wordTrace_append hprefix tailTrace_827862
  have hstable : (prefixWord ++ tailWord_827862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827862).length < 2 ^ (prefixWord ++ tailWord_827862).sum := by decide
  have hdescent : baseEnd_827862 < baseStart_827862 := by decide
  rcases family_descends (prefixWord ++ tailWord_827862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827893 : List Nat := [1, 3, 5, 1, 2, 1, 3, 1, 4]
def baseStart_827893 : Nat := 118140960795 + 827893 * 2 ^ 59
def prefixEnd_827893 : Nat := 4983230072969 + 3 ^ 40 * 827893 * 2
def baseEnd_827893 : Nat := 188936461996815377124487

theorem tailTrace_827893 : CollatzResearch.WordTrace tailWord_827893 prefixEnd_827893 188936461996815377124487 := by
  unfold tailWord_827893
  simp only [CollatzResearch.WordTrace]
  refine ⟨30195738389692528712648333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20130492259795019141765555 30195738389692528712648333)
  ·
    refine ⟨11323401896134698267243125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30195738389692528712648333 11323401896134698267243125)
    ·
      refine ⟨1061568927762627962554043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11323401896134698267243125 1061568927762627962554043)
      ·
        refine ⟨1592353391643941943831065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061568927762627962554043 1592353391643941943831065)
        ·
          refine ⟨1194265043732956457873299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1592353391643941943831065 1194265043732956457873299)
          ·
            refine ⟨1791397565599434686809949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194265043732956457873299 1791397565599434686809949)
            ·
              refine ⟨671774087099788007553731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1791397565599434686809949 671774087099788007553731)
              ·
                refine ⟨1007661130649682011330597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671774087099788007553731 1007661130649682011330597)
                ·
                  refine ⟨188936461996815377124487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1007661130649682011330597 188936461996815377124487)
                  ·
                    rfl

theorem cell21_827893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_827893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827893 prefixEnd_827893 := by exact prefixLift 827893
  have htrace : WordTrace (prefixWord ++ tailWord_827893) baseStart_827893 baseEnd_827893 := by
    simpa [prefixWord, tailWord_827893, baseEnd_827893] using wordTrace_append hprefix tailTrace_827893
  have hstable : (prefixWord ++ tailWord_827893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827893).length < 2 ^ (prefixWord ++ tailWord_827893).sum := by decide
  have hdescent : baseEnd_827893 < baseStart_827893 := by decide
  rcases family_descends (prefixWord ++ tailWord_827893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827918 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 6]
def baseStart_827918 : Nat := 118140960795 + 827918 * 2 ^ 59
def prefixEnd_827918 : Nat := 4983230072969 + 3 ^ 40 * 827918 * 2
def baseEnd_827918 : Nat := 188942167337420889207769

theorem tailTrace_827918 : CollatzResearch.WordTrace tailWord_827918 prefixEnd_827918 188942167337420889207769 := by
  unfold tailWord_827918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774581276825244747788551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20131100143067971988205605 3774581276825244747788551)
  ·
    refine ⟨5661871915237867121682827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774581276825244747788551 5661871915237867121682827)
    ·
      refine ⟨8492807872856800682524241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661871915237867121682827 8492807872856800682524241)
      ·
        refine ⟨6369605904642600511893181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8492807872856800682524241 6369605904642600511893181)
        ·
          refine ⟨2388602214240975191959943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6369605904642600511893181 2388602214240975191959943)
          ·
            refine ⟨3582903321361462787939915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388602214240975191959943 3582903321361462787939915)
            ·
              refine ⟨5374354982042194181909873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582903321361462787939915 5374354982042194181909873)
              ·
                refine ⟨4030766236531645636432405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5374354982042194181909873 4030766236531645636432405)
                ·
                  refine ⟨188942167337420889207769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4030766236531645636432405 188942167337420889207769)
                  ·
                    rfl

theorem cell21_827918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_827918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827918 prefixEnd_827918 := by exact prefixLift 827918
  have htrace : WordTrace (prefixWord ++ tailWord_827918) baseStart_827918 baseEnd_827918 := by
    simpa [prefixWord, tailWord_827918, baseEnd_827918] using wordTrace_append hprefix tailTrace_827918
  have hstable : (prefixWord ++ tailWord_827918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827918).length < 2 ^ (prefixWord ++ tailWord_827918).sum := by decide
  have hdescent : baseEnd_827918 < baseStart_827918 := by decide
  rcases family_descends (prefixWord ++ tailWord_827918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827932 : List Nat := [2, 2, 3, 1, 2, 2, 9]
def baseStart_827932 : Nat := 118140960795 + 827932 * 2 ^ 59
def prefixEnd_827932 : Nat := 4983230072969 + 3 ^ 40 * 827932 * 2
def baseEnd_827932 : Nat := 20993929147573330663823

theorem tailTrace_827932 : CollatzResearch.WordTrace tailWord_827932 prefixEnd_827932 20993929147573330663823 := by
  unfold tailWord_827932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098580418275619186659025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20131440557700825582212033 15098580418275619186659025)
  ·
    refine ⟨11323935313706714389994269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15098580418275619186659025 11323935313706714389994269)
    ·
      refine ⟨4246475742640017896247851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11323935313706714389994269 4246475742640017896247851)
      ·
        refine ⟨6369713613960026844371777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4246475742640017896247851 6369713613960026844371777)
        ·
          refine ⟨4777285210470020133278833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6369713613960026844371777 4777285210470020133278833)
          ·
            refine ⟨3582963907852515099959125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777285210470020133278833 3582963907852515099959125)
            ·
              refine ⟨20993929147573330663823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3582963907852515099959125 20993929147573330663823)
              ·
                rfl

theorem cell21_827932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 9].length) (baseStart_827932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827932 prefixEnd_827932 := by exact prefixLift 827932
  have htrace : WordTrace (prefixWord ++ tailWord_827932) baseStart_827932 baseEnd_827932 := by
    simpa [prefixWord, tailWord_827932, baseEnd_827932] using wordTrace_append hprefix tailTrace_827932
  have hstable : (prefixWord ++ tailWord_827932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827932).length < 2 ^ (prefixWord ++ tailWord_827932).sum := by decide
  have hdescent : baseEnd_827932 < baseStart_827932 := by decide
  rcases family_descends (prefixWord ++ tailWord_827932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827980 : List Nat := [2, 2, 1, 3, 1, 2, 2, 5, 3]
def baseStart_827980 : Nat := 118140960795 + 827980 * 2 ^ 59
def prefixEnd_827980 : Nat := 4983230072969 + 3 ^ 40 * 827980 * 2
def baseEnd_827980 : Nat := 188956316582122559174309

theorem tailTrace_827980 : CollatzResearch.WordTrace tailWord_827980 prefixEnd_827980 188956316582122559174309 := by
  unfold tailWord_827980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099455770188671285532697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20132607693584895047376929 15099455770188671285532697)
  ·
    refine ⟨11324591827641503464149523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15099455770188671285532697 11324591827641503464149523)
    ·
      refine ⟨16986887741462255196224285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11324591827641503464149523 16986887741462255196224285)
      ·
        refine ⟨6370082903048345698584107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16986887741462255196224285 6370082903048345698584107)
        ·
          refine ⟨9555124354572518547876161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370082903048345698584107 9555124354572518547876161)
          ·
            refine ⟨7166343265929388910907121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9555124354572518547876161 7166343265929388910907121)
            ·
              refine ⟨5374757449447041683180341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166343265929388910907121 5374757449447041683180341)
              ·
                refine ⟨503883510885660157798157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5374757449447041683180341 503883510885660157798157)
                ·
                  refine ⟨188956316582122559174309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503883510885660157798157 188956316582122559174309)
                  ·
                    rfl

theorem cell21_827980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_827980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_827980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_827980 prefixEnd_827980 := by exact prefixLift 827980
  have htrace : WordTrace (prefixWord ++ tailWord_827980) baseStart_827980 baseEnd_827980 := by
    simpa [prefixWord, tailWord_827980, baseEnd_827980] using wordTrace_append hprefix tailTrace_827980
  have hstable : (prefixWord ++ tailWord_827980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827980).length < 2 ^ (prefixWord ++ tailWord_827980).sum := by decide
  have hdescent : baseEnd_827980 < baseStart_827980 := by decide
  rcases family_descends (prefixWord ++ tailWord_827980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828025 : List Nat := [1, 2, 1, 3, 3, 3, 3, 5]
def baseStart_828025 : Nat := 118140960795 + 828025 * 2 ^ 59
def prefixEnd_828025 : Nat := 4983230072969 + 3 ^ 40 * 828025 * 2
def baseEnd_828025 : Nat := 62988862065070826974739

theorem tailTrace_828025 : CollatzResearch.WordTrace tailWord_828025 prefixEnd_828025 62988862065070826974739 := by
  unfold tailWord_828025
  simp only [CollatzResearch.WordTrace]
  refine ⟨30200552825214315256453529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20133701883476210170969019 30200552825214315256453529)
  ·
    refine ⟨22650414618910736442340147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30200552825214315256453529 22650414618910736442340147)
    ·
      refine ⟨33975621928366104663510221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22650414618910736442340147 33975621928366104663510221)
      ·
        refine ⟨12740858223137289248816333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33975621928366104663510221 12740858223137289248816333)
        ·
          refine ⟨4777821833676483468306125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12740858223137289248816333 4777821833676483468306125)
          ·
            refine ⟨1791683187628681300614797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4777821833676483468306125 1791683187628681300614797)
            ·
              refine ⟨671881195360755487730549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1791683187628681300614797 671881195360755487730549)
              ·
                refine ⟨62988862065070826974739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 671881195360755487730549 62988862065070826974739)
                ·
                  rfl

theorem cell21_828025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 5].length) (baseStart_828025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828025 prefixEnd_828025 := by exact prefixLift 828025
  have htrace : WordTrace (prefixWord ++ tailWord_828025) baseStart_828025 baseEnd_828025 := by
    simpa [prefixWord, tailWord_828025, baseEnd_828025] using wordTrace_append hprefix tailTrace_828025
  have hstable : (prefixWord ++ tailWord_828025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828025).length < 2 ^ (prefixWord ++ tailWord_828025).sum := by decide
  have hdescent : baseEnd_828025 < baseStart_828025 := by decide
  rcases family_descends (prefixWord ++ tailWord_828025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828056 : List Nat := [2, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_828056 : Nat := 118140960795 + 828056 * 2 ^ 59
def prefixEnd_828056 : Nat := 4983230072969 + 3 ^ 40 * 828056 * 2
def baseEnd_828056 : Nat := 188973660817563315907487

theorem tailTrace_828056 : CollatzResearch.WordTrace tailWord_828056 prefixEnd_828056 188973660817563315907487 := by
  unfold tailWord_828056
  simp only [CollatzResearch.WordTrace]
  refine ⟨15100841744051003775416011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20134455658734671700554681 15100841744051003775416011)
  ·
    refine ⟨22651262616076505663124017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15100841744051003775416011 22651262616076505663124017)
    ·
      refine ⟨16988446962057379247343013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22651262616076505663124017 16988446962057379247343013)
      ·
        refine ⟨3185333805385758608876815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16988446962057379247343013 3185333805385758608876815)
        ·
          refine ⟨4778000708078637913315223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185333805385758608876815 4778000708078637913315223)
          ·
            refine ⟨7167001062117956869972835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4778000708078637913315223 7167001062117956869972835)
            ·
              refine ⟨10750501593176935304959253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7167001062117956869972835 10750501593176935304959253)
              ·
                refine ⟨503929762180168842419965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10750501593176935304959253 503929762180168842419965)
                ·
                  refine ⟨188973660817563315907487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 503929762180168842419965 188973660817563315907487)
                  ·
                    rfl

theorem cell21_828056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_828056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828056 prefixEnd_828056 := by exact prefixLift 828056
  have htrace : WordTrace (prefixWord ++ tailWord_828056) baseStart_828056 baseEnd_828056 := by
    simpa [prefixWord, tailWord_828056, baseEnd_828056] using wordTrace_append hprefix tailTrace_828056
  have hstable : (prefixWord ++ tailWord_828056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828056).length < 2 ^ (prefixWord ++ tailWord_828056).sum := by decide
  have hdescent : baseEnd_828056 < baseStart_828056 := by decide
  rcases family_descends (prefixWord ++ tailWord_828056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828191 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_828191 : Nat := 118140960795 + 828191 * 2 ^ 59
def prefixEnd_828191 : Nat := 4983230072969 + 3 ^ 40 * 828191 * 2
def baseEnd_828191 : Nat := 189004469656833081157211

theorem tailTrace_828191 : CollatzResearch.WordTrace tailWord_828191 prefixEnd_828191 189004469656833081157211 := by
  unfold tailWord_828191
  simp only [CollatzResearch.WordTrace]
  refine ⟨30206607342612925606996427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20137738228408617071330951 30206607342612925606996427)
  ·
    refine ⟨45309911013919388410494641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30206607342612925606996427 45309911013919388410494641)
    ·
      refine ⟨33982433260439541307870981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45309911013919388410494641 33982433260439541307870981)
      ·
        refine ⟨6371706236332413995225809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33982433260439541307870981 6371706236332413995225809)
        ·
          refine ⟨4778779677249310496419357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6371706236332413995225809 4778779677249310496419357)
          ·
            refine ⟨1792042378968491436157259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4778779677249310496419357 1792042378968491436157259)
            ·
              refine ⟨2688063568452737154235889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792042378968491436157259 2688063568452737154235889)
              ·
                refine ⟨2016047676339552865676917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2688063568452737154235889 2016047676339552865676917)
                ·
                  refine ⟨189004469656833081157211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016047676339552865676917 189004469656833081157211)
                  ·
                    rfl

theorem cell21_828191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_828191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828191 prefixEnd_828191 := by exact prefixLift 828191
  have htrace : WordTrace (prefixWord ++ tailWord_828191) baseStart_828191 baseEnd_828191 := by
    simpa [prefixWord, tailWord_828191, baseEnd_828191] using wordTrace_append hprefix tailTrace_828191
  have hstable : (prefixWord ++ tailWord_828191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828191).length < 2 ^ (prefixWord ++ tailWord_828191).sum := by decide
  have hdescent : baseEnd_828191 < baseStart_828191 := by decide
  rcases family_descends (prefixWord ++ tailWord_828191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828225 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 5]
def baseStart_828225 : Nat := 118140960795 + 828225 * 2 ^ 59
def prefixEnd_828225 : Nat := 4983230072969 + 3 ^ 40 * 828225 * 2
def baseEnd_828225 : Nat := 189012228920056577590475

theorem tailTrace_828225 : CollatzResearch.WordTrace tailWord_828225 prefixEnd_828225 189012228920056577590475 := by
  unfold tailWord_828225
  simp only [CollatzResearch.WordTrace]
  refine ⟨30207847424489749413734129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20138564949659832942489419 30207847424489749413734129)
  ·
    refine ⟨22655885568367312060300597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30207847424489749413734129 22655885568367312060300597)
    ·
      refine ⟨2123989272034435505653181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22655885568367312060300597 2123989272034435505653181)
      ·
        refine ⟨796495977012913314619943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2123989272034435505653181 796495977012913314619943)
        ·
          refine ⟨1194743965519369971929915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796495977012913314619943 1194743965519369971929915)
          ·
            refine ⟨1792115948279054957894873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194743965519369971929915 1792115948279054957894873)
            ·
              refine ⟨1344086961209291218421155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792115948279054957894873 1344086961209291218421155)
              ·
                refine ⟨2016130441813936827631733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344086961209291218421155 2016130441813936827631733)
                ·
                  refine ⟨189012228920056577590475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2016130441813936827631733 189012228920056577590475)
                  ·
                    rfl

theorem cell21_828225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_828225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828225 prefixEnd_828225 := by exact prefixLift 828225
  have htrace : WordTrace (prefixWord ++ tailWord_828225) baseStart_828225 baseEnd_828225 := by
    simpa [prefixWord, tailWord_828225, baseEnd_828225] using wordTrace_append hprefix tailTrace_828225
  have hstable : (prefixWord ++ tailWord_828225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828225).length < 2 ^ (prefixWord ++ tailWord_828225).sum := by decide
  have hdescent : baseEnd_828225 < baseStart_828225 := by decide
  rcases family_descends (prefixWord ++ tailWord_828225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828270 : List Nat := [4, 1, 2, 3, 3, 1, 7]
def baseStart_828270 : Nat := 118140960795 + 828270 * 2 ^ 59
def prefixEnd_828270 : Nat := 4983230072969 + 3 ^ 40 * 828270 * 2
def baseEnd_828270 : Nat := 21002499837016277704487

theorem tailTrace_828270 : CollatzResearch.WordTrace tailWord_828270 prefixEnd_828270 21002499837016277704487 := by
  unfold tailWord_828270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776186088665840262390283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20139659139551148066081509 3776186088665840262390283)
  ·
    refine ⟨5664279132998760393585425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3776186088665840262390283 5664279132998760393585425)
    ·
      refine ⟨4248209349749070295189069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5664279132998760393585425 4248209349749070295189069)
      ·
        refine ⟨1593078506155901360695901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4248209349749070295189069 1593078506155901360695901)
        ·
          refine ⟨597404439808463010260963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1593078506155901360695901 597404439808463010260963)
          ·
            refine ⟨896106659712694515391445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597404439808463010260963 896106659712694515391445)
            ·
              refine ⟨21002499837016277704487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 896106659712694515391445 21002499837016277704487)
              ·
                rfl

theorem cell21_828270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 7].length) (baseStart_828270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828270 prefixEnd_828270 := by exact prefixLift 828270
  have htrace : WordTrace (prefixWord ++ tailWord_828270) baseStart_828270 baseEnd_828270 := by
    simpa [prefixWord, tailWord_828270, baseEnd_828270] using wordTrace_append hprefix tailTrace_828270
  have hstable : (prefixWord ++ tailWord_828270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828270).length < 2 ^ (prefixWord ++ tailWord_828270).sum := by decide
  have hdescent : baseEnd_828270 < baseStart_828270 := by decide
  rcases family_descends (prefixWord ++ tailWord_828270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828281 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_828281 : Nat := 118140960795 + 828281 * 2 ^ 59
def prefixEnd_828281 : Nat := 4983230072969 + 3 ^ 40 * 828281 * 2
def baseEnd_828281 : Nat := 189025008883012924657027

theorem tailTrace_828281 : CollatzResearch.WordTrace tailWord_828281 prefixEnd_828281 189025008883012924657027 := by
  unfold tailWord_828281
  simp only [CollatzResearch.WordTrace]
  refine ⟨30209889912286870977772697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20139926608191247318515131 30209889912286870977772697)
  ·
    refine ⟨22657417434215153233329523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30209889912286870977772697 22657417434215153233329523)
    ·
      refine ⟨33986126151322729849994285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22657417434215153233329523 33986126151322729849994285)
      ·
        refine ⟨12744797306746023693747857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33986126151322729849994285 12744797306746023693747857)
        ·
          refine ⟨9558597980059517770310893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12744797306746023693747857 9558597980059517770310893)
          ·
            refine ⟨3584474242522319163866585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9558597980059517770310893 3584474242522319163866585)
            ·
              refine ⟨2688355681891739372899939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584474242522319163866585 2688355681891739372899939)
              ·
                refine ⟨4032533522837609059349909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688355681891739372899939 4032533522837609059349909)
                ·
                  refine ⟨189025008883012924657027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4032533522837609059349909 189025008883012924657027)
                  ·
                    rfl

theorem cell21_828281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_828281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828281 prefixEnd_828281 := by exact prefixLift 828281
  have htrace : WordTrace (prefixWord ++ tailWord_828281) baseStart_828281 baseEnd_828281 := by
    simpa [prefixWord, tailWord_828281, baseEnd_828281] using wordTrace_append hprefix tailTrace_828281
  have hstable : (prefixWord ++ tailWord_828281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828281).length < 2 ^ (prefixWord ++ tailWord_828281).sum := by decide
  have hdescent : baseEnd_828281 < baseStart_828281 := by decide
  rcases family_descends (prefixWord ++ tailWord_828281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828290 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_828290 : Nat := 118140960795 + 828290 * 2 ^ 59
def prefixEnd_828290 : Nat := 4983230072969 + 3 ^ 40 * 828290 * 2
def baseEnd_828290 : Nat := 189027062805630909007009

theorem tailTrace_828290 : CollatzResearch.WordTrace tailWord_828290 prefixEnd_828290 189027062805630909007009 := by
  unfold tailWord_828290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7552554542313566378712581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20140145446169510343233549 7552554542313566378712581)
  ·
    refine ⟨1416103976683793696008609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7552554542313566378712581 1416103976683793696008609)
    ·
      refine ⟨1062077982512845272006457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1416103976683793696008609 1062077982512845272006457)
      ·
        refine ⟨796558486884633954004843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1062077982512845272006457 796558486884633954004843)
        ·
          refine ⟨1194837730326950931007265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796558486884633954004843 1194837730326950931007265)
          ·
            refine ⟨896128297745213198255449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194837730326950931007265 896128297745213198255449)
            ·
              refine ⟨672096223308909898691587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896128297745213198255449 672096223308909898691587)
              ·
                refine ⟨1008144334963364848037381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672096223308909898691587 1008144334963364848037381)
                ·
                  refine ⟨189027062805630909007009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008144334963364848037381 189027062805630909007009)
                  ·
                    rfl

theorem cell21_828290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_828290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828290 prefixEnd_828290 := by exact prefixLift 828290
  have htrace : WordTrace (prefixWord ++ tailWord_828290) baseStart_828290 baseEnd_828290 := by
    simpa [prefixWord, tailWord_828290, baseEnd_828290] using wordTrace_append hprefix tailTrace_828290
  have hstable : (prefixWord ++ tailWord_828290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828290).length < 2 ^ (prefixWord ++ tailWord_828290).sum := by decide
  have hdescent : baseEnd_828290 < baseStart_828290 := by decide
  rcases family_descends (prefixWord ++ tailWord_828290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828391 : List Nat := [1, 1, 5, 2, 2, 3, 1, 2, 4]
def baseStart_828391 : Nat := 118140960795 + 828391 * 2 ^ 59
def prefixEnd_828391 : Nat := 4983230072969 + 3 ^ 40 * 828391 * 2
def baseEnd_828391 : Nat := 189050112381677177823469

theorem tailTrace_828391 : CollatzResearch.WordTrace tailWord_828391 prefixEnd_828391 189050112381677177823469 := by
  unfold tailWord_828391
  simp only [CollatzResearch.WordTrace]
  refine ⟨30213901941888359764277027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20142601294592239842851351 30213901941888359764277027)
  ·
    refine ⟨45320852912832539646415541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30213901941888359764277027 45320852912832539646415541)
    ·
      refine ⟨4248829960578050591851457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45320852912832539646415541 4248829960578050591851457)
      ·
        refine ⟨3186622470433537943888593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248829960578050591851457 3186622470433537943888593)
        ·
          refine ⟨2389966852825153457916445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3186622470433537943888593 2389966852825153457916445)
          ·
            refine ⟨896237569809432546718667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2389966852825153457916445 896237569809432546718667)
            ·
              refine ⟨1344356354714148820078001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896237569809432546718667 1344356354714148820078001)
              ·
                refine ⟨1008267266035611615058501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1344356354714148820078001 1008267266035611615058501)
                ·
                  refine ⟨189050112381677177823469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008267266035611615058501 189050112381677177823469)
                  ·
                    rfl

theorem cell21_828391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 2, 4].length) (baseStart_828391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828391 prefixEnd_828391 := by exact prefixLift 828391
  have htrace : WordTrace (prefixWord ++ tailWord_828391) baseStart_828391 baseEnd_828391 := by
    simpa [prefixWord, tailWord_828391, baseEnd_828391] using wordTrace_append hprefix tailTrace_828391
  have hstable : (prefixWord ++ tailWord_828391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828391).length < 2 ^ (prefixWord ++ tailWord_828391).sum := by decide
  have hdescent : baseEnd_828391 < baseStart_828391 := by decide
  rcases family_descends (prefixWord ++ tailWord_828391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828447 : List Nat := [1, 1, 2, 4, 1, 3, 9]
def baseStart_828447 : Nat := 118140960795 + 828447 * 2 ^ 59
def prefixEnd_828447 : Nat := 4983230072969 + 3 ^ 40 * 828447 * 2
def baseEnd_828447 : Nat := 21006988038292613876669

theorem tailTrace_828447 : CollatzResearch.WordTrace tailWord_828447 prefixEnd_828447 21006988038292613876669 := by
  unfold tailWord_828447
  simp only [CollatzResearch.WordTrace]
  refine ⟨30215944429685481328315595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20143962953123654218877063 30215944429685481328315595)
  ·
    refine ⟨45323916644528221992473393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30215944429685481328315595 45323916644528221992473393)
    ·
      refine ⟨33992937483396166494355045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45323916644528221992473393 33992937483396166494355045)
      ·
        refine ⟨6373675778136781217691571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33992937483396166494355045 6373675778136781217691571)
        ·
          refine ⟨9560513667205171826537357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373675778136781217691571 9560513667205171826537357)
          ·
            refine ⟨3585192625201939434951509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9560513667205171826537357 3585192625201939434951509)
            ·
              refine ⟨21006988038292613876669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3585192625201939434951509 21006988038292613876669)
              ·
                rfl

theorem cell21_828447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 9].length) (baseStart_828447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828447 prefixEnd_828447 := by exact prefixLift 828447
  have htrace : WordTrace (prefixWord ++ tailWord_828447) baseStart_828447 baseEnd_828447 := by
    simpa [prefixWord, tailWord_828447, baseEnd_828447] using wordTrace_append hprefix tailTrace_828447
  have hstable : (prefixWord ++ tailWord_828447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828447).length < 2 ^ (prefixWord ++ tailWord_828447).sum := by decide
  have hdescent : baseEnd_828447 < baseStart_828447 := by decide
  rcases family_descends (prefixWord ++ tailWord_828447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828526 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_828526 : Nat := 118140960795 + 828526 * 2 ^ 59
def prefixEnd_828526 : Nat := 4983230072969 + 3 ^ 40 * 828526 * 2
def baseEnd_828526 : Nat := 189080921220946943073193

theorem tailTrace_828526 : CollatzResearch.WordTrace tailWord_828526 prefixEnd_828526 189080921220946943073193 := by
  unfold tailWord_828526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3777353224549909727555179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20145883864266185213627621 3777353224549909727555179)
  ·
    refine ⟨5666029836824864591332769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3777353224549909727555179 5666029836824864591332769)
    ·
      refine ⟨4249522377618648443499577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5666029836824864591332769 4249522377618648443499577)
      ·
        refine ⟨3187141783213986332624683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4249522377618648443499577 3187141783213986332624683)
        ·
          refine ⟨4780712674820979498937025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187141783213986332624683 4780712674820979498937025)
          ·
            refine ⟨3585534506115734624202769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780712674820979498937025 3585534506115734624202769)
            ·
              refine ⟨2689150879586800968152077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3585534506115734624202769 2689150879586800968152077)
              ·
                refine ⟨1008431579845050363057029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2689150879586800968152077 1008431579845050363057029)
                ·
                  refine ⟨189080921220946943073193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1008431579845050363057029 189080921220946943073193)
                  ·
                    rfl

theorem cell21_828526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_828526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828526 prefixEnd_828526 := by exact prefixLift 828526
  have htrace : WordTrace (prefixWord ++ tailWord_828526) baseStart_828526 baseEnd_828526 := by
    simpa [prefixWord, tailWord_828526, baseEnd_828526] using wordTrace_append hprefix tailTrace_828526
  have hstable : (prefixWord ++ tailWord_828526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828526).length < 2 ^ (prefixWord ++ tailWord_828526).sum := by decide
  have hdescent : baseEnd_828526 < baseStart_828526 := by decide
  rcases family_descends (prefixWord ++ tailWord_828526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828540 : List Nat := [2, 2, 2, 1, 1, 3, 5, 5]
def baseStart_828540 : Nat := 118140960795 + 828540 * 2 ^ 59
def prefixEnd_828540 : Nat := 4983230072969 + 3 ^ 40 * 828540 * 2
def baseEnd_828540 : Nat := 63028038737228676613277

theorem tailTrace_828540 : CollatzResearch.WordTrace tailWord_828540 prefixEnd_828540 63028038737228676613277 := by
  unfold tailWord_828540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15109668209174279105725537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20146224278899038807634049 15109668209174279105725537)
  ·
    refine ⟨11332251156880709329294153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15109668209174279105725537 11332251156880709329294153)
    ·
      refine ⟨8499188367660531996970615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11332251156880709329294153 8499188367660531996970615)
      ·
        refine ⟨12748782551490797995455923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499188367660531996970615 12748782551490797995455923)
        ·
          refine ⟨19123173827236196993183885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12748782551490797995455923 19123173827236196993183885)
          ·
            refine ⟨7171190185213573872443957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19123173827236196993183885 7171190185213573872443957)
            ·
              refine ⟨672299079863772550541621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7171190185213573872443957 672299079863772550541621)
              ·
                refine ⟨63028038737228676613277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672299079863772550541621 63028038737228676613277)
                ·
                  rfl

theorem cell21_828540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_828540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828540 prefixEnd_828540 := by exact prefixLift 828540
  have htrace : WordTrace (prefixWord ++ tailWord_828540) baseStart_828540 baseEnd_828540 := by
    simpa [prefixWord, tailWord_828540, baseEnd_828540] using wordTrace_append hprefix tailTrace_828540
  have hstable : (prefixWord ++ tailWord_828540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828540).length < 2 ^ (prefixWord ++ tailWord_828540).sum := by decide
  have hdescent : baseEnd_828540 < baseStart_828540 := by decide
  rcases family_descends (prefixWord ++ tailWord_828540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828554 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 7]
def baseStart_828554 : Nat := 118140960795 + 828554 * 2 ^ 59
def prefixEnd_828554 : Nat := 4983230072969 + 3 ^ 40 * 828554 * 2
def baseEnd_828554 : Nat := 189087311202425116606469

theorem tailTrace_828554 : CollatzResearch.WordTrace tailWord_828554 prefixEnd_828554 189087311202425116606469 := by
  unfold tailWord_828554
  simp only [CollatzResearch.WordTrace]
  refine ⟨7554961760074459650615179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20146564693531892401640477 7554961760074459650615179)
  ·
    refine ⟨11332442640111689475922769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7554961760074459650615179 11332442640111689475922769)
    ·
      refine ⟨8499331980083767106942077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11332442640111689475922769 8499331980083767106942077)
      ·
        refine ⟨3187249492531412665103279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8499331980083767106942077 3187249492531412665103279)
        ·
          refine ⟨4780874238797118997654919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187249492531412665103279 4780874238797118997654919)
          ·
            refine ⟨7171311358195678496482379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4780874238797118997654919 7171311358195678496482379)
            ·
              refine ⟨10756967037293517744723569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7171311358195678496482379 10756967037293517744723569)
              ·
                refine ⟨8067725277970138308542677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10756967037293517744723569 8067725277970138308542677)
                ·
                  refine ⟨189087311202425116606469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8067725277970138308542677 189087311202425116606469)
                  ·
                    rfl

theorem cell21_828554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_828554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828554 prefixEnd_828554 := by exact prefixLift 828554
  have htrace : WordTrace (prefixWord ++ tailWord_828554) baseStart_828554 baseEnd_828554 := by
    simpa [prefixWord, tailWord_828554, baseEnd_828554] using wordTrace_append hprefix tailTrace_828554
  have hstable : (prefixWord ++ tailWord_828554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828554).length < 2 ^ (prefixWord ++ tailWord_828554).sum := by decide
  have hdescent : baseEnd_828554 < baseStart_828554 := by decide
  rcases family_descends (prefixWord ++ tailWord_828554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828599 : List Nat := [1, 1, 3, 1, 4, 1, 3, 7]
def baseStart_828599 : Nat := 118140960795 + 828599 * 2 ^ 59
def prefixEnd_828599 : Nat := 4983230072969 + 3 ^ 40 * 828599 * 2
def baseEnd_828599 : Nat := 63032526938505012785459

theorem tailTrace_828599 : CollatzResearch.WordTrace tailWord_828599 prefixEnd_828599 63032526938505012785459 := by
  unfold tailWord_828599
  simp only [CollatzResearch.WordTrace]
  refine ⟨30221488325134811287848851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20147658883423207525232567 30221488325134811287848851)
  ·
    refine ⟨45332232487702216931773277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30221488325134811287848851 45332232487702216931773277)
    ·
      refine ⟨16999587182888331349414979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45332232487702216931773277 16999587182888331349414979)
      ·
        refine ⟨25499380774332497024122469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16999587182888331349414979 25499380774332497024122469)
        ·
          refine ⟨4781133895187343192022963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25499380774332497024122469 4781133895187343192022963)
          ·
            refine ⟨7171700842781014788034445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781133895187343192022963 7171700842781014788034445)
            ·
              refine ⟨2689387816042880545512917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7171700842781014788034445 2689387816042880545512917)
              ·
                refine ⟨63032526938505012785459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2689387816042880545512917 63032526938505012785459)
                ·
                  rfl

theorem cell21_828599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 7].length) (baseStart_828599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828599 prefixEnd_828599 := by exact prefixLift 828599
  have htrace : WordTrace (prefixWord ++ tailWord_828599) baseStart_828599 baseEnd_828599 := by
    simpa [prefixWord, tailWord_828599, baseEnd_828599] using wordTrace_append hprefix tailTrace_828599
  have hstable : (prefixWord ++ tailWord_828599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828599).length < 2 ^ (prefixWord ++ tailWord_828599).sum := by decide
  have hdescent : baseEnd_828599 < baseStart_828599 := by decide
  rcases family_descends (prefixWord ++ tailWord_828599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828720 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_828720 : Nat := 118140960795 + 828720 * 2 ^ 59
def prefixEnd_828720 : Nat := 4983230072969 + 3 ^ 40 * 828720 * 2
def baseEnd_828720 : Nat := 189125194664045716839463

theorem tailTrace_828720 : CollatzResearch.WordTrace tailWord_828720 prefixEnd_828720 189125194664045716839463 := by
  unfold tailWord_828720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15112950778848224476501807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20150601038464299302002409 15112950778848224476501807)
  ·
    refine ⟨22669426168272336714752711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15112950778848224476501807 22669426168272336714752711)
    ·
      refine ⟨34004139252408505072129067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22669426168272336714752711 34004139252408505072129067)
      ·
        refine ⟨51006208878612757608193601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34004139252408505072129067 51006208878612757608193601)
        ·
          refine ⟨38254656658959568206145201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51006208878612757608193601 38254656658959568206145201)
          ·
            refine ⟨28690992494219676154608901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38254656658959568206145201 28690992494219676154608901)
            ·
              refine ⟨5379561092666189278989169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28690992494219676154608901 5379561092666189278989169)
              ·
                refine ⟨4034670819499641959241877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5379561092666189278989169 4034670819499641959241877)
                ·
                  refine ⟨189125194664045716839463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4034670819499641959241877 189125194664045716839463)
                  ·
                    rfl

theorem cell21_828720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_828720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828720 prefixEnd_828720 := by exact prefixLift 828720
  have htrace : WordTrace (prefixWord ++ tailWord_828720) baseStart_828720 baseEnd_828720 := by
    simpa [prefixWord, tailWord_828720, baseEnd_828720] using wordTrace_append hprefix tailTrace_828720
  have hstable : (prefixWord ++ tailWord_828720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828720).length < 2 ^ (prefixWord ++ tailWord_828720).sum := by decide
  have hdescent : baseEnd_828720 < baseStart_828720 := by decide
  rcases family_descends (prefixWord ++ tailWord_828720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828723 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 3]
def baseStart_828723 : Nat := 118140960795 + 828723 * 2 ^ 59
def prefixEnd_828723 : Nat := 4983230072969 + 3 ^ 40 * 828723 * 2
def baseEnd_828723 : Nat := 189125879304918378289457

theorem tailTrace_828723 : CollatzResearch.WordTrace tailWord_828723 prefixEnd_828723 189125879304918378289457 := by
  unfold tailWord_828723
  simp only [CollatzResearch.WordTrace]
  refine ⟨30226010976685580465362823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20150673984457053643575215 30226010976685580465362823)
  ·
    refine ⟨45339016465028370698044235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30226010976685580465362823 45339016465028370698044235)
    ·
      refine ⟨68008524697542556047066353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45339016465028370698044235 68008524697542556047066353)
      ·
        refine ⟨51006393523156917035299765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68008524697542556047066353 51006393523156917035299765)
        ·
          refine ⟨4781849392795960972059353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51006393523156917035299765 4781849392795960972059353)
          ·
            refine ⟨3586387044596970729044515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4781849392795960972059353 3586387044596970729044515)
            ·
              refine ⟨5379580566895456093566773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3586387044596970729044515 5379580566895456093566773)
              ·
                refine ⟨504335678146449008771885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5379580566895456093566773 504335678146449008771885)
                ·
                  refine ⟨189125879304918378289457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504335678146449008771885 189125879304918378289457)
                  ·
                    rfl

theorem cell21_828723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3].length) (baseStart_828723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828723 prefixEnd_828723 := by exact prefixLift 828723
  have htrace : WordTrace (prefixWord ++ tailWord_828723) baseStart_828723 baseEnd_828723 := by
    simpa [prefixWord, tailWord_828723, baseEnd_828723] using wordTrace_append hprefix tailTrace_828723
  have hstable : (prefixWord ++ tailWord_828723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828723).length < 2 ^ (prefixWord ++ tailWord_828723).sum := by decide
  have hdescent : baseEnd_828723 < baseStart_828723 := by decide
  rcases family_descends (prefixWord ++ tailWord_828723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828740 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_828740 : Nat := 118140960795 + 828740 * 2 ^ 59
def prefixEnd_828740 : Nat := 4983230072969 + 3 ^ 40 * 828740 * 2
def baseEnd_828740 : Nat := 189129758936530126506089

theorem tailTrace_828740 : CollatzResearch.WordTrace tailWord_828740 prefixEnd_828740 189129758936530126506089 := by
  unfold tailWord_828740
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113315508811996184365837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20151087345082661579154449 15113315508811996184365837)
  ·
    refine ⟨5667493315804498569137189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15113315508811996184365837 5667493315804498569137189)
    ·
      refine ⟨1062654996713343481713223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5667493315804498569137189 1062654996713343481713223)
      ·
        refine ⟨1593982495070015222569835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062654996713343481713223 1593982495070015222569835)
        ·
          refine ⟨2390973742605022833854753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1593982495070015222569835 2390973742605022833854753)
          ·
            refine ⟨1793230306953767125391065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2390973742605022833854753 1793230306953767125391065)
            ·
              refine ⟨1344922730215325344043299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793230306953767125391065 1344922730215325344043299)
              ·
                refine ⟨2017384095322988016064949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1344922730215325344043299 2017384095322988016064949)
                ·
                  refine ⟨189129758936530126506089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017384095322988016064949 189129758936530126506089)
                  ·
                    rfl

theorem cell21_828740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_828740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828740 prefixEnd_828740 := by exact prefixLift 828740
  have htrace : WordTrace (prefixWord ++ tailWord_828740) baseStart_828740 baseEnd_828740 := by
    simpa [prefixWord, tailWord_828740, baseEnd_828740] using wordTrace_append hprefix tailTrace_828740
  have hstable : (prefixWord ++ tailWord_828740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828740).length < 2 ^ (prefixWord ++ tailWord_828740).sum := by decide
  have hdescent : baseEnd_828740 < baseStart_828740 := by decide
  rcases family_descends (prefixWord ++ tailWord_828740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828768 : List Nat := [2, 1, 1, 3, 4, 1, 4, 5]
def baseStart_828768 : Nat := 118140960795 + 828768 * 2 ^ 59
def prefixEnd_828768 : Nat := 4983230072969 + 3 ^ 40 * 828768 * 2
def baseEnd_828768 : Nat := 63045382972669433346455

theorem tailTrace_828768 : CollatzResearch.WordTrace tailWord_828768 prefixEnd_828768 63045382972669433346455 := by
  unfold tailWord_828768
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113826130761276575375479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20151768174348368767167305 15113826130761276575375479)
  ·
    refine ⟨22670739196141914863063219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15113826130761276575375479 22670739196141914863063219)
    ·
      refine ⟨34006108794212872294594829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22670739196141914863063219 34006108794212872294594829)
      ·
        refine ⟨12752290797829827110473061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34006108794212872294594829 12752290797829827110473061)
        ·
          refine ⟨2391054524593092583213699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12752290797829827110473061 2391054524593092583213699)
          ·
            refine ⟨3586581786889638874820549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391054524593092583213699 3586581786889638874820549)
            ·
              refine ⟨672484085041807289028853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3586581786889638874820549 672484085041807289028853)
              ·
                refine ⟨63045382972669433346455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672484085041807289028853 63045382972669433346455)
                ·
                  rfl

theorem cell21_828768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_828768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828768 prefixEnd_828768 := by exact prefixLift 828768
  have htrace : WordTrace (prefixWord ++ tailWord_828768) baseStart_828768 baseEnd_828768 := by
    simpa [prefixWord, tailWord_828768, baseEnd_828768] using wordTrace_append hprefix tailTrace_828768
  have hstable : (prefixWord ++ tailWord_828768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828768).length < 2 ^ (prefixWord ++ tailWord_828768).sum := by decide
  have hdescent : baseEnd_828768 < baseStart_828768 := by decide
  rcases family_descends (prefixWord ++ tailWord_828768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828796 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 6]
def baseStart_828796 : Nat := 118140960795 + 828796 * 2 ^ 59
def prefixEnd_828796 : Nat := 4983230072969 + 3 ^ 40 * 828796 * 2
def baseEnd_828796 : Nat := 189142538899486473572641

theorem tailTrace_828796 : CollatzResearch.WordTrace tailWord_828796 prefixEnd_828796 189142538899486473572641 := by
  unfold tailWord_828796
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114336752710556966385121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20152449003614075955180161 15114336752710556966385121)
  ·
    refine ⟨11335752564532917724788841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15114336752710556966385121 11335752564532917724788841)
    ·
      refine ⟨8501814423399688293591631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11335752564532917724788841 8501814423399688293591631)
      ·
        refine ⟨12752721635099532440387447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501814423399688293591631 12752721635099532440387447)
        ·
          refine ⟨19129082452649298660581171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12752721635099532440387447 19129082452649298660581171)
          ·
            refine ⟨28693623678973947990871757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19129082452649298660581171 28693623678973947990871757)
            ·
              refine ⟨10760108879615230496576909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28693623678973947990871757 10760108879615230496576909)
              ·
                refine ⟨4035040829855711436216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10760108879615230496576909 4035040829855711436216341)
                ·
                  refine ⟨189142538899486473572641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4035040829855711436216341 189142538899486473572641)
                  ·
                    rfl

theorem cell21_828796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_828796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828796 prefixEnd_828796 := by exact prefixLift 828796
  have htrace : WordTrace (prefixWord ++ tailWord_828796) baseStart_828796 baseEnd_828796 := by
    simpa [prefixWord, tailWord_828796, baseEnd_828796] using wordTrace_append hprefix tailTrace_828796
  have hstable : (prefixWord ++ tailWord_828796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828796).length < 2 ^ (prefixWord ++ tailWord_828796).sum := by decide
  have hdescent : baseEnd_828796 < baseStart_828796 := by decide
  rcases family_descends (prefixWord ++ tailWord_828796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828903 : List Nat := [1, 1, 5, 2, 1, 3, 8]
def baseStart_828903 : Nat := 118140960795 + 828903 * 2 ^ 59
def prefixEnd_828903 : Nat := 4983230072969 + 3 ^ 40 * 828903 * 2
def baseEnd_828903 : Nat := 21018550861919785032121

theorem tailTrace_828903 : CollatzResearch.WordTrace tailWord_828903 prefixEnd_828903 21018550861919785032121 := by
  unfold tailWord_828903
  simp only [CollatzResearch.WordTrace]
  refine ⟨30232576116033471206915363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20155050744022314137943575 30232576116033471206915363)
  ·
    refine ⟨45348864174050206810373045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30232576116033471206915363 45348864174050206810373045)
    ·
      refine ⟨4251456016317206888472473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45348864174050206810373045 4251456016317206888472473)
      ·
        refine ⟨3188592012237905166354355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4251456016317206888472473 3188592012237905166354355)
        ·
          refine ⟨4782888018356857749531533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3188592012237905166354355 4782888018356857749531533)
          ·
            refine ⟨1793583006883821656074325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4782888018356857749531533 1793583006883821656074325)
            ·
              refine ⟨21018550861919785032121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1793583006883821656074325 21018550861919785032121)
              ·
                rfl

theorem cell21_828903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 8].length) (baseStart_828903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828903 prefixEnd_828903 := by exact prefixLift 828903
  have htrace : WordTrace (prefixWord ++ tailWord_828903) baseStart_828903 baseEnd_828903 := by
    simpa [prefixWord, tailWord_828903, baseEnd_828903] using wordTrace_append hprefix tailTrace_828903
  have hstable : (prefixWord ++ tailWord_828903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828903).length < 2 ^ (prefixWord ++ tailWord_828903).sum := by decide
  have hdescent : baseEnd_828903 < baseStart_828903 := by decide
  rcases family_descends (prefixWord ++ tailWord_828903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828968 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 5]
def baseStart_828968 : Nat := 118140960795 + 828968 * 2 ^ 59
def prefixEnd_828968 : Nat := 4983230072969 + 3 ^ 40 * 828968 * 2
def baseEnd_828968 : Nat := 189181791642852396705623

theorem tailTrace_828968 : CollatzResearch.WordTrace tailWord_828968 prefixEnd_828968 189181791642852396705623 := by
  unfold tailWord_828968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15117473430398993654015779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20156631240531991538687705 15117473430398993654015779)
  ·
    refine ⟨22676210145598490481023669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15117473430398993654015779 22676210145598490481023669)
    ·
      refine ⟨2125894701149858482595969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22676210145598490481023669 2125894701149858482595969)
      ·
        refine ⟨1594421025862393861946977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2125894701149858482595969 1594421025862393861946977)
        ·
          refine ⟨1195815769396795396460233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1594421025862393861946977 1195815769396795396460233)
          ·
            refine ⟨896861827047596547345175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1195815769396795396460233 896861827047596547345175)
            ·
              refine ⟨1345292740571394821017763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 896861827047596547345175 1345292740571394821017763)
              ·
                refine ⟨2017939110857092231526645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345292740571394821017763 2017939110857092231526645)
                ·
                  refine ⟨189181791642852396705623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2017939110857092231526645 189181791642852396705623)
                  ·
                    rfl

theorem cell21_828968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_828968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828968 prefixEnd_828968 := by exact prefixLift 828968
  have htrace : WordTrace (prefixWord ++ tailWord_828968) baseStart_828968 baseEnd_828968 := by
    simpa [prefixWord, tailWord_828968, baseEnd_828968] using wordTrace_append hprefix tailTrace_828968
  have hstable : (prefixWord ++ tailWord_828968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828968).length < 2 ^ (prefixWord ++ tailWord_828968).sum := by decide
  have hdescent : baseEnd_828968 < baseStart_828968 := by decide
  rcases family_descends (prefixWord ++ tailWord_828968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828979 : List Nat := [1, 1, 1, 2, 4, 4, 2, 6]
def baseStart_828979 : Nat := 118140960795 + 828979 * 2 ^ 59
def prefixEnd_828979 : Nat := 4983230072969 + 3 ^ 40 * 828979 * 2
def baseEnd_828979 : Nat := 63061433997572940674089

theorem tailTrace_828979 : CollatzResearch.WordTrace tailWord_828979 prefixEnd_828979 63061433997572940674089 := by
  unfold tailWord_828979
  simp only [CollatzResearch.WordTrace]
  refine ⟨30235348063758136186681991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20156898709172090791121327 30235348063758136186681991)
  ·
    refine ⟨45353022095637204280022987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30235348063758136186681991 45353022095637204280022987)
    ·
      refine ⟨68029533143455806420034481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45353022095637204280022987 68029533143455806420034481)
      ·
        refine ⟨51022149857591854815025861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68029533143455806420034481 51022149857591854815025861)
        ·
          refine ⟨9566653098298472777817349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51022149857591854815025861 9566653098298472777817349)
          ·
            refine ⟨1793747455930963645840753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9566653098298472777817349 1793747455930963645840753)
            ·
              refine ⟨1345310591948222734380565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793747455930963645840753 1345310591948222734380565)
              ·
                refine ⟨63061433997572940674089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1345310591948222734380565 63061433997572940674089)
                ·
                  rfl

theorem cell21_828979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 6].length) (baseStart_828979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_828979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_828979 prefixEnd_828979 := by exact prefixLift 828979
  have htrace : WordTrace (prefixWord ++ tailWord_828979) baseStart_828979 baseEnd_828979 := by
    simpa [prefixWord, tailWord_828979, baseEnd_828979] using wordTrace_append hprefix tailTrace_828979
  have hstable : (prefixWord ++ tailWord_828979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828979).length < 2 ^ (prefixWord ++ tailWord_828979).sum := by decide
  have hdescent : baseEnd_828979 < baseStart_828979 := by decide
  rcases family_descends (prefixWord ++ tailWord_828979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829027 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 3]
def baseStart_829027 : Nat := 118140960795 + 829027 * 2 ^ 59
def prefixEnd_829027 : Nat := 4983230072969 + 3 ^ 40 * 829027 * 2
def baseEnd_829027 : Nat := 189195256246681405222169

theorem tailTrace_829027 : CollatzResearch.WordTrace tailWord_829027 prefixEnd_829027 189195256246681405222169 := by
  unfold tailWord_829027
  simp only [CollatzResearch.WordTrace]
  refine ⟨30237098767584240384429335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20158065845056160256286223 30237098767584240384429335)
  ·
    refine ⟨45355648151376360576644003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30237098767584240384429335 45355648151376360576644003)
    ·
      refine ⟨68033472227064540864966005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45355648151376360576644003 68033472227064540864966005)
      ·
        refine ⟨6378138021287300706090563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68033472227064540864966005 6378138021287300706090563)
        ·
          refine ⟨9567207031930951059135845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378138021287300706090563 9567207031930951059135845)
          ·
            refine ⟨1793851318487053323587971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9567207031930951059135845 1793851318487053323587971)
            ·
              refine ⟨2690776977730579985381957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793851318487053323587971 2690776977730579985381957)
              ·
                refine ⟨504520683324483747259117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2690776977730579985381957 504520683324483747259117)
                ·
                  refine ⟨189195256246681405222169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504520683324483747259117 189195256246681405222169)
                  ·
                    rfl

theorem cell21_829027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 3].length) (baseStart_829027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829027 prefixEnd_829027 := by exact prefixLift 829027
  have htrace : WordTrace (prefixWord ++ tailWord_829027) baseStart_829027 baseEnd_829027 := by
    simpa [prefixWord, tailWord_829027, baseEnd_829027] using wordTrace_append hprefix tailTrace_829027
  have hstable : (prefixWord ++ tailWord_829027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829027).length < 2 ^ (prefixWord ++ tailWord_829027).sum := by decide
  have hdescent : baseEnd_829027 < baseStart_829027 := by decide
  rcases family_descends (prefixWord ++ tailWord_829027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829207 : List Nat := [1, 1, 3, 4, 2, 1, 3, 6]
def baseStart_829207 : Nat := 118140960795 + 829207 * 2 ^ 59
def prefixEnd_829207 : Nat := 4983230072969 + 3 ^ 40 * 829207 * 2
def baseEnd_829207 : Nat := 63078778233013697407267

theorem tailTrace_829207 : CollatzResearch.WordTrace tailWord_829207 prefixEnd_829207 63078778233013697407267 := by
  unfold tailWord_829207
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243663906932131125981875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20162442604621420750654583 30243663906932131125981875)
  ·
    refine ⟨45365495860398196688972813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30243663906932131125981875 45365495860398196688972813)
    ·
      refine ⟨17012060947649323758364805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45365495860398196688972813 17012060947649323758364805)
      ·
        refine ⟨3189761427684248204693401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17012060947649323758364805 3189761427684248204693401)
        ·
          refine ⟨2392321070763186153520051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189761427684248204693401 2392321070763186153520051)
          ·
            refine ⟨3588481606144779230280077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392321070763186153520051 3588481606144779230280077)
            ·
              refine ⟨1345680602304292211355029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3588481606144779230280077 1345680602304292211355029)
              ·
                refine ⟨63078778233013697407267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1345680602304292211355029 63078778233013697407267)
                ·
                  rfl

theorem cell21_829207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 6].length) (baseStart_829207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829207 prefixEnd_829207 := by exact prefixLift 829207
  have htrace : WordTrace (prefixWord ++ tailWord_829207) baseStart_829207 baseEnd_829207 := by
    simpa [prefixWord, tailWord_829207, baseEnd_829207] using wordTrace_append hprefix tailTrace_829207
  have hstable : (prefixWord ++ tailWord_829207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829207).length < 2 ^ (prefixWord ++ tailWord_829207).sum := by decide
  have hdescent : baseEnd_829207 < baseStart_829207 := by decide
  rcases family_descends (prefixWord ++ tailWord_829207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829221 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_829221 : Nat := 118140960795 + 829221 * 2 ^ 59
def prefixEnd_829221 : Nat := 4983230072969 + 3 ^ 40 * 829221 * 2
def baseEnd_829221 : Nat := 189239529689780178988439

theorem tailTrace_829221 : CollatzResearch.WordTrace tailWord_829221 prefixEnd_829221 189239529689780178988439 := by
  unfold tailWord_829221
  simp only [CollatzResearch.WordTrace]
  refine ⟨30244174528881411516991517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20162783019254274344661011 30244174528881411516991517)
  ·
    refine ⟨11341565448330529318871819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30244174528881411516991517 11341565448330529318871819)
    ·
      refine ⟨17012348172495793978307729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11341565448330529318871819 17012348172495793978307729)
      ·
        refine ⟨12759261129371845483730797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17012348172495793978307729 12759261129371845483730797)
        ·
          refine ⟨4784722923514442056399049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12759261129371845483730797 4784722923514442056399049)
          ·
            refine ⟨3588542192635831542299287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4784722923514442056399049 3588542192635831542299287)
            ·
              refine ⟨5382813288953747313448931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588542192635831542299287 5382813288953747313448931)
              ·
                refine ⟨8074219933430620970173397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382813288953747313448931 8074219933430620970173397)
                ·
                  refine ⟨189239529689780178988439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8074219933430620970173397 189239529689780178988439)
                  ·
                    rfl

theorem cell21_829221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_829221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829221 prefixEnd_829221 := by exact prefixLift 829221
  have htrace : WordTrace (prefixWord ++ tailWord_829221) baseStart_829221 baseEnd_829221 := by
    simpa [prefixWord, tailWord_829221, baseEnd_829221] using wordTrace_append hprefix tailTrace_829221
  have hstable : (prefixWord ++ tailWord_829221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829221).length < 2 ^ (prefixWord ++ tailWord_829221).sum := by decide
  have hdescent : baseEnd_829221 < baseStart_829221 := by decide
  rcases family_descends (prefixWord ++ tailWord_829221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829224 : List Nat := [2, 1, 5, 1, 1, 3, 3, 5]
def baseStart_829224 : Nat := 118140960795 + 829224 * 2 ^ 59
def prefixEnd_829224 : Nat := 4983230072969 + 3 ^ 40 * 829224 * 2
def baseEnd_829224 : Nat := 63080071443550946812811

theorem tailTrace_829224 : CollatzResearch.WordTrace tailWord_829224 prefixEnd_829224 63080071443550946812811 := by
  unfold tailWord_829224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122141973935271514675363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20162855965247028686233817 15122141973935271514675363)
  ·
    refine ⟨22683212960902907272013045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15122141973935271514675363 22683212960902907272013045)
    ·
      refine ⟨2126551215084647556751223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22683212960902907272013045 2126551215084647556751223)
      ·
        refine ⟨3189826822626971335126835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126551215084647556751223 3189826822626971335126835)
        ·
          refine ⟨4784740233940457002690253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189826822626971335126835 4784740233940457002690253)
          ·
            refine ⟨1794277587727671376008845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4784740233940457002690253 1794277587727671376008845)
            ·
              refine ⟨672854095397876766003317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1794277587727671376008845 672854095397876766003317)
              ·
                refine ⟨63080071443550946812811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 672854095397876766003317 63080071443550946812811)
                ·
                  rfl

theorem cell21_829224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_829224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829224 prefixEnd_829224 := by exact prefixLift 829224
  have htrace : WordTrace (prefixWord ++ tailWord_829224) baseStart_829224 baseEnd_829224 := by
    simpa [prefixWord, tailWord_829224, baseEnd_829224] using wordTrace_append hprefix tailTrace_829224
  have hstable : (prefixWord ++ tailWord_829224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829224).length < 2 ^ (prefixWord ++ tailWord_829224).sum := by decide
  have hdescent : baseEnd_829224 < baseStart_829224 := by decide
  rcases family_descends (prefixWord ++ tailWord_829224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829283 : List Nat := [1, 1, 1, 5, 4, 1, 1, 7]
def baseStart_829283 : Nat := 118140960795 + 829283 * 2 ^ 59
def prefixEnd_829283 : Nat := 4983230072969 + 3 ^ 40 * 829283 * 2
def baseEnd_829283 : Nat := 63084559644827282984993

theorem tailTrace_829283 : CollatzResearch.WordTrace tailWord_829283 prefixEnd_829283 63084559644827282984993 := by
  unfold tailWord_829283
  simp only [CollatzResearch.WordTrace]
  refine ⟨30246435854656796105748503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20164290569771197403832335 30246435854656796105748503)
  ·
    refine ⟨45369653781985194158622755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30246435854656796105748503 45369653781985194158622755)
    ·
      refine ⟨68054480672977791237934133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45369653781985194158622755 68054480672977791237934133)
      ·
        refine ⟨6380107563091667928556325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68054480672977791237934133 6380107563091667928556325)
        ·
          refine ⟨1196270168079687736604311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6380107563091667928556325 1196270168079687736604311)
          ·
            refine ⟨1794405252119531604906467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196270168079687736604311 1794405252119531604906467)
            ·
              refine ⟨2691607878179297407359701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794405252119531604906467 2691607878179297407359701)
              ·
                refine ⟨63084559644827282984993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2691607878179297407359701 63084559644827282984993)
                ·
                  rfl

theorem cell21_829283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 7].length) (baseStart_829283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829283 prefixEnd_829283 := by exact prefixLift 829283
  have htrace : WordTrace (prefixWord ++ tailWord_829283) baseStart_829283 baseEnd_829283 := by
    simpa [prefixWord, tailWord_829283, baseEnd_829283] using wordTrace_append hprefix tailTrace_829283
  have hstable : (prefixWord ++ tailWord_829283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829283).length < 2 ^ (prefixWord ++ tailWord_829283).sum := by decide
  have hdescent : baseEnd_829283 < baseStart_829283 := by decide
  rcases family_descends (prefixWord ++ tailWord_829283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829407 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 3]
def baseStart_829407 : Nat := 118140960795 + 829407 * 2 ^ 59
def prefixEnd_829407 : Nat := 4983230072969 + 3 ^ 40 * 829407 * 2
def baseEnd_829407 : Nat := 189281977423885188888059

theorem tailTrace_829407 : CollatzResearch.WordTrace tailWord_829407 prefixEnd_829407 189281977423885188888059 := by
  unfold tailWord_829407
  simp only [CollatzResearch.WordTrace]
  refine ⟨30250958506207565283262475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20167305670805043522174983 30250958506207565283262475)
  ·
    refine ⟨45376437759311347924893713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30250958506207565283262475 45376437759311347924893713)
    ·
      refine ⟨34032328319483510943670285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45376437759311347924893713 34032328319483510943670285)
      ·
        refine ⟨12762123119806316603876357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34032328319483510943670285 12762123119806316603876357)
        ·
          refine ⟨2392898084963684363226817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12762123119806316603876357 2392898084963684363226817)
          ·
            refine ⟨1794673563722763272420113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392898084963684363226817 1794673563722763272420113)
            ·
              refine ⟨1346005172792072454315085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794673563722763272420113 1346005172792072454315085)
              ·
                refine ⟨504751939797027170368157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346005172792072454315085 504751939797027170368157)
                ·
                  refine ⟨189281977423885188888059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504751939797027170368157 189281977423885188888059)
                  ·
                    rfl

theorem cell21_829407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3].length) (baseStart_829407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829407 prefixEnd_829407 := by exact prefixLift 829407
  have htrace : WordTrace (prefixWord ++ tailWord_829407) baseStart_829407 baseEnd_829407 := by
    simpa [prefixWord, tailWord_829407, baseEnd_829407] using wordTrace_append hprefix tailTrace_829407
  have hstable : (prefixWord ++ tailWord_829407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829407).length < 2 ^ (prefixWord ++ tailWord_829407).sum := by decide
  have hdescent : baseEnd_829407 < baseStart_829407 := by decide
  rcases family_descends (prefixWord ++ tailWord_829407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829418 : List Nat := [3, 1, 3, 1, 2, 1, 10]
def baseStart_829418 : Nat := 118140960795 + 829418 * 2 ^ 59
def prefixEnd_829418 : Nat := 4983230072969 + 3 ^ 40 * 829418 * 2
def baseEnd_829418 : Nat := 21031609752639068244967

theorem tailTrace_829418 : CollatzResearch.WordTrace tailWord_829418 prefixEnd_829418 21031609752639068244967 := by
  unfold tailWord_829418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562839927291928540478227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20167573139445142774608605 7562839927291928540478227)
  ·
    refine ⟨11344259890937892810717341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7562839927291928540478227 11344259890937892810717341)
    ·
      refine ⟨4254097459101709804019003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11344259890937892810717341 4254097459101709804019003)
      ·
        refine ⟨6381146188652564706028505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4254097459101709804019003 6381146188652564706028505)
        ·
          refine ⟨4785859641489423529521379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6381146188652564706028505 4785859641489423529521379)
          ·
            refine ⟨7178789462234135294282069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785859641489423529521379 7178789462234135294282069)
            ·
              refine ⟨21031609752639068244967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7178789462234135294282069 21031609752639068244967)
              ·
                rfl

theorem cell21_829418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 10].length) (baseStart_829418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829418 prefixEnd_829418 := by exact prefixLift 829418
  have htrace : WordTrace (prefixWord ++ tailWord_829418) baseStart_829418 baseEnd_829418 := by
    simpa [prefixWord, tailWord_829418, baseEnd_829418] using wordTrace_append hprefix tailTrace_829418
  have hstable : (prefixWord ++ tailWord_829418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829418).length < 2 ^ (prefixWord ++ tailWord_829418).sum := by decide
  have hdescent : baseEnd_829418 < baseStart_829418 := by decide
  rcases family_descends (prefixWord ++ tailWord_829418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829497 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_829497 : Nat := 118140960795 + 829497 * 2 ^ 59
def prefixEnd_829497 : Nat := 4983230072969 + 3 ^ 40 * 829497 * 2
def baseEnd_829497 : Nat := 189302516650065032387875

theorem tailTrace_829497 : CollatzResearch.WordTrace tailWord_829497 prefixEnd_829497 189302516650065032387875 := by
  unfold tailWord_829497
  simp only [CollatzResearch.WordTrace]
  refine ⟨30254241075881510654038745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20169494050587673769359163 30254241075881510654038745)
  ·
    refine ⟨22690680806911132990529059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30254241075881510654038745 22690680806911132990529059)
    ·
      refine ⟨34036021210366699485793589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22690680806911132990529059 34036021210366699485793589)
      ·
        refine ⟨3190876988471878076793149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34036021210366699485793589 3190876988471878076793149)
        ·
          refine ⟨1196578870676954278797431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3190876988471878076793149 1196578870676954278797431)
          ·
            refine ⟨1794868306015431418196147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196578870676954278797431 1794868306015431418196147)
            ·
              refine ⟨2692302459023147127294221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794868306015431418196147 2692302459023147127294221)
              ·
                refine ⟨1009613422133680172735333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2692302459023147127294221 1009613422133680172735333)
                ·
                  refine ⟨189302516650065032387875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009613422133680172735333 189302516650065032387875)
                  ·
                    rfl

theorem cell21_829497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_829497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829497 prefixEnd_829497 := by exact prefixLift 829497
  have htrace : WordTrace (prefixWord ++ tailWord_829497) baseStart_829497 baseEnd_829497 := by
    simpa [prefixWord, tailWord_829497, baseEnd_829497] using wordTrace_append hprefix tailTrace_829497
  have hstable : (prefixWord ++ tailWord_829497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829497).length < 2 ^ (prefixWord ++ tailWord_829497).sum := by decide
  have hdescent : baseEnd_829497 < baseStart_829497 := by decide
  rcases family_descends (prefixWord ++ tailWord_829497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829539 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_829539 : Nat := 118140960795 + 829539 * 2 ^ 59
def prefixEnd_829539 : Nat := 4983230072969 + 3 ^ 40 * 829539 * 2
def baseEnd_829539 : Nat := 189312101622282292687789

theorem tailTrace_829539 : CollatzResearch.WordTrace tailWord_829539 prefixEnd_829539 189312101622282292687789 := by
  unfold tailWord_829539
  simp only [CollatzResearch.WordTrace]
  refine ⟨30255772941729351827067671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20170515294486234551378447 30255772941729351827067671)
  ·
    refine ⟨45383659412594027740601507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30255772941729351827067671 45383659412594027740601507)
    ·
      refine ⟨68075489118891041610902261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45383659412594027740601507 68075489118891041610902261)
      ·
        refine ⟨6382077104896035151022087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68075489118891041610902261 6382077104896035151022087)
        ·
          refine ⟨9573115657344052726533131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6382077104896035151022087 9573115657344052726533131)
          ·
            refine ⟨14359673486016079089799697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9573115657344052726533131 14359673486016079089799697)
            ·
              refine ⟨10769755114512059317349773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14359673486016079089799697 10769755114512059317349773)
              ·
                refine ⟨4038658167942022244006165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10769755114512059317349773 4038658167942022244006165)
                ·
                  refine ⟨189312101622282292687789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4038658167942022244006165 189312101622282292687789)
                  ·
                    rfl

theorem cell21_829539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_829539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829539 prefixEnd_829539 := by exact prefixLift 829539
  have htrace : WordTrace (prefixWord ++ tailWord_829539) baseStart_829539 baseEnd_829539 := by
    simpa [prefixWord, tailWord_829539, baseEnd_829539] using wordTrace_append hprefix tailTrace_829539
  have hstable : (prefixWord ++ tailWord_829539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829539).length < 2 ^ (prefixWord ++ tailWord_829539).sum := by decide
  have hdescent : baseEnd_829539 < baseStart_829539 := by decide
  rcases family_descends (prefixWord ++ tailWord_829539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829584 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_829584 : Nat := 118140960795 + 829584 * 2 ^ 59
def prefixEnd_829584 : Nat := 4983230072969 + 3 ^ 40 * 829584 * 2
def baseEnd_829584 : Nat := 189322371235372214437697

theorem tailTrace_829584 : CollatzResearch.WordTrace tailWord_829584 prefixEnd_829584 189322371235372214437697 := by
  unfold tailWord_829584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128707113283162256227903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20171609484377549674970537 15128707113283162256227903)
  ·
    refine ⟨22693060669924743384341855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15128707113283162256227903 22693060669924743384341855)
    ·
      refine ⟨34039591004887115076512783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22693060669924743384341855 34039591004887115076512783)
      ·
        refine ⟨51059386507330672614769175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34039591004887115076512783 51059386507330672614769175)
        ·
          refine ⟨76589079760996008922153763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51059386507330672614769175 76589079760996008922153763)
          ·
            refine ⟨114883619641494013383230645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76589079760996008922153763 114883619641494013383230645)
            ·
              refine ⟨10770339341390063754677873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114883619641494013383230645 10770339341390063754677873)
              ·
                refine ⟨8077754506042547816008405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10770339341390063754677873 8077754506042547816008405)
                ·
                  refine ⟨189322371235372214437697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8077754506042547816008405 189322371235372214437697)
                  ·
                    rfl

theorem cell21_829584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_829584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829584 prefixEnd_829584 := by exact prefixLift 829584
  have htrace : WordTrace (prefixWord ++ tailWord_829584) baseStart_829584 baseEnd_829584 := by
    simpa [prefixWord, tailWord_829584, baseEnd_829584] using wordTrace_append hprefix tailTrace_829584
  have hstable : (prefixWord ++ tailWord_829584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829584).length < 2 ^ (prefixWord ++ tailWord_829584).sum := by decide
  have hdescent : baseEnd_829584 < baseStart_829584 := by decide
  rcases family_descends (prefixWord ++ tailWord_829584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829601 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 5]
def baseStart_829601 : Nat := 118140960795 + 829601 * 2 ^ 59
def prefixEnd_829601 : Nat := 4983230072969 + 3 ^ 40 * 829601 * 2
def baseEnd_829601 : Nat := 189326250866983962654329

theorem tailTrace_829601 : CollatzResearch.WordTrace tailWord_829601 prefixEnd_829601 189326250866983962654329 := by
  unfold tailWord_829601
  simp only [CollatzResearch.WordTrace]
  refine ⟨30258034267504736415824657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20172022845003157610549771 30258034267504736415824657)
  ·
    refine ⟨22693525700628552311868493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30258034267504736415824657 22693525700628552311868493)
    ·
      refine ⟨8510072137735707116950685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22693525700628552311868493 8510072137735707116950685)
      ·
        refine ⟨3191277051650890168856507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8510072137735707116950685 3191277051650890168856507)
        ·
          refine ⟨4786915577476335253284761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191277051650890168856507 4786915577476335253284761)
          ·
            refine ⟨3590186683107251439963571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4786915577476335253284761 3590186683107251439963571)
            ·
              refine ⟨5385280024660877159945357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590186683107251439963571 5385280024660877159945357)
              ·
                refine ⟨2019480009247828934979509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5385280024660877159945357 2019480009247828934979509)
                ·
                  refine ⟨189326250866983962654329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2019480009247828934979509 189326250866983962654329)
                  ·
                    rfl

theorem cell21_829601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_829601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829601 prefixEnd_829601 := by exact prefixLift 829601
  have htrace : WordTrace (prefixWord ++ tailWord_829601) baseStart_829601 baseEnd_829601 := by
    simpa [prefixWord, tailWord_829601, baseEnd_829601] using wordTrace_append hprefix tailTrace_829601
  have hstable : (prefixWord ++ tailWord_829601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829601).length < 2 ^ (prefixWord ++ tailWord_829601).sum := by decide
  have hdescent : baseEnd_829601 < baseStart_829601 := by decide
  rcases family_descends (prefixWord ++ tailWord_829601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829621 : List Nat := [1, 3, 3, 4, 1, 2, 2, 5]
def baseStart_829621 : Nat := 118140960795 + 829621 * 2 ^ 59
def prefixEnd_829621 : Nat := 4983230072969 + 3 ^ 40 * 829621 * 2
def baseEnd_829621 : Nat := 63110271713156124106985

theorem tailTrace_829621 : CollatzResearch.WordTrace tailWord_829621 prefixEnd_829621 63110271713156124106985 := by
  unfold tailWord_829621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30258763727432279831552717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20172509151621519887701811 30258763727432279831552717)
  ·
    refine ⟨11347036397787104936832269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30258763727432279831552717 11347036397787104936832269)
    ·
      refine ⟨4255138649170164351312101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11347036397787104936832269 4255138649170164351312101)
      ·
        refine ⟨797838496719405815871019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4255138649170164351312101 797838496719405815871019)
        ·
          refine ⟨1196757745079108723806529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797838496719405815871019 1196757745079108723806529)
          ·
            refine ⟨897568308809331542854897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1196757745079108723806529 897568308809331542854897)
            ·
              refine ⟨673176231606998657141173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897568308809331542854897 673176231606998657141173)
              ·
                refine ⟨63110271713156124106985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 673176231606998657141173 63110271713156124106985)
                ·
                  rfl

theorem cell21_829621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 5].length) (baseStart_829621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829621 prefixEnd_829621 := by exact prefixLift 829621
  have htrace : WordTrace (prefixWord ++ tailWord_829621) baseStart_829621 baseEnd_829621 := by
    simpa [prefixWord, tailWord_829621, baseEnd_829621] using wordTrace_append hprefix tailTrace_829621
  have hstable : (prefixWord ++ tailWord_829621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829621).length < 2 ^ (prefixWord ++ tailWord_829621).sum := by decide
  have hdescent : baseEnd_829621 < baseStart_829621 := by decide
  rcases family_descends (prefixWord ++ tailWord_829621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829646 : List Nat := [4, 1, 1, 1, 4, 1, 9]
def baseStart_829646 : Nat := 118140960795 + 829646 * 2 ^ 59
def prefixEnd_829646 : Nat := 4983230072969 + 3 ^ 40 * 829646 * 2
def baseEnd_829646 : Nat := 21037391164452653822693

theorem tailTrace_829646 : CollatzResearch.WordTrace tailWord_829646 prefixEnd_829646 21037391164452653822693 := by
  unfold tailWord_829646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3782459444042713637651599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20173117034894472734141861 3782459444042713637651599)
  ·
    refine ⟨5673689166064070456477399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3782459444042713637651599 5673689166064070456477399)
    ·
      refine ⟨8510533749096105684716099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5673689166064070456477399 8510533749096105684716099)
      ·
        refine ⟨12765800623644158527074149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8510533749096105684716099 12765800623644158527074149)
        ·
          refine ⟨2393587616933279723826403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12765800623644158527074149 2393587616933279723826403)
          ·
            refine ⟨3590381425399919585739605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2393587616933279723826403 3590381425399919585739605)
            ·
              refine ⟨21037391164452653822693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3590381425399919585739605 21037391164452653822693)
              ·
                rfl

theorem cell21_829646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 9].length) (baseStart_829646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829646 prefixEnd_829646 := by exact prefixLift 829646
  have htrace : WordTrace (prefixWord ++ tailWord_829646) baseStart_829646 baseEnd_829646 := by
    simpa [prefixWord, tailWord_829646, baseEnd_829646] using wordTrace_append hprefix tailTrace_829646
  have hstable : (prefixWord ++ tailWord_829646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829646).length < 2 ^ (prefixWord ++ tailWord_829646).sum := by decide
  have hdescent : baseEnd_829646 < baseStart_829646 := by decide
  rcases family_descends (prefixWord ++ tailWord_829646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829705 : List Nat := [1, 2, 1, 1, 3, 13]
def baseStart_829705 : Nat := 118140960795 + 829705 * 2 ^ 59
def prefixEnd_829705 : Nat := 4983230072969 + 3 ^ 40 * 829705 * 2
def baseEnd_829705 : Nat := 7012962410514921960029

theorem tailTrace_829705 : CollatzResearch.WordTrace tailWord_829705 prefixEnd_829705 7012962410514921960029 := by
  unfold tailWord_829705
  simp only [CollatzResearch.WordTrace]
  refine ⟨30261827459127962177610569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20174551639418641451740379 30261827459127962177610569)
  ·
    refine ⟨22696370594345971633207927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30261827459127962177610569 22696370594345971633207927)
    ·
      refine ⟨34044555891518957449811891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22696370594345971633207927 34044555891518957449811891)
      ·
        refine ⟨51066833837278436174717837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34044555891518957449811891 51066833837278436174717837)
        ·
          refine ⟨19150062688979413565519189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51066833837278436174717837 19150062688979413565519189)
          ·
            refine ⟨7012962410514921960029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 19150062688979413565519189 7012962410514921960029)
            ·
              rfl

theorem cell21_829705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 13].length) (baseStart_829705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829705 prefixEnd_829705 := by exact prefixLift 829705
  have htrace : WordTrace (prefixWord ++ tailWord_829705) baseStart_829705 baseEnd_829705 := by
    simpa [prefixWord, tailWord_829705, baseEnd_829705] using wordTrace_append hprefix tailTrace_829705
  have hstable : (prefixWord ++ tailWord_829705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829705).length < 2 ^ (prefixWord ++ tailWord_829705).sum := by decide
  have hdescent : baseEnd_829705 < baseStart_829705 := by decide
  rcases family_descends (prefixWord ++ tailWord_829705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829708 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 4]
def baseStart_829708 : Nat := 118140960795 + 829708 * 2 ^ 59
def prefixEnd_829708 : Nat := 4983230072969 + 3 ^ 40 * 829708 * 2
def baseEnd_829708 : Nat := 189350669724775554370777

theorem tailTrace_829708 : CollatzResearch.WordTrace tailWord_829708 prefixEnd_829708 189350669724775554370777 := by
  unfold tailWord_829708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130968439058546844984889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20174624585411395793313185 15130968439058546844984889)
  ·
    refine ⟨11348226329293910133738667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15130968439058546844984889 11348226329293910133738667)
    ·
      refine ⟨17022339493940865200608001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348226329293910133738667 17022339493940865200608001)
      ·
        refine ⟨12766754620455648900456001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17022339493940865200608001 12766754620455648900456001)
        ·
          refine ⟨9575065965341736675342001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12766754620455648900456001 9575065965341736675342001)
          ·
            refine ⟨7181299474006302506506501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9575065965341736675342001 7181299474006302506506501)
            ·
              refine ⟨1346493651376181719969969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7181299474006302506506501 1346493651376181719969969)
              ·
                refine ⟨1009870238532136289977477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346493651376181719969969 1009870238532136289977477)
                ·
                  refine ⟨189350669724775554370777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1009870238532136289977477 189350669724775554370777)
                  ·
                    rfl

theorem cell21_829708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_829708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829708 prefixEnd_829708 := by exact prefixLift 829708
  have htrace : WordTrace (prefixWord ++ tailWord_829708) baseStart_829708 baseEnd_829708 := by
    simpa [prefixWord, tailWord_829708, baseEnd_829708] using wordTrace_append hprefix tailTrace_829708
  have hstable : (prefixWord ++ tailWord_829708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829708).length < 2 ^ (prefixWord ++ tailWord_829708).sum := by decide
  have hdescent : baseEnd_829708 < baseStart_829708 := by decide
  rcases family_descends (prefixWord ++ tailWord_829708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829767 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_829767 : Nat := 118140960795 + 829767 * 2 ^ 59
def prefixEnd_829767 : Nat := 4983230072969 + 3 ^ 40 * 829767 * 2
def baseEnd_829767 : Nat := 189364134328604562887323

theorem tailTrace_829767 : CollatzResearch.WordTrace tailWord_829767 prefixEnd_829767 189364134328604562887323 := by
  unfold tailWord_829767
  simp only [CollatzResearch.WordTrace]
  refine ⟨30264088784903346766367555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20176059189935564510911703 30264088784903346766367555)
  ·
    refine ⟨45396133177355020149551333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30264088784903346766367555 45396133177355020149551333)
    ·
      refine ⟨8511774970754066278040875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45396133177355020149551333 8511774970754066278040875)
      ·
        refine ⟨12767662456131099417061313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8511774970754066278040875 12767662456131099417061313)
        ·
          refine ⟨9575746842098324562795985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12767662456131099417061313 9575746842098324562795985)
          ·
            refine ⟨7181810131573743422096989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9575746842098324562795985 7181810131573743422096989)
            ·
              refine ⟨2693178799340153783286371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7181810131573743422096989 2693178799340153783286371)
              ·
                refine ⟨4039768199010230674929557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693178799340153783286371 4039768199010230674929557)
                ·
                  refine ⟨189364134328604562887323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4039768199010230674929557 189364134328604562887323)
                  ·
                    rfl

theorem cell21_829767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_829767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829767 prefixEnd_829767 := by exact prefixLift 829767
  have htrace : WordTrace (prefixWord ++ tailWord_829767) baseStart_829767 baseEnd_829767 := by
    simpa [prefixWord, tailWord_829767, baseEnd_829767] using wordTrace_append hprefix tailTrace_829767
  have hstable : (prefixWord ++ tailWord_829767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829767).length < 2 ^ (prefixWord ++ tailWord_829767).sum := by decide
  have hdescent : baseEnd_829767 < baseStart_829767 := by decide
  rcases family_descends (prefixWord ++ tailWord_829767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829790 : List Nat := [4, 4, 2, 1, 1, 1, 1, 7]
def baseStart_829790 : Nat := 118140960795 + 829790 * 2 ^ 59
def prefixEnd_829790 : Nat := 4983230072969 + 3 ^ 40 * 829790 * 2
def baseEnd_829790 : Nat := 63123127747320544667981

theorem tailTrace_829790 : CollatzResearch.WordTrace tailWord_829790 prefixEnd_829790 63123127747320544667981 := by
  unfold tailWord_829790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783115957977502711806853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20176618442546681129636549 3783115957977502711806853)
  ·
    refine ⟨709334242120781758463785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3783115957977502711806853 709334242120781758463785)
    ·
      refine ⟨532000681590586318847839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 709334242120781758463785 532000681590586318847839)
      ·
        refine ⟨798001022385879478271759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532000681590586318847839 798001022385879478271759)
        ·
          refine ⟨1197001533578819217407639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798001022385879478271759 1197001533578819217407639)
          ·
            refine ⟨1795502300368228826111459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197001533578819217407639 1795502300368228826111459)
            ·
              refine ⟨2693253450552343239167189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795502300368228826111459 2693253450552343239167189)
              ·
                refine ⟨63123127747320544667981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2693253450552343239167189 63123127747320544667981)
                ·
                  rfl

theorem cell21_829790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_829790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829790 prefixEnd_829790 := by exact prefixLift 829790
  have htrace : WordTrace (prefixWord ++ tailWord_829790) baseStart_829790 baseEnd_829790 := by
    simpa [prefixWord, tailWord_829790, baseEnd_829790] using wordTrace_append hprefix tailTrace_829790
  have hstable : (prefixWord ++ tailWord_829790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829790).length < 2 ^ (prefixWord ++ tailWord_829790).sum := by decide
  have hdescent : baseEnd_829790 < baseStart_829790 := by decide
  rcases family_descends (prefixWord ++ tailWord_829790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829804 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 3]
def baseStart_829804 : Nat := 118140960795 + 829804 * 2 ^ 59
def prefixEnd_829804 : Nat := 4983230072969 + 3 ^ 40 * 829804 * 2
def baseEnd_829804 : Nat := 189372578232700720770581

theorem tailTrace_829804 : CollatzResearch.WordTrace tailWord_829804 prefixEnd_829804 189372578232700720770581 := by
  unfold tailWord_829804
  simp only [CollatzResearch.WordTrace]
  refine ⟨15132719142884651042732233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20176958857179534723642977 15132719142884651042732233)
  ·
    refine ⟨11349539357163488282049175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15132719142884651042732233 11349539357163488282049175)
    ·
      refine ⟨17024309035745232423073763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11349539357163488282049175 17024309035745232423073763)
      ·
        refine ⟨25536463553617848634610645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17024309035745232423073763 25536463553617848634610645)
        ·
          refine ⟨598510864537918327373687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25536463553617848634610645 598510864537918327373687)
          ·
            refine ⟨897766296806877491060531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598510864537918327373687 897766296806877491060531)
            ·
              refine ⟨1346649445210316236590797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897766296806877491060531 1346649445210316236590797)
              ·
                refine ⟨504993541953868588721549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346649445210316236590797 504993541953868588721549)
                ·
                  refine ⟨189372578232700720770581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 504993541953868588721549 189372578232700720770581)
                  ·
                    rfl

theorem cell21_829804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_829804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829804 prefixEnd_829804 := by exact prefixLift 829804
  have htrace : WordTrace (prefixWord ++ tailWord_829804) baseStart_829804 baseEnd_829804 := by
    simpa [prefixWord, tailWord_829804, baseEnd_829804] using wordTrace_append hprefix tailTrace_829804
  have hstable : (prefixWord ++ tailWord_829804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829804).length < 2 ^ (prefixWord ++ tailWord_829804).sum := by decide
  have hdescent : baseEnd_829804 < baseStart_829804 := by decide
  rcases family_descends (prefixWord ++ tailWord_829804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829877 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 4]
def baseStart_829877 : Nat := 118140960795 + 829877 * 2 ^ 59
def prefixEnd_829877 : Nat := 4983230072969 + 3 ^ 40 * 829877 * 2
def baseEnd_829877 : Nat := 189389237827268816053765

theorem tailTrace_829877 : CollatzResearch.WordTrace tailWord_829877 prefixEnd_829877 189389237827268816053765 := by
  unfold tailWord_829877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30268100814504835552871885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20178733876336557035247923 30268100814504835552871885)
  ·
    refine ⟨11350537805439313332326957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30268100814504835552871885 11350537805439313332326957)
    ·
      refine ⟨4256451677039742499622609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11350537805439313332326957 4256451677039742499622609)
      ·
        refine ⟨3192338757779806874716957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4256451677039742499622609 3192338757779806874716957)
        ·
          refine ⟨1197127034167427578018859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3192338757779806874716957 1197127034167427578018859)
          ·
            refine ⟨1795690551251141367028289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197127034167427578018859 1795690551251141367028289)
            ·
              refine ⟨1346767913438356025271217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795690551251141367028289 1346767913438356025271217)
              ·
                refine ⟨1010075935078767018953413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346767913438356025271217 1010075935078767018953413)
                ·
                  refine ⟨189389237827268816053765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010075935078767018953413 189389237827268816053765)
                  ·
                    rfl

theorem cell21_829877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_829877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829877 prefixEnd_829877 := by exact prefixLift 829877
  have htrace : WordTrace (prefixWord ++ tailWord_829877) baseStart_829877 baseEnd_829877 := by
    simpa [prefixWord, tailWord_829877, baseEnd_829877] using wordTrace_append hprefix tailTrace_829877
  have hstable : (prefixWord ++ tailWord_829877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829877).length < 2 ^ (prefixWord ++ tailWord_829877).sum := by decide
  have hdescent : baseEnd_829877 < baseStart_829877 := by decide
  rcases family_descends (prefixWord ++ tailWord_829877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829888 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 5]
def baseStart_829888 : Nat := 118140960795 + 829888 * 2 ^ 59
def prefixEnd_829888 : Nat := 4983230072969 + 3 ^ 40 * 829888 * 2
def baseEnd_829888 : Nat := 189391748177135241370409

theorem tailTrace_829888 : CollatzResearch.WordTrace tailWord_829888 prefixEnd_829888 189391748177135241370409 := by
  unfold tailWord_829888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134251008732492215761159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20179001344976656287681545 15134251008732492215761159)
  ·
    refine ⟨22701376513098738323641739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134251008732492215761159 22701376513098738323641739)
    ·
      refine ⟨34052064769648107485462609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22701376513098738323641739 34052064769648107485462609)
      ·
        refine ⟨25539048577236080614096957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34052064769648107485462609 25539048577236080614096957)
        ·
          refine ⟨9577143216463530230286359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25539048577236080614096957 9577143216463530230286359)
          ·
            refine ⟨14365714824695295345429539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9577143216463530230286359 14365714824695295345429539)
            ·
              refine ⟨21548572237042943018144309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14365714824695295345429539 21548572237042943018144309)
              ·
                refine ⟨2020178647222775907951029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21548572237042943018144309 2020178647222775907951029)
                ·
                  refine ⟨189391748177135241370409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020178647222775907951029 189391748177135241370409)
                  ·
                    rfl

theorem cell21_829888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_829888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829888 prefixEnd_829888 := by exact prefixLift 829888
  have htrace : WordTrace (prefixWord ++ tailWord_829888) baseStart_829888 baseEnd_829888 := by
    simpa [prefixWord, tailWord_829888, baseEnd_829888] using wordTrace_append hprefix tailTrace_829888
  have hstable : (prefixWord ++ tailWord_829888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829888).length < 2 ^ (prefixWord ++ tailWord_829888).sum := by decide
  have hdescent : baseEnd_829888 < baseStart_829888 := by decide
  rcases family_descends (prefixWord ++ tailWord_829888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829953 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 4]
def baseStart_829953 : Nat := 118140960795 + 829953 * 2 ^ 59
def prefixEnd_829953 : Nat := 4983230072969 + 3 ^ 40 * 829953 * 2
def baseEnd_829953 : Nat := 189406582062709572786943

theorem tailTrace_829953 : CollatzResearch.WordTrace tailWord_829953 prefixEnd_829953 189406582062709572786943 := by
  unfold tailWord_829953
  simp only [CollatzResearch.WordTrace]
  refine ⟨30270872762229500532638513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20180581841486333688425675 30270872762229500532638513)
  ·
    refine ⟨22703154571672125399478885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30270872762229500532638513 22703154571672125399478885)
    ·
      refine ⟨4256841482188523512402291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22703154571672125399478885 4256841482188523512402291)
      ·
        refine ⟨6385262223282785268603437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4256841482188523512402291 6385262223282785268603437)
        ·
          refine ⟨2394473333731044475726289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6385262223282785268603437 2394473333731044475726289)
          ·
            refine ⟨1795855000298283356794717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394473333731044475726289 1795855000298283356794717)
            ·
              refine ⟨673445625111856258798019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1795855000298283356794717 673445625111856258798019)
              ·
                refine ⟨1010168437667784388197029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673445625111856258798019 1010168437667784388197029)
                ·
                  refine ⟨189406582062709572786943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010168437667784388197029 189406582062709572786943)
                  ·
                    rfl

theorem cell21_829953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_829953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_829953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_829953 prefixEnd_829953 := by exact prefixLift 829953
  have htrace : WordTrace (prefixWord ++ tailWord_829953) baseStart_829953 baseEnd_829953 := by
    simpa [prefixWord, tailWord_829953, baseEnd_829953] using wordTrace_append hprefix tailTrace_829953
  have hstable : (prefixWord ++ tailWord_829953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829953).length < 2 ^ (prefixWord ++ tailWord_829953).sum := by decide
  have hdescent : baseEnd_829953 < baseStart_829953 := by decide
  rcases family_descends (prefixWord ++ tailWord_829953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830004 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_830004 : Nat := 118140960795 + 830004 * 2 ^ 59
def prefixEnd_830004 : Nat := 4983230072969 + 3 ^ 40 * 830004 * 2
def baseEnd_830004 : Nat := 189418220957544817436839

theorem tailTrace_830004 : CollatzResearch.WordTrace tailWord_830004 prefixEnd_830004 189418220957544817436839 := by
  unfold tailWord_830004
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136366442522368121372533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20181821923363157495163377 15136366442522368121372533)
  ·
    refine ⟨1419034353986472011378675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15136366442522368121372533 1419034353986472011378675)
    ·
      refine ⟨2128551530979708017068013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419034353986472011378675 2128551530979708017068013)
      ·
        refine ⟨798206824117390506400505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2128551530979708017068013 798206824117390506400505)
        ·
          refine ⟨598655118088042879800379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798206824117390506400505 598655118088042879800379)
          ·
            refine ⟨897982677132064319700569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598655118088042879800379 897982677132064319700569)
            ·
              refine ⟨673487007849048239775427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897982677132064319700569 673487007849048239775427)
              ·
                refine ⟨1010230511773572359663141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673487007849048239775427 1010230511773572359663141)
                ·
                  refine ⟨189418220957544817436839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010230511773572359663141 189418220957544817436839)
                  ·
                    rfl

theorem cell21_830004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_830004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830004 prefixEnd_830004 := by exact prefixLift 830004
  have htrace : WordTrace (prefixWord ++ tailWord_830004) baseStart_830004 baseEnd_830004 := by
    simpa [prefixWord, tailWord_830004, baseEnd_830004] using wordTrace_append hprefix tailTrace_830004
  have hstable : (prefixWord ++ tailWord_830004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830004).length < 2 ^ (prefixWord ++ tailWord_830004).sum := by decide
  have hdescent : baseEnd_830004 < baseStart_830004 := by decide
  rcases family_descends (prefixWord ++ tailWord_830004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830012 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 4]
def baseStart_830012 : Nat := 118140960795 + 830012 * 2 ^ 59
def prefixEnd_830012 : Nat := 4983230072969 + 3 ^ 40 * 830012 * 2
def baseEnd_830012 : Nat := 189420046666538581303489

theorem tailTrace_830012 : CollatzResearch.WordTrace tailWord_830012 prefixEnd_830012 189420046666538581303489 := by
  unfold tailWord_830012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15136512334507876804518145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20182016446010502406024193 15136512334507876804518145)
  ·
    refine ⟨11352384250880907603388609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15136512334507876804518145 11352384250880907603388609)
    ·
      refine ⟨8514288188160680702541457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11352384250880907603388609 8514288188160680702541457)
      ·
        refine ⟨6385716141120510526906093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8514288188160680702541457 6385716141120510526906093)
        ·
          refine ⟨2394643552920191447589785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6385716141120510526906093 2394643552920191447589785)
          ·
            refine ⟨1795982664690143585692339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394643552920191447589785 1795982664690143585692339)
            ·
              refine ⟨2693973997035215378538509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795982664690143585692339 2693973997035215378538509)
              ·
                refine ⟨1010240248888205766951941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2693973997035215378538509 1010240248888205766951941)
                ·
                  refine ⟨189420046666538581303489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010240248888205766951941 189420046666538581303489)
                  ·
                    rfl

theorem cell21_830012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_830012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830012 prefixEnd_830012 := by exact prefixLift 830012
  have htrace : WordTrace (prefixWord ++ tailWord_830012) baseStart_830012 baseEnd_830012 := by
    simpa [prefixWord, tailWord_830012, baseEnd_830012] using wordTrace_append hprefix tailTrace_830012
  have hstable : (prefixWord ++ tailWord_830012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830012).length < 2 ^ (prefixWord ++ tailWord_830012).sum := by decide
  have hdescent : baseEnd_830012 < baseStart_830012 := by decide
  rcases family_descends (prefixWord ++ tailWord_830012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830071 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 4]
def baseStart_830071 : Nat := 118140960795 + 830071 * 2 ^ 59
def prefixEnd_830071 : Nat := 4983230072969 + 3 ^ 40 * 830071 * 2
def baseEnd_830071 : Nat := 189433511270367589820035

theorem tailTrace_830071 : CollatzResearch.WordTrace tailWord_830071 prefixEnd_830071 189433511270367589820035 := by
  unfold tailWord_830071
  simp only [CollatzResearch.WordTrace]
  refine ⟨30275176575802006685434067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20183451050534671123622711 30275176575802006685434067)
  ·
    refine ⟨45412764863703010028151101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30275176575802006685434067 45412764863703010028151101)
    ·
      refine ⟨17029786823888628760556663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45412764863703010028151101 17029786823888628760556663)
      ·
        refine ⟨25544680235832943140834995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17029786823888628760556663 25544680235832943140834995)
        ·
          refine ⟨38317020353749414711252493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25544680235832943140834995 38317020353749414711252493)
          ·
            refine ⟨14368882632656030516719685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38317020353749414711252493 14368882632656030516719685)
            ·
              refine ⟨2694165493623005721884941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14368882632656030516719685 2694165493623005721884941)
              ·
                refine ⟨1010312060108627145706853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2694165493623005721884941 1010312060108627145706853)
                ·
                  refine ⟨189433511270367589820035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010312060108627145706853 189433511270367589820035)
                  ·
                    rfl

theorem cell21_830071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 4].length) (baseStart_830071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830071 prefixEnd_830071 := by exact prefixLift 830071
  have htrace : WordTrace (prefixWord ++ tailWord_830071) baseStart_830071 baseEnd_830071 := by
    simpa [prefixWord, tailWord_830071, baseEnd_830071] using wordTrace_append hprefix tailTrace_830071
  have hstable : (prefixWord ++ tailWord_830071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830071).length < 2 ^ (prefixWord ++ tailWord_830071).sum := by decide
  have hdescent : baseEnd_830071 < baseStart_830071 := by decide
  rcases family_descends (prefixWord ++ tailWord_830071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830133 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_830133 : Nat := 118140960795 + 830133 * 2 ^ 59
def prefixEnd_830133 : Nat := 4983230072969 + 3 ^ 40 * 830133 * 2
def baseEnd_830133 : Nat := 189447660515069259786575

theorem tailTrace_830133 : CollatzResearch.WordTrace tailWord_830133 prefixEnd_830133 189447660515069259786575 := by
  unfold tailWord_830133
  simp only [CollatzResearch.WordTrace]
  refine ⟨30277437901577391274191053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20184958601051594182794035 30277437901577391274191053)
  ·
    refine ⟨11354039213091521727821645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30277437901577391274191053 11354039213091521727821645)
    ·
      refine ⟨4257764704909320647933117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11354039213091521727821645 4257764704909320647933117)
      ·
        refine ⟨1596661764340995242974919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4257764704909320647933117 1596661764340995242974919)
        ·
          refine ⟨2394992646511492864462379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596661764340995242974919 2394992646511492864462379)
          ·
            refine ⟨3592488969767239296693569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2394992646511492864462379 3592488969767239296693569)
            ·
              refine ⟨2694366727325429472520177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3592488969767239296693569 2694366727325429472520177)
              ·
                refine ⟨2020775045494072104390133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2694366727325429472520177 2020775045494072104390133)
                ·
                  refine ⟨189447660515069259786575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2020775045494072104390133 189447660515069259786575)
                  ·
                    rfl

theorem cell21_830133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_830133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830133 prefixEnd_830133 := by exact prefixLift 830133
  have htrace : WordTrace (prefixWord ++ tailWord_830133) baseStart_830133 baseEnd_830133 := by
    simpa [prefixWord, tailWord_830133, baseEnd_830133] using wordTrace_append hprefix tailTrace_830133
  have hstable : (prefixWord ++ tailWord_830133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830133).length < 2 ^ (prefixWord ++ tailWord_830133).sum := by decide
  have hdescent : baseEnd_830133 < baseStart_830133 := by decide
  rcases family_descends (prefixWord ++ tailWord_830133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830181 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 4]
def baseStart_830181 : Nat := 118140960795 + 830181 * 2 ^ 59
def prefixEnd_830181 : Nat := 4983230072969 + 3 ^ 40 * 830181 * 2
def baseEnd_830181 : Nat := 189458614769031842986477

theorem tailTrace_830181 : CollatzResearch.WordTrace tailWord_830181 prefixEnd_830181 189458614769031842986477 := by
  unfold tailWord_830181
  simp only [CollatzResearch.WordTrace]
  refine ⟨30279188605403495471938397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20186125736935663647958931 30279188605403495471938397)
  ·
    refine ⟨11354695727026310801976899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30279188605403495471938397 11354695727026310801976899)
    ·
      refine ⟨17032043590539466202965349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354695727026310801976899 17032043590539466202965349)
      ·
        refine ⟨3193508173226149913056003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17032043590539466202965349 3193508173226149913056003)
        ·
          refine ⟨4790262259839224869584005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193508173226149913056003 4790262259839224869584005)
          ·
            refine ⟨898174173719854663047001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4790262259839224869584005 898174173719854663047001)
            ·
              refine ⟨673630630289890997285251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898174173719854663047001 673630630289890997285251)
              ·
                refine ⟨1010445945434836495927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673630630289890997285251 1010445945434836495927877)
                ·
                  refine ⟨189458614769031842986477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010445945434836495927877 189458614769031842986477)
                  ·
                    rfl

theorem cell21_830181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_830181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830181 prefixEnd_830181 := by exact prefixLift 830181
  have htrace : WordTrace (prefixWord ++ tailWord_830181) baseStart_830181 baseEnd_830181 := by
    simpa [prefixWord, tailWord_830181, baseEnd_830181] using wordTrace_append hprefix tailTrace_830181
  have hstable : (prefixWord ++ tailWord_830181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830181).length < 2 ^ (prefixWord ++ tailWord_830181).sum := by decide
  have hdescent : baseEnd_830181 < baseStart_830181 := by decide
  rcases family_descends (prefixWord ++ tailWord_830181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830209 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 3]
def baseStart_830209 : Nat := 118140960795 + 830209 * 2 ^ 59
def prefixEnd_830209 : Nat := 4983230072969 + 3 ^ 40 * 830209 * 2
def baseEnd_830209 : Nat := 189465004750510016519753

theorem tailTrace_830209 : CollatzResearch.WordTrace tailWord_830209 prefixEnd_830209 189465004750510016519753 := by
  unfold tailWord_830209
  simp only [CollatzResearch.WordTrace]
  refine ⟨30280209849302056253957681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20186806566201370835971787 30280209849302056253957681)
  ·
    refine ⟨22710157386976542190468261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30280209849302056253957681 22710157386976542190468261)
    ·
      refine ⟨4258154510058101660712799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22710157386976542190468261 4258154510058101660712799)
      ·
        refine ⟨6387231765087152491069199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4258154510058101660712799 6387231765087152491069199)
        ·
          refine ⟨9580847647630728736603799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6387231765087152491069199 9580847647630728736603799)
          ·
            refine ⟨14371271471446093104905699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9580847647630728736603799 14371271471446093104905699)
            ·
              refine ⟨21556907207169139657358549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14371271471446093104905699 21556907207169139657358549)
              ·
                refine ⟨505240012668026710719341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21556907207169139657358549 505240012668026710719341)
                ·
                  refine ⟨189465004750510016519753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505240012668026710719341 189465004750510016519753)
                  ·
                    rfl

theorem cell21_830209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 3].length) (baseStart_830209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830209 prefixEnd_830209 := by exact prefixLift 830209
  have htrace : WordTrace (prefixWord ++ tailWord_830209) baseStart_830209 baseEnd_830209 := by
    simpa [prefixWord, tailWord_830209, baseEnd_830209] using wordTrace_append hprefix tailTrace_830209
  have hstable : (prefixWord ++ tailWord_830209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830209).length < 2 ^ (prefixWord ++ tailWord_830209).sum := by decide
  have hdescent : baseEnd_830209 < baseStart_830209 := by decide
  rcases family_descends (prefixWord ++ tailWord_830209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830223 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_830223 : Nat := 118140960795 + 830223 * 2 ^ 59
def prefixEnd_830223 : Nat := 4983230072969 + 3 ^ 40 * 830223 * 2
def baseEnd_830223 : Nat := 189468199741249103286391

theorem tailTrace_830223 : CollatzResearch.WordTrace tailWord_830223 prefixEnd_830223 189468199741249103286391 := by
  unfold tailWord_830223
  simp only [CollatzResearch.WordTrace]
  refine ⟨30280720471251336644967323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20187146980834224429978215 30280720471251336644967323)
  ·
    refine ⟨45421080706877004967450985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30280720471251336644967323 45421080706877004967450985)
    ·
      refine ⟨34065810530157753725588239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45421080706877004967450985 34065810530157753725588239)
      ·
        refine ⟨51098715795236630588382359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34065810530157753725588239 51098715795236630588382359)
        ·
          refine ⟨76648073692854945882573539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51098715795236630588382359 76648073692854945882573539)
          ·
            refine ⟨114972110539282418823860309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76648073692854945882573539 114972110539282418823860309)
            ·
              refine ⟨1347329420382215845592113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 114972110539282418823860309 1347329420382215845592113)
              ·
                refine ⟨1010497065286661884194085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347329420382215845592113 1010497065286661884194085)
                ·
                  refine ⟨189468199741249103286391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010497065286661884194085 189468199741249103286391)
                  ·
                    rfl

theorem cell21_830223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_830223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830223 prefixEnd_830223 := by exact prefixLift 830223
  have htrace : WordTrace (prefixWord ++ tailWord_830223) baseStart_830223 baseEnd_830223 := by
    simpa [prefixWord, tailWord_830223, baseEnd_830223] using wordTrace_append hprefix tailTrace_830223
  have hstable : (prefixWord ++ tailWord_830223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830223).length < 2 ^ (prefixWord ++ tailWord_830223).sum := by decide
  have hdescent : baseEnd_830223 < baseStart_830223 := by decide
  rcases family_descends (prefixWord ++ tailWord_830223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830251 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 7]
def baseStart_830251 : Nat := 118140960795 + 830251 * 2 ^ 59
def prefixEnd_830251 : Nat := 4983230072969 + 3 ^ 40 * 830251 * 2
def baseEnd_830251 : Nat := 189474589722727276819667

theorem tailTrace_830251 : CollatzResearch.WordTrace tailWord_830251 prefixEnd_830251 189474589722727276819667 := by
  unfold tailWord_830251
  simp only [CollatzResearch.WordTrace]
  refine ⟨30281741715149897426986607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20187827810099931617991071 30281741715149897426986607)
  ·
    refine ⟨45422612572724846140479911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30281741715149897426986607 45422612572724846140479911)
    ·
      refine ⟨68133918859087269210719867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45422612572724846140479911 68133918859087269210719867)
      ·
        refine ⟨102200878288630903816079801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68133918859087269210719867 102200878288630903816079801)
        ·
          refine ⟨76650658716473177862059851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102200878288630903816079801 76650658716473177862059851)
          ·
            refine ⟨114975988074709766793089777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76650658716473177862059851 114975988074709766793089777)
            ·
              refine ⟨86231991056032325094817333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114975988074709766793089777 86231991056032325094817333)
              ·
                refine ⟨8084249161503030477639125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86231991056032325094817333 8084249161503030477639125)
                ·
                  refine ⟨189474589722727276819667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8084249161503030477639125 189474589722727276819667)
                  ·
                    rfl

theorem cell21_830251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_830251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830251 prefixEnd_830251 := by exact prefixLift 830251
  have htrace : WordTrace (prefixWord ++ tailWord_830251) baseStart_830251 baseEnd_830251 := by
    simpa [prefixWord, tailWord_830251, baseEnd_830251] using wordTrace_append hprefix tailTrace_830251
  have hstable : (prefixWord ++ tailWord_830251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830251).length < 2 ^ (prefixWord ++ tailWord_830251).sum := by decide
  have hdescent : baseEnd_830251 < baseStart_830251 := by decide
  rcases family_descends (prefixWord ++ tailWord_830251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830327 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 7]
def baseStart_830327 : Nat := 118140960795 + 830327 * 2 ^ 59
def prefixEnd_830327 : Nat := 4983230072969 + 3 ^ 40 * 830327 * 2
def baseEnd_830327 : Nat := 189491933958168033552845

theorem tailTrace_830327 : CollatzResearch.WordTrace tailWord_830327 prefixEnd_830327 189491933958168033552845 := by
  unfold tailWord_830327
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284513662874562406753235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20189675775249708271168823 30284513662874562406753235)
  ·
    refine ⟨45426770494311843610129853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30284513662874562406753235 45426770494311843610129853)
    ·
      refine ⟨17035038935366941353798695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45426770494311843610129853 17035038935366941353798695)
      ·
        refine ⟨25552558403050412030698043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17035038935366941353798695 25552558403050412030698043)
        ·
          refine ⟨38328837604575618046047065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25552558403050412030698043 38328837604575618046047065)
          ·
            refine ⟨28746628203431713534535299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38328837604575618046047065 28746628203431713534535299)
            ·
              refine ⟨43119942305147570301802949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28746628203431713534535299 43119942305147570301802949)
              ·
                refine ⟨8084989182215169431588053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43119942305147570301802949 8084989182215169431588053)
                ·
                  refine ⟨189491933958168033552845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8084989182215169431588053 189491933958168033552845)
                  ·
                    rfl

theorem cell21_830327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_830327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830327 prefixEnd_830327 := by exact prefixLift 830327
  have htrace : WordTrace (prefixWord ++ tailWord_830327) baseStart_830327 baseEnd_830327 := by
    simpa [prefixWord, tailWord_830327, baseEnd_830327] using wordTrace_append hprefix tailTrace_830327
  have hstable : (prefixWord ++ tailWord_830327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830327).length < 2 ^ (prefixWord ++ tailWord_830327).sum := by decide
  have hdescent : baseEnd_830327 < baseStart_830327 := by decide
  rcases family_descends (prefixWord ++ tailWord_830327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830420 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 7]
def baseStart_830420 : Nat := 118140960795 + 830420 * 2 ^ 59
def prefixEnd_830420 : Nat := 4983230072969 + 3 ^ 40 * 830420 * 2
def baseEnd_830420 : Nat := 189513157825220538502655

theorem tailTrace_830420 : CollatzResearch.WordTrace tailWord_830420 prefixEnd_830420 189513157825220538502655 := by
  unfold tailWord_830420
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143952825768819644944357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20191937101025092859925809 15143952825768819644944357)
  ·
    refine ⟨2839491154831653683427067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15143952825768819644944357 2839491154831653683427067)
    ·
      refine ⟨4259236732247480525140601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2839491154831653683427067 4259236732247480525140601)
      ·
        refine ⟨3194427549185610393855451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4259236732247480525140601 3194427549185610393855451)
        ·
          refine ⟨4791641323778415590783177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194427549185610393855451 4791641323778415590783177)
          ·
            refine ⟨3593730992833811693087383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4791641323778415590783177 3593730992833811693087383)
            ·
              refine ⟨5390596489250717539631075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3593730992833811693087383 5390596489250717539631075)
              ·
                refine ⟨8085894733876076309446613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5390596489250717539631075 8085894733876076309446613)
                ·
                  refine ⟨189513157825220538502655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8085894733876076309446613 189513157825220538502655)
                  ·
                    rfl

theorem cell21_830420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_830420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830420 prefixEnd_830420 := by exact prefixLift 830420
  have htrace : WordTrace (prefixWord ++ tailWord_830420) baseStart_830420 baseEnd_830420 := by
    simpa [prefixWord, tailWord_830420, baseEnd_830420] using wordTrace_append hprefix tailTrace_830420
  have hstable : (prefixWord ++ tailWord_830420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830420).length < 2 ^ (prefixWord ++ tailWord_830420).sum := by decide
  have hdescent : baseEnd_830420 < baseStart_830420 := by decide
  rcases family_descends (prefixWord ++ tailWord_830420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830454 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_830454 : Nat := 118140960795 + 830454 * 2 ^ 59
def prefixEnd_830454 : Nat := 4983230072969 + 3 ^ 40 * 830454 * 2
def baseEnd_830454 : Nat := 189520917088444034935919

theorem tailTrace_830454 : CollatzResearch.WordTrace tailWord_830454 prefixEnd_830454 189520917088444034935919 := by
  unfold tailWord_830454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893071608338403943539151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20192763822276308731084277 1893071608338403943539151)
  ·
    refine ⟨2839607412507605915308727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893071608338403943539151 2839607412507605915308727)
    ·
      refine ⟨4259411118761408872963091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2839607412507605915308727 4259411118761408872963091)
      ·
        refine ⟨6389116678142113309444637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4259411118761408872963091 6389116678142113309444637)
        ·
          refine ⟨2395918754303292491041739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6389116678142113309444637 2395918754303292491041739)
          ·
            refine ⟨3593878131454938736562609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2395918754303292491041739 3593878131454938736562609)
            ·
              refine ⟨2695408598591204052421957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3593878131454938736562609 2695408598591204052421957)
              ·
                refine ⟨505389112235850759829117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2695408598591204052421957 505389112235850759829117)
                ·
                  refine ⟨189520917088444034935919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505389112235850759829117 189520917088444034935919)
                  ·
                    rfl

theorem cell21_830454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_830454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830454 prefixEnd_830454 := by exact prefixLift 830454
  have htrace : WordTrace (prefixWord ++ tailWord_830454) baseStart_830454 baseEnd_830454 := by
    simpa [prefixWord, tailWord_830454, baseEnd_830454] using wordTrace_append hprefix tailTrace_830454
  have hstable : (prefixWord ++ tailWord_830454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830454).length < 2 ^ (prefixWord ++ tailWord_830454).sum := by decide
  have hdescent : baseEnd_830454 < baseStart_830454 := by decide
  rcases family_descends (prefixWord ++ tailWord_830454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830606 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 3]
def baseStart_830606 : Nat := 118140960795 + 830606 * 2 ^ 59
def prefixEnd_830606 : Nat := 4983230072969 + 3 ^ 40 * 830606 * 2
def baseEnd_830606 : Nat := 189555605559325548402275

theorem tailTrace_830606 : CollatzResearch.WordTrace tailWord_830606 prefixEnd_830606 189555605559325548402275 := by
  unfold tailWord_830606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786836203607974132019959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20196459752575862037439781 3786836203607974132019959)
  ·
    refine ⟨5680254305411961198029939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786836203607974132019959 5680254305411961198029939)
    ·
      refine ⟨8520381458117941797044909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680254305411961198029939 8520381458117941797044909)
      ·
        refine ⟨3195143046794228173891841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8520381458117941797044909 3195143046794228173891841)
        ·
          refine ⟨2396357285095671130418881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195143046794228173891841 2396357285095671130418881)
          ·
            refine ⟨1797267963821753347814161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396357285095671130418881 1797267963821753347814161)
            ·
              refine ⟨1347950972866315010860621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797267963821753347814161 1347950972866315010860621)
              ·
                refine ⟨505481614824868129072733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347950972866315010860621 505481614824868129072733)
                ·
                  refine ⟨189555605559325548402275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505481614824868129072733 189555605559325548402275)
                  ·
                    rfl

theorem cell21_830606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_830606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830606 prefixEnd_830606 := by exact prefixLift 830606
  have htrace : WordTrace (prefixWord ++ tailWord_830606) baseStart_830606 baseEnd_830606 := by
    simpa [prefixWord, tailWord_830606, baseEnd_830606] using wordTrace_append hprefix tailTrace_830606
  have hstable : (prefixWord ++ tailWord_830606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830606).length < 2 ^ (prefixWord ++ tailWord_830606).sum := by decide
  have hdescent : baseEnd_830606 < baseStart_830606 := by decide
  rcases family_descends (prefixWord ++ tailWord_830606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830620 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 4]
def baseStart_830620 : Nat := 118140960795 + 830620 * 2 ^ 59
def prefixEnd_830620 : Nat := 4983230072969 + 3 ^ 40 * 830620 * 2
def baseEnd_830620 : Nat := 189558800550064635168913

theorem tailTrace_830620 : CollatzResearch.WordTrace tailWord_830620 prefixEnd_830620 189558800550064635168913 := by
  unfold tailWord_830620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147600125406536723584657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20196800167208715631446209 15147600125406536723584657)
  ·
    refine ⟨11360700094054902542688493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15147600125406536723584657 11360700094054902542688493)
    ·
      refine ⟨4260262535270588453508185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11360700094054902542688493 4260262535270588453508185)
      ·
        refine ⟨3195196901452941340131139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4260262535270588453508185 3195196901452941340131139)
        ·
          refine ⟨4792795352179412010196709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195196901452941340131139 4792795352179412010196709)
          ·
            refine ⟨898649128533639751911883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4792795352179412010196709 898649128533639751911883)
            ·
              refine ⟨1347973692800459627867825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898649128533639751911883 1347973692800459627867825)
              ·
                refine ⟨1010980269600344720900869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1347973692800459627867825 1010980269600344720900869)
                ·
                  refine ⟨189558800550064635168913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1010980269600344720900869 189558800550064635168913)
                  ·
                    rfl

theorem cell21_830620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_830620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830620 prefixEnd_830620 := by exact prefixLift 830620
  have htrace : WordTrace (prefixWord ++ tailWord_830620) baseStart_830620 baseEnd_830620 := by
    simpa [prefixWord, tailWord_830620, baseEnd_830620] using wordTrace_append hprefix tailTrace_830620
  have hstable : (prefixWord ++ tailWord_830620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830620).length < 2 ^ (prefixWord ++ tailWord_830620).sum := by decide
  have hdescent : baseEnd_830620 < baseStart_830620 := by decide
  rcases family_descends (prefixWord ++ tailWord_830620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830637 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 4]
def baseStart_830637 : Nat := 118140960795 + 830637 * 2 ^ 59
def prefixEnd_830637 : Nat := 4983230072969 + 3 ^ 40 * 830637 * 2
def baseEnd_830637 : Nat := 189562680181676383385545

theorem tailTrace_830637 : CollatzResearch.WordTrace tailWord_830637 prefixEnd_830637 189562680181676383385545 := by
  unfold tailWord_830637
  simp only [CollatzResearch.WordTrace]
  refine ⟨30295820291751485350538165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197213527834323567025443 30295820291751485350538165)
  ·
    refine ⟨2840233152351701751612953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30295820291751485350538165 2840233152351701751612953)
    ·
      refine ⟨2130174864263776313709715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2840233152351701751612953 2130174864263776313709715)
      ·
        refine ⟨3195262296395664470564573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130174864263776313709715 3195262296395664470564573)
        ·
          refine ⟨1198223361148374176461715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3195262296395664470564573 1198223361148374176461715)
          ·
            refine ⟨1797335041722561264692573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198223361148374176461715 1797335041722561264692573)
            ·
              refine ⟨674000640645960474259715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797335041722561264692573 674000640645960474259715)
              ·
                refine ⟨1011000960968940711389573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674000640645960474259715 1011000960968940711389573)
                ·
                  refine ⟨189562680181676383385545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011000960968940711389573 189562680181676383385545)
                  ·
                    rfl

theorem cell21_830637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_830637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830637 prefixEnd_830637 := by exact prefixLift 830637
  have htrace : WordTrace (prefixWord ++ tailWord_830637) baseStart_830637 baseEnd_830637 := by
    simpa [prefixWord, tailWord_830637, baseEnd_830637] using wordTrace_append hprefix tailTrace_830637
  have hstable : (prefixWord ++ tailWord_830637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830637).length < 2 ^ (prefixWord ++ tailWord_830637).sum := by decide
  have hdescent : baseEnd_830637 < baseStart_830637 := by decide
  rcases family_descends (prefixWord ++ tailWord_830637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830800 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 3]
def baseStart_830800 : Nat := 118140960795 + 830800 * 2 ^ 59
def prefixEnd_830800 : Nat := 4983230072969 + 3 ^ 40 * 830800 * 2
def baseEnd_830800 : Nat := 189599879002424322168545

theorem tailTrace_830800 : CollatzResearch.WordTrace tailWord_830800 prefixEnd_830800 189599879002424322168545 := by
  unfold tailWord_830800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15150882695080482094360927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20201176926773976125814569 15150882695080482094360927)
  ·
    refine ⟨22726324042620723141541391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15150882695080482094360927 22726324042620723141541391)
    ·
      refine ⟨34089486063931084712312087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22726324042620723141541391 34089486063931084712312087)
      ·
        refine ⟨51134229095896627068468131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34089486063931084712312087 51134229095896627068468131)
        ·
          refine ⟨76701343643844940602702197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51134229095896627068468131 76701343643844940602702197)
          ·
            refine ⟨7190750966610463181503331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76701343643844940602702197 7190750966610463181503331)
            ·
              refine ⟨10786126449915694772254997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190750966610463181503331 10786126449915694772254997)
              ·
                refine ⟨505599677339798192449453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10786126449915694772254997 505599677339798192449453)
                ·
                  refine ⟨189599879002424322168545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505599677339798192449453 189599879002424322168545)
                  ·
                    rfl

theorem cell21_830800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 3].length) (baseStart_830800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830800 prefixEnd_830800 := by exact prefixLift 830800
  have htrace : WordTrace (prefixWord ++ tailWord_830800) baseStart_830800 baseEnd_830800 := by
    simpa [prefixWord, tailWord_830800, baseEnd_830800] using wordTrace_append hprefix tailTrace_830800
  have hstable : (prefixWord ++ tailWord_830800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830800).length < 2 ^ (prefixWord ++ tailWord_830800).sum := by decide
  have hdescent : baseEnd_830800 < baseStart_830800 := by decide
  rcases family_descends (prefixWord ++ tailWord_830800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830862 : List Nat := [4, 1, 1, 4, 2, 1, 2, 6]
def baseStart_830862 : Nat := 118140960795 + 830862 * 2 ^ 59
def prefixEnd_830862 : Nat := 4983230072969 + 3 ^ 40 * 830862 * 2
def baseEnd_830862 : Nat := 63204676082375330711695

theorem tailTrace_830862 : CollatzResearch.WordTrace tailWord_830862 prefixEnd_830862 63204676082375330711695 := by
  unfold tailWord_830862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788003339492043597184855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20202684477290899184985893 3788003339492043597184855)
  ·
    refine ⟨5682005009238065395777283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788003339492043597184855 5682005009238065395777283)
    ·
      refine ⟨8523007513857098093665925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682005009238065395777283 8523007513857098093665925)
      ·
        refine ⟨1598063908848205892562361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8523007513857098093665925 1598063908848205892562361)
        ·
          refine ⟨1198547931636154419421771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598063908848205892562361 1198547931636154419421771)
          ·
            refine ⟨1797821897454231629132657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198547931636154419421771 1797821897454231629132657)
            ·
              refine ⟨1348366423090673721849493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797821897454231629132657 1348366423090673721849493)
              ·
                refine ⟨63204676082375330711695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1348366423090673721849493 63204676082375330711695)
                ·
                  rfl

theorem cell21_830862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_830862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830862 prefixEnd_830862 := by exact prefixLift 830862
  have htrace : WordTrace (prefixWord ++ tailWord_830862) baseStart_830862 baseEnd_830862 := by
    simpa [prefixWord, tailWord_830862, baseEnd_830862] using wordTrace_append hprefix tailTrace_830862
  have hstable : (prefixWord ++ tailWord_830862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830862).length < 2 ^ (prefixWord ++ tailWord_830862).sum := by decide
  have hdescent : baseEnd_830862 < baseStart_830862 := by decide
  rcases family_descends (prefixWord ++ tailWord_830862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830989 : List Nat := [1, 7, 1, 1, 3, 1, 2, 5]
def baseStart_830989 : Nat := 118140960795 + 830989 * 2 ^ 59
def prefixEnd_830989 : Nat := 4983230072969 + 3 ^ 40 * 830989 * 2
def baseEnd_830989 : Nat := 63214337125800664506053

theorem tailTrace_830989 : CollatzResearch.WordTrace tailWord_830989 prefixEnd_830989 63214337125800664506053 := by
  unfold tailWord_830989
  simp only [CollatzResearch.WordTrace]
  refine ⟨30308658786476249467352021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20205772524317499644901347 30308658786476249467352021)
  ·
    refine ⟨710359190308037096891063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30308658786476249467352021 710359190308037096891063)
    ·
      refine ⟨1065538785462055645336595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710359190308037096891063 1065538785462055645336595)
      ·
        refine ⟨1598308178193083468004893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065538785462055645336595 1598308178193083468004893)
        ·
          refine ⟨599365566822406300501835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1598308178193083468004893 599365566822406300501835)
          ·
            refine ⟨899048350233609450752753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599365566822406300501835 899048350233609450752753)
            ·
              refine ⟨674286262675207088064565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899048350233609450752753 674286262675207088064565)
              ·
                refine ⟨63214337125800664506053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674286262675207088064565 63214337125800664506053)
                ·
                  rfl

theorem cell21_830989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 5].length) (baseStart_830989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830989 prefixEnd_830989 := by exact prefixLift 830989
  have htrace : WordTrace (prefixWord ++ tailWord_830989) baseStart_830989 baseEnd_830989 := by
    simpa [prefixWord, tailWord_830989, baseEnd_830989] using wordTrace_append hprefix tailTrace_830989
  have hstable : (prefixWord ++ tailWord_830989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830989).length < 2 ^ (prefixWord ++ tailWord_830989).sum := by decide
  have hdescent : baseEnd_830989 < baseStart_830989 := by decide
  rcases family_descends (prefixWord ++ tailWord_830989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830997 : List Nat := [1, 3, 2, 1, 3, 2, 4, 5]
def baseStart_830997 : Nat := 118140960795 + 830997 * 2 ^ 59
def prefixEnd_830997 : Nat := 4983230072969 + 3 ^ 40 * 830997 * 2
def baseEnd_830997 : Nat := 63214945695465252461603

theorem tailTrace_830997 : CollatzResearch.WordTrace tailWord_830997 prefixEnd_830997 63214945695465252461603 := by
  unfold tailWord_830997
  simp only [CollatzResearch.WordTrace]
  refine ⟨30308950570447266833643245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20205967046964844555762163 30308950570447266833643245)
  ·
    refine ⟨11365856463917725062616217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30308950570447266833643245 11365856463917725062616217)
    ·
      refine ⟨8524392347938293796962163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11365856463917725062616217 8524392347938293796962163)
      ·
        refine ⟨12786588521907440695443245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524392347938293796962163 12786588521907440695443245)
        ·
          refine ⟨4794970695715290260791217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12786588521907440695443245 4794970695715290260791217)
          ·
            refine ⟨3596228021786467695593413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4794970695715290260791217 3596228021786467695593413)
            ·
              refine ⟨674292754084962692923765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3596228021786467695593413 674292754084962692923765)
              ·
                refine ⟨63214945695465252461603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674292754084962692923765 63214945695465252461603)
                ·
                  rfl

theorem cell21_830997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 5].length) (baseStart_830997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_830997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_830997 prefixEnd_830997 := by exact prefixLift 830997
  have htrace : WordTrace (prefixWord ++ tailWord_830997) baseStart_830997 baseEnd_830997 := by
    simpa [prefixWord, tailWord_830997, baseEnd_830997] using wordTrace_append hprefix tailTrace_830997
  have hstable : (prefixWord ++ tailWord_830997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830997).length < 2 ^ (prefixWord ++ tailWord_830997).sum := by decide
  have hdescent : baseEnd_830997 < baseStart_830997 := by decide
  rcases family_descends (prefixWord ++ tailWord_830997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831135 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 6]
def baseStart_831135 : Nat := 118140960795 + 831135 * 2 ^ 59
def prefixEnd_831135 : Nat := 4983230072969 + 3 ^ 40 * 831135 * 2
def baseEnd_831135 : Nat := 189676330566538184084527

theorem tailTrace_831135 : CollatzResearch.WordTrace tailWord_831135 prefixEnd_831135 189676330566538184084527 := by
  unfold tailWord_831135
  simp only [CollatzResearch.WordTrace]
  refine ⟨30313983843947316402166859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20209322562631544268111239 30313983843947316402166859)
  ·
    refine ⟨45470975765920974603250289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30313983843947316402166859 45470975765920974603250289)
    ·
      refine ⟨34103231824440730952437717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45470975765920974603250289 34103231824440730952437717)
      ·
        refine ⟨799294495885329631697759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34103231824440730952437717 799294495885329631697759)
        ·
          refine ⟨1198941743827994447546639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799294495885329631697759 1198941743827994447546639)
          ·
            refine ⟨1798412615741991671319959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198941743827994447546639 1798412615741991671319959)
            ·
              refine ⟨2697618923612987506979939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798412615741991671319959 2697618923612987506979939)
              ·
                refine ⟨4046428385419481260469909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697618923612987506979939 4046428385419481260469909)
                ·
                  refine ⟨189676330566538184084527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4046428385419481260469909 189676330566538184084527)
                  ·
                    rfl

theorem cell21_831135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_831135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831135 prefixEnd_831135 := by exact prefixLift 831135
  have htrace : WordTrace (prefixWord ++ tailWord_831135) baseStart_831135 baseEnd_831135 := by
    simpa [prefixWord, tailWord_831135, baseEnd_831135] using wordTrace_append hprefix tailTrace_831135
  have hstable : (prefixWord ++ tailWord_831135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831135).length < 2 ^ (prefixWord ++ tailWord_831135).sum := by decide
  have hdescent : baseEnd_831135 < baseStart_831135 := by decide
  rcases family_descends (prefixWord ++ tailWord_831135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831166 : List Nat := [4, 2, 1, 1, 2, 4, 2, 5]
def baseStart_831166 : Nat := 118140960795 + 831166 * 2 ^ 59
def prefixEnd_831166 : Nat := 4983230072969 + 3 ^ 40 * 831166 * 2
def baseEnd_831166 : Nat := 63227801729629673022599

theorem tailTrace_831166 : CollatzResearch.WordTrace tailWord_831166 prefixEnd_831166 63227801729629673022599 := by
  unfold tailWord_831166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789389313354376087068169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20210076337890005797696901 3789389313354376087068169)
  ·
    refine ⟨2842041985015782065301127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3789389313354376087068169 2842041985015782065301127)
    ·
      refine ⟨4263062977523673097951691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2842041985015782065301127 4263062977523673097951691)
      ·
        refine ⟨6394594466285509646927537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263062977523673097951691 6394594466285509646927537)
        ·
          refine ⟨4795945849714132235195653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6394594466285509646927537 4795945849714132235195653)
          ·
            refine ⟨899239846821399794099185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4795945849714132235195653 899239846821399794099185)
            ·
              refine ⟨674429885116049845574389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899239846821399794099185 674429885116049845574389)
              ·
                refine ⟨63227801729629673022599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 674429885116049845574389 63227801729629673022599)
                ·
                  rfl

theorem cell21_831166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_831166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831166 prefixEnd_831166 := by exact prefixLift 831166
  have htrace : WordTrace (prefixWord ++ tailWord_831166) baseStart_831166 baseEnd_831166 := by
    simpa [prefixWord, tailWord_831166, baseEnd_831166] using wordTrace_append hprefix tailTrace_831166
  have hstable : (prefixWord ++ tailWord_831166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831166).length < 2 ^ (prefixWord ++ tailWord_831166).sum := by decide
  have hdescent : baseEnd_831166 < baseStart_831166 := by decide
  rcases family_descends (prefixWord ++ tailWord_831166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831208 : List Nat := [2, 1, 4, 1, 3, 1, 1, 8]
def baseStart_831208 : Nat := 118140960795 + 831208 * 2 ^ 59
def prefixEnd_831208 : Nat := 4983230072969 + 3 ^ 40 * 831208 * 2
def baseEnd_831208 : Nat := 63230996720368759789237

theorem tailTrace_831208 : CollatzResearch.WordTrace tailWord_831208 prefixEnd_831208 63230996720368759789237 := by
  unfold tailWord_831208
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158323186341424934787139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20211097581788566579716185 15158323186341424934787139)
  ·
    refine ⟨22737484779512137402180709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15158323186341424934787139 22737484779512137402180709)
    ·
      refine ⟨4263278396158525762908883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22737484779512137402180709 4263278396158525762908883)
      ·
        refine ⟨6394917594237788644363325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4263278396158525762908883 6394917594237788644363325)
        ·
          refine ⟨2398094097839170741636247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6394917594237788644363325 2398094097839170741636247)
          ·
            refine ⟨3597141146758756112454371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398094097839170741636247 3597141146758756112454371)
            ·
              refine ⟨5395711720138134168681557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3597141146758756112454371 5395711720138134168681557)
              ·
                refine ⟨63230996720368759789237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5395711720138134168681557 63230996720368759789237)
                ·
                  rfl

theorem cell21_831208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_831208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831208 prefixEnd_831208 := by exact prefixLift 831208
  have htrace : WordTrace (prefixWord ++ tailWord_831208) baseStart_831208 baseEnd_831208 := by
    simpa [prefixWord, tailWord_831208, baseEnd_831208] using wordTrace_append hprefix tailTrace_831208
  have hstable : (prefixWord ++ tailWord_831208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831208).length < 2 ^ (prefixWord ++ tailWord_831208).sum := by decide
  have hdescent : baseEnd_831208 < baseStart_831208 := by decide
  rcases family_descends (prefixWord ++ tailWord_831208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831380 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_831380 : Nat := 118140960795 + 831380 * 2 ^ 59
def prefixEnd_831380 : Nat := 4983230072969 + 3 ^ 40 * 831380 * 2
def baseEnd_831380 : Nat := 189732242904472202500693

theorem tailTrace_831380 : CollatzResearch.WordTrace tailWord_831380 prefixEnd_831380 189732242904472202500693 := by
  unfold tailWord_831380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15161459864029861622417797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20215279818706482163223729 15161459864029861622417797)
  ·
    refine ⟨2842773724505599054203337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15161459864029861622417797 2842773724505599054203337)
    ·
      refine ⟨2132080293379199290652503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2842773724505599054203337 2132080293379199290652503)
      ·
        refine ⟨3198120440068798935978755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132080293379199290652503 3198120440068798935978755)
        ·
          refine ⟨4797180660103198403968133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198120440068798935978755 4797180660103198403968133)
          ·
            refine ⟨899471373769349700744025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4797180660103198403968133 899471373769349700744025)
            ·
              refine ⟨674603530327012275558019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899471373769349700744025 674603530327012275558019)
              ·
                refine ⟨1011905295490518413337029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674603530327012275558019 1011905295490518413337029)
                ·
                  refine ⟨189732242904472202500693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011905295490518413337029 189732242904472202500693)
                  ·
                    rfl

theorem cell21_831380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_831380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831380 prefixEnd_831380 := by exact prefixLift 831380
  have htrace : WordTrace (prefixWord ++ tailWord_831380) baseStart_831380 baseEnd_831380 := by
    simpa [prefixWord, tailWord_831380, baseEnd_831380] using wordTrace_append hprefix tailTrace_831380
  have hstable : (prefixWord ++ tailWord_831380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831380).length < 2 ^ (prefixWord ++ tailWord_831380).sum := by decide
  have hdescent : baseEnd_831380 < baseStart_831380 := by decide
  rcases family_descends (prefixWord ++ tailWord_831380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831422 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_831422 : Nat := 118140960795 + 831422 * 2 ^ 59
def prefixEnd_831422 : Nat := 4983230072969 + 3 ^ 40 * 831422 * 2
def baseEnd_831422 : Nat := 189741827876689462800607

theorem tailTrace_831422 : CollatzResearch.WordTrace tailWord_831422 prefixEnd_831422 189741827876689462800607 := by
  unfold tailWord_831422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790556449238445552233065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20216301062605042945243013 3790556449238445552233065)
  ·
    refine ⟨2842917336928834164174799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3790556449238445552233065 2842917336928834164174799)
    ·
      refine ⟨4264376005393251246262199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2842917336928834164174799 4264376005393251246262199)
      ·
        refine ⟨6396564008089876869393299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264376005393251246262199 6396564008089876869393299)
        ·
          refine ⟨9594846012134815304089949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6396564008089876869393299 9594846012134815304089949)
          ·
            refine ⟨3598067254550555739033731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9594846012134815304089949 3598067254550555739033731)
            ·
              refine ⟨5397100881825833608550597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598067254550555739033731 5397100881825833608550597)
              ·
                refine ⟨1011956415342343801603237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5397100881825833608550597 1011956415342343801603237)
                ·
                  refine ⟨189741827876689462800607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1011956415342343801603237 189741827876689462800607)
                  ·
                    rfl

theorem cell21_831422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_831422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831422 prefixEnd_831422 := by exact prefixLift 831422
  have htrace : WordTrace (prefixWord ++ tailWord_831422) baseStart_831422 baseEnd_831422 := by
    simpa [prefixWord, tailWord_831422, baseEnd_831422] using wordTrace_append hprefix tailTrace_831422
  have hstable : (prefixWord ++ tailWord_831422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831422).length < 2 ^ (prefixWord ++ tailWord_831422).sum := by decide
  have hdescent : baseEnd_831422 < baseStart_831422 := by decide
  rcases family_descends (prefixWord ++ tailWord_831422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831436 : List Nat := [2, 2, 1, 4, 1, 2, 3, 6]
def baseStart_831436 : Nat := 118140960795 + 831436 * 2 ^ 59
def prefixEnd_831436 : Nat := 4983230072969 + 3 ^ 40 * 831436 * 2
def baseEnd_831436 : Nat := 63248340955809516522415

theorem tailTrace_831436 : CollatzResearch.WordTrace tailWord_831436 prefixEnd_831436 63248340955809516522415 := by
  unfold tailWord_831436
  simp only [CollatzResearch.WordTrace]
  refine ⟨15162481107928422404437081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20216641477237896539249441 15162481107928422404437081)
  ·
    refine ⟨11371860830946316803327811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15162481107928422404437081 11371860830946316803327811)
    ·
      refine ⟨17057791246419475204991717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11371860830946316803327811 17057791246419475204991717)
      ·
        refine ⟨3198335858703651600935947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17057791246419475204991717 3198335858703651600935947)
        ·
          refine ⟨4797503788055477401403921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198335858703651600935947 4797503788055477401403921)
          ·
            refine ⟨3598127841041608051052941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4797503788055477401403921 3598127841041608051052941)
            ·
              refine ⟨1349297940390603019144853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3598127841041608051052941 1349297940390603019144853)
              ·
                refine ⟨63248340955809516522415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1349297940390603019144853 63248340955809516522415)
                ·
                  rfl

theorem cell21_831436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 6].length) (baseStart_831436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831436 prefixEnd_831436 := by exact prefixLift 831436
  have htrace : WordTrace (prefixWord ++ tailWord_831436) baseStart_831436 baseEnd_831436 := by
    simpa [prefixWord, tailWord_831436, baseEnd_831436] using wordTrace_append hprefix tailTrace_831436
  have hstable : (prefixWord ++ tailWord_831436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831436).length < 2 ^ (prefixWord ++ tailWord_831436).sum := by decide
  have hdescent : baseEnd_831436 < baseStart_831436 := by decide
  rcases family_descends (prefixWord ++ tailWord_831436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831481 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 6]
def baseStart_831481 : Nat := 118140960795 + 831481 * 2 ^ 59
def prefixEnd_831481 : Nat := 4983230072969 + 3 ^ 40 * 831481 * 2
def baseEnd_831481 : Nat := 189755292480518471317153

theorem tailTrace_831481 : CollatzResearch.WordTrace tailWord_831481 prefixEnd_831481 189755292480518471317153 := by
  unfold tailWord_831481
  simp only [CollatzResearch.WordTrace]
  refine ⟨30326603500693817494262297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20217735667129211662841531 30326603500693817494262297)
  ·
    refine ⟨22744952625520363120696723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30326603500693817494262297 22744952625520363120696723)
    ·
      refine ⟨34117428938280544681045085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22744952625520363120696723 34117428938280544681045085)
      ·
        refine ⟨12794035851855204255391907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34117428938280544681045085 12794035851855204255391907)
        ·
          refine ⟨19191053777782806383087861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12794035851855204255391907 19191053777782806383087861)
          ·
            refine ⟨1799161291667138098414487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19191053777782806383087861 1799161291667138098414487)
            ·
              refine ⟨2698741937500707147621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799161291667138098414487 2698741937500707147621731)
              ·
                refine ⟨4048112906251060721432597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698741937500707147621731 4048112906251060721432597)
                ·
                  refine ⟨189755292480518471317153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4048112906251060721432597 189755292480518471317153)
                  ·
                    rfl

theorem cell21_831481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_831481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831481 prefixEnd_831481 := by exact prefixLift 831481
  have htrace : WordTrace (prefixWord ++ tailWord_831481) baseStart_831481 baseEnd_831481 := by
    simpa [prefixWord, tailWord_831481, baseEnd_831481] using wordTrace_append hprefix tailTrace_831481
  have hstable : (prefixWord ++ tailWord_831481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831481).length < 2 ^ (prefixWord ++ tailWord_831481).sum := by decide
  have hdescent : baseEnd_831481 < baseStart_831481 := by decide
  rcases family_descends (prefixWord ++ tailWord_831481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831543 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 3]
def baseStart_831543 : Nat := 118140960795 + 831543 * 2 ^ 59
def prefixEnd_831543 : Nat := 4983230072969 + 3 ^ 40 * 831543 * 2
def baseEnd_831543 : Nat := 189769441725220141283693

theorem tailTrace_831543 : CollatzResearch.WordTrace tailWord_831543 prefixEnd_831543 189769441725220141283693 := by
  unfold tailWord_831543
  simp only [CollatzResearch.WordTrace]
  refine ⟨30328864826469202083019283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20219243217646134722012855 30328864826469202083019283)
  ·
    refine ⟨45493297239703803124528925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30328864826469202083019283 45493297239703803124528925)
    ·
      refine ⟨17059986464888926171698347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45493297239703803124528925 17059986464888926171698347)
      ·
        refine ⟨25589979697333389257547521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17059986464888926171698347 25589979697333389257547521)
        ·
          refine ⟨19192484773000041943160641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25589979697333389257547521 19192484773000041943160641)
          ·
            refine ⟨14394363579750031457370481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19192484773000041943160641 14394363579750031457370481)
            ·
              refine ⟨10795772684812523593027861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14394363579750031457370481 10795772684812523593027861)
              ·
                refine ⟨506051844600587043423181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10795772684812523593027861 506051844600587043423181)
                ·
                  refine ⟨189769441725220141283693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506051844600587043423181 189769441725220141283693)
                  ·
                    rfl

theorem cell21_831543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3].length) (baseStart_831543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831543 prefixEnd_831543 := by exact prefixLift 831543
  have htrace : WordTrace (prefixWord ++ tailWord_831543) baseStart_831543 baseEnd_831543 := by
    simpa [prefixWord, tailWord_831543, baseEnd_831543] using wordTrace_append hprefix tailTrace_831543
  have hstable : (prefixWord ++ tailWord_831543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831543).length < 2 ^ (prefixWord ++ tailWord_831543).sum := by decide
  have hdescent : baseEnd_831543 < baseStart_831543 := by decide
  rcases family_descends (prefixWord ++ tailWord_831543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831594 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_831594 : Nat := 118140960795 + 831594 * 2 ^ 59
def prefixEnd_831594 : Nat := 4983230072969 + 3 ^ 40 * 831594 * 2
def baseEnd_831594 : Nat := 189781080620055385933589

theorem tailTrace_831594 : CollatzResearch.WordTrace tailWord_831594 prefixEnd_831594 189781080620055385933589 := by
  unfold tailWord_831594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582681237321109448281459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20220483299522958528750557 7582681237321109448281459)
  ·
    refine ⟨11374021855981664172422189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7582681237321109448281459 11374021855981664172422189)
    ·
      refine ⟨4265258195993124064658321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11374021855981664172422189 4265258195993124064658321)
      ·
        refine ⟨3198943646994843048493741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265258195993124064658321 3198943646994843048493741)
        ·
          refine ⟨1199603867623066143185153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3198943646994843048493741 1199603867623066143185153)
          ·
            refine ⟨899702900717299607388865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1199603867623066143185153 899702900717299607388865)
            ·
              refine ⟨674777175537974705541649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899702900717299607388865 674777175537974705541649)
              ·
                refine ⟨506082881653481029156237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674777175537974705541649 506082881653481029156237)
                ·
                  refine ⟨189781080620055385933589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506082881653481029156237 189781080620055385933589)
                  ·
                    rfl

theorem cell21_831594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_831594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831594 prefixEnd_831594 := by exact prefixLift 831594
  have htrace : WordTrace (prefixWord ++ tailWord_831594) baseStart_831594 baseEnd_831594 := by
    simpa [prefixWord, tailWord_831594, baseEnd_831594] using wordTrace_append hprefix tailTrace_831594
  have hstable : (prefixWord ++ tailWord_831594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831594).length < 2 ^ (prefixWord ++ tailWord_831594).sum := by decide
  have hdescent : baseEnd_831594 < baseStart_831594 := by decide
  rcases family_descends (prefixWord ++ tailWord_831594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831616 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_831616 : Nat := 118140960795 + 831616 * 2 ^ 59
def prefixEnd_831616 : Nat := 4983230072969 + 3 ^ 40 * 831616 * 2
def baseEnd_831616 : Nat := 189786101319788236566877

theorem tailTrace_831616 : CollatzResearch.WordTrace tailWord_831616 prefixEnd_831616 189786101319788236566877 := by
  unfold tailWord_831616
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165763677602367775213351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20221018236803157033617801 15165763677602367775213351)
  ·
    refine ⟨22748645516403551662820027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15165763677602367775213351 22748645516403551662820027)
    ·
      refine ⟨34122968274605327494230041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22748645516403551662820027 34122968274605327494230041)
      ·
        refine ⟨25592226205953995620672531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34122968274605327494230041 25592226205953995620672531)
        ·
          refine ⟨38388339308930993431008797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25592226205953995620672531 38388339308930993431008797)
          ·
            refine ⟨14395627240849122536628299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38388339308930993431008797 14395627240849122536628299)
            ·
              refine ⟨21593440861273683804942449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14395627240849122536628299 21593440861273683804942449)
              ·
                refine ⟨16195080645955262853706837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21593440861273683804942449 16195080645955262853706837)
                ·
                  refine ⟨189786101319788236566877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16195080645955262853706837 189786101319788236566877)
                  ·
                    rfl

theorem cell21_831616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_831616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831616 prefixEnd_831616 := by exact prefixLift 831616
  have htrace : WordTrace (prefixWord ++ tailWord_831616) baseStart_831616 baseEnd_831616 := by
    simpa [prefixWord, tailWord_831616, baseEnd_831616] using wordTrace_append hprefix tailTrace_831616
  have hstable : (prefixWord ++ tailWord_831616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831616).length < 2 ^ (prefixWord ++ tailWord_831616).sum := by decide
  have hdescent : baseEnd_831616 < baseStart_831616 := by decide
  rcases family_descends (prefixWord ++ tailWord_831616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831650 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_831650 : Nat := 118140960795 + 831650 * 2 ^ 59
def prefixEnd_831650 : Nat := 4983230072969 + 3 ^ 40 * 831650 * 2
def baseEnd_831650 : Nat := 189793860583011733000141

theorem tailTrace_831650 : CollatzResearch.WordTrace tailWord_831650 prefixEnd_831650 189793860583011733000141 := by
  unfold tailWord_831650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583191859270389839291101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20221844958054372904776269 7583191859270389839291101)
  ·
    refine ⟨2843696947226396189734163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7583191859270389839291101 2843696947226396189734163)
    ·
      refine ⟨4265545420839594284601245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843696947226396189734163 4265545420839594284601245)
      ·
        refine ⟨1599579532814847856725467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4265545420839594284601245 1599579532814847856725467)
        ·
          refine ⟨2399369299222271785088201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599579532814847856725467 2399369299222271785088201)
          ·
            refine ⟨1799526974416703838816151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399369299222271785088201 1799526974416703838816151)
            ·
              refine ⟨2699290461625055758224227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799526974416703838816151 2699290461625055758224227)
              ·
                refine ⟨4048935692437583637336341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699290461625055758224227 4048935692437583637336341)
                ·
                  refine ⟨189793860583011733000141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4048935692437583637336341 189793860583011733000141)
                  ·
                    rfl

theorem cell21_831650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_831650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831650 prefixEnd_831650 := by exact prefixLift 831650
  have htrace : WordTrace (prefixWord ++ tailWord_831650) baseStart_831650 baseEnd_831650 := by
    simpa [prefixWord, tailWord_831650, baseEnd_831650] using wordTrace_append hprefix tailTrace_831650
  have hstable : (prefixWord ++ tailWord_831650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831650).length < 2 ^ (prefixWord ++ tailWord_831650).sum := by decide
  have hdescent : baseEnd_831650 < baseStart_831650 := by decide
  rcases family_descends (prefixWord ++ tailWord_831650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831681 : List Nat := [1, 2, 6, 1, 2, 1, 1, 7]
def baseStart_831681 : Nat := 118140960795 + 831681 * 2 ^ 59
def prefixEnd_831681 : Nat := 4983230072969 + 3 ^ 40 * 831681 * 2
def baseEnd_831681 : Nat := 63266978401787522661137

theorem tailTrace_831681 : CollatzResearch.WordTrace tailWord_831681 prefixEnd_831681 63266978401787522661137 := by
  unfold tailWord_831681
  simp only [CollatzResearch.WordTrace]
  refine ⟨30333898099969251651542897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20222598733312834434361931 30333898099969251651542897)
  ·
    refine ⟨22750423574976938738657173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30333898099969251651542897 22750423574976938738657173)
    ·
      refine ⟨1066426105077044003374555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22750423574976938738657173 1066426105077044003374555)
      ·
        refine ⟨1599639157615566005061833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066426105077044003374555 1599639157615566005061833)
        ·
          refine ⟨1199729368211674503796375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1599639157615566005061833 1199729368211674503796375)
          ·
            refine ⟨1799594052317511755694563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199729368211674503796375 1799594052317511755694563)
            ·
              refine ⟨2699391078476267633541845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799594052317511755694563 2699391078476267633541845)
              ·
                refine ⟨63266978401787522661137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2699391078476267633541845 63266978401787522661137)
                ·
                  rfl

theorem cell21_831681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_831681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831681 prefixEnd_831681 := by exact prefixLift 831681
  have htrace : WordTrace (prefixWord ++ tailWord_831681) baseStart_831681 baseEnd_831681 := by
    simpa [prefixWord, tailWord_831681, baseEnd_831681] using wordTrace_append hprefix tailTrace_831681
  have hstable : (prefixWord ++ tailWord_831681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831681).length < 2 ^ (prefixWord ++ tailWord_831681).sum := by decide
  have hdescent : baseEnd_831681 < baseStart_831681 := by decide
  rcases family_descends (prefixWord ++ tailWord_831681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831712 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 3]
def baseStart_831712 : Nat := 118140960795 + 831712 * 2 ^ 59
def prefixEnd_831712 : Nat := 4983230072969 + 3 ^ 40 * 831712 * 2
def baseEnd_831712 : Nat := 189808009827713402966681

theorem tailTrace_831712 : CollatzResearch.WordTrace tailWord_831712 prefixEnd_831712 189808009827713402966681 := by
  unfold tailWord_831712
  simp only [CollatzResearch.WordTrace]
  refine ⟨15167514381428471972960695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20223352508571295963947593 15167514381428471972960695)
  ·
    refine ⟨22751271572142707959441043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15167514381428471972960695 22751271572142707959441043)
    ·
      refine ⟨34126907358214061939161565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22751271572142707959441043 34126907358214061939161565)
      ·
        refine ⟨12797590259330273227185587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34126907358214061939161565 12797590259330273227185587)
        ·
          refine ⟨19196385388995409840778381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12797590259330273227185587 19196385388995409840778381)
          ·
            refine ⟨7198644520873278690291893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19196385388995409840778381 7198644520873278690291893)
            ·
              refine ⟨674872923831869877214865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7198644520873278690291893 674872923831869877214865)
              ·
                refine ⟨506154692873902407911149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674872923831869877214865 506154692873902407911149)
                ·
                  refine ⟨189808009827713402966681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506154692873902407911149 189808009827713402966681)
                  ·
                    rfl

theorem cell21_831712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 3].length) (baseStart_831712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831712 prefixEnd_831712 := by exact prefixLift 831712
  have htrace : WordTrace (prefixWord ++ tailWord_831712) baseStart_831712 baseEnd_831712 := by
    simpa [prefixWord, tailWord_831712, baseEnd_831712] using wordTrace_append hprefix tailTrace_831712
  have hstable : (prefixWord ++ tailWord_831712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831712).length < 2 ^ (prefixWord ++ tailWord_831712).sum := by decide
  have hdescent : baseEnd_831712 < baseStart_831712 := by decide
  rcases family_descends (prefixWord ++ tailWord_831712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831723 : List Nat := [1, 1, 1, 1, 2, 5, 4, 6]
def baseStart_831723 : Nat := 118140960795 + 831723 * 2 ^ 59
def prefixEnd_831723 : Nat := 4983230072969 + 3 ^ 40 * 831723 * 2
def baseEnd_831723 : Nat := 63270173392526609427775

theorem tailTrace_831723 : CollatzResearch.WordTrace tailWord_831723 prefixEnd_831723 63270173392526609427775 := by
  unfold tailWord_831723
  simp only [CollatzResearch.WordTrace]
  refine ⟨30335429965817092824571823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20223619977211395216381215 30335429965817092824571823)
  ·
    refine ⟨45503144948725639236857735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30335429965817092824571823 45503144948725639236857735)
    ·
      refine ⟨68254717423088458855286603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45503144948725639236857735 68254717423088458855286603)
      ·
        refine ⟨102382076134632688282929905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68254717423088458855286603 102382076134632688282929905)
        ·
          refine ⟨76786557100974516212197429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102382076134632688282929905 76786557100974516212197429)
          ·
            refine ⟨7198739728216360894893509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76786557100974516212197429 7198739728216360894893509)
            ·
              refine ⟨1349763699040567667792533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7198739728216360894893509 1349763699040567667792533)
              ·
                refine ⟨63270173392526609427775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1349763699040567667792533 63270173392526609427775)
                ·
                  rfl

theorem cell21_831723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_831723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831723 prefixEnd_831723 := by exact prefixLift 831723
  have htrace : WordTrace (prefixWord ++ tailWord_831723) baseStart_831723 baseEnd_831723 := by
    simpa [prefixWord, tailWord_831723, baseEnd_831723] using wordTrace_append hprefix tailTrace_831723
  have hstable : (prefixWord ++ tailWord_831723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831723).length < 2 ^ (prefixWord ++ tailWord_831723).sum := by decide
  have hdescent : baseEnd_831723 < baseStart_831723 := by decide
  rcases family_descends (prefixWord ++ tailWord_831723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831774 : List Nat := [4, 3, 2, 1, 1, 3, 1, 6]
def baseStart_831774 : Nat := 118140960795 + 831774 * 2 ^ 59
def prefixEnd_831774 : Nat := 4983230072969 + 3 ^ 40 * 831774 * 2
def baseEnd_831774 : Nat := 63274053024138357644407

theorem tailTrace_831774 : CollatzResearch.WordTrace tailWord_831774 prefixEnd_831774 63274053024138357644407 := by
  unfold tailWord_831774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3792161261079041066834797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20224860059088219023118917 3792161261079041066834797)
  ·
    refine ⟨1422060472904640400063049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3792161261079041066834797 1422060472904640400063049)
    ·
      refine ⟨1066545354678480300047287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1422060472904640400063049 1066545354678480300047287)
      ·
        refine ⟨1599818032017720450070931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1066545354678480300047287 1599818032017720450070931)
        ·
          refine ⟨2399727048026580675106397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599818032017720450070931 2399727048026580675106397)
          ·
            refine ⟨899897643009967753164899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2399727048026580675106397 899897643009967753164899)
            ·
              refine ⟨1349846464514951629747349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899897643009967753164899 1349846464514951629747349)
              ·
                refine ⟨63274053024138357644407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1349846464514951629747349 63274053024138357644407)
                ·
                  rfl

theorem cell21_831774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_831774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831774 prefixEnd_831774 := by exact prefixLift 831774
  have htrace : WordTrace (prefixWord ++ tailWord_831774) baseStart_831774 baseEnd_831774 := by
    simpa [prefixWord, tailWord_831774, baseEnd_831774] using wordTrace_append hprefix tailTrace_831774
  have hstable : (prefixWord ++ tailWord_831774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831774).length < 2 ^ (prefixWord ++ tailWord_831774).sum := by decide
  have hdescent : baseEnd_831774 < baseStart_831774 := by decide
  rcases family_descends (prefixWord ++ tailWord_831774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831836 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_831836 : Nat := 118140960795 + 831836 * 2 ^ 59
def prefixEnd_831836 : Nat := 4983230072969 + 3 ^ 40 * 831836 * 2
def baseEnd_831836 : Nat := 189836308317116742899761

theorem tailTrace_831836 : CollatzResearch.WordTrace tailWord_831836 prefixEnd_831836 189836308317116742899761 := by
  unfold tailWord_831836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15169775707203856561717681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20226367609605142082290241 15169775707203856561717681)
  ·
    refine ⟨11377331780402892421288261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15169775707203856561717681 11377331780402892421288261)
    ·
      refine ⟨2133249708825542328991549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11377331780402892421288261 2133249708825542328991549)
      ·
        refine ⟨799968640809578373371831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2133249708825542328991549 799968640809578373371831)
        ·
          refine ⟨1199952961214367560057747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799968640809578373371831 1199952961214367560057747)
          ·
            refine ⟨1799929441821551340086621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199952961214367560057747 1799929441821551340086621)
            ·
              refine ⟨674973540683081752532483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1799929441821551340086621 674973540683081752532483)
              ·
                refine ⟨1012460311024622628798725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674973540683081752532483 1012460311024622628798725)
                ·
                  refine ⟨189836308317116742899761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012460311024622628798725 189836308317116742899761)
                  ·
                    rfl

theorem cell21_831836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_831836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831836 prefixEnd_831836 := by exact prefixLift 831836
  have htrace : WordTrace (prefixWord ++ tailWord_831836) baseStart_831836 baseEnd_831836 := by
    simpa [prefixWord, tailWord_831836, baseEnd_831836] using wordTrace_append hprefix tailTrace_831836
  have hstable : (prefixWord ++ tailWord_831836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831836).length < 2 ^ (prefixWord ++ tailWord_831836).sum := by decide
  have hdescent : baseEnd_831836 < baseStart_831836 := by decide
  rcases family_descends (prefixWord ++ tailWord_831836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831861 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_831861 : Nat := 118140960795 + 831861 * 2 ^ 59
def prefixEnd_831861 : Nat := 4983230072969 + 3 ^ 40 * 831861 * 2
def baseEnd_831861 : Nat := 189842013657722254983043

theorem tailTrace_831861 : CollatzResearch.WordTrace tailWord_831861 prefixEnd_831861 189842013657722254983043 := by
  unfold tailWord_831861
  simp only [CollatzResearch.WordTrace]
  refine ⟨30340463239317142393095437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20226975492878094928730291 30340463239317142393095437)
  ·
    refine ⟨11377673714743928397410789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30340463239317142393095437 11377673714743928397410789)
    ·
      refine ⟨2133313821514486574514523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11377673714743928397410789 2133313821514486574514523)
      ·
        refine ⟨3199970732271729861771785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133313821514486574514523 3199970732271729861771785)
        ·
          refine ⟨2399978049203797396328839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3199970732271729861771785 2399978049203797396328839)
          ·
            refine ⟨3599967073805696094493259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399978049203797396328839 3599967073805696094493259)
            ·
              refine ⟨5399950610708544141739889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3599967073805696094493259 5399950610708544141739889)
              ·
                refine ⟨4049962958031408106304917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5399950610708544141739889 4049962958031408106304917)
                ·
                  refine ⟨189842013657722254983043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4049962958031408106304917 189842013657722254983043)
                  ·
                    rfl

theorem cell21_831861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_831861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831861 prefixEnd_831861 := by exact prefixLift 831861
  have htrace : WordTrace (prefixWord ++ tailWord_831861) baseStart_831861 baseEnd_831861 := by
    simpa [prefixWord, tailWord_831861, baseEnd_831861] using wordTrace_append hprefix tailTrace_831861
  have hstable : (prefixWord ++ tailWord_831861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831861).length < 2 ^ (prefixWord ++ tailWord_831861).sum := by decide
  have hdescent : baseEnd_831861 < baseStart_831861 := by decide
  rcases family_descends (prefixWord ++ tailWord_831861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831906 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_831906 : Nat := 118140960795 + 831906 * 2 ^ 59
def prefixEnd_831906 : Nat := 4983230072969 + 3 ^ 40 * 831906 * 2
def baseEnd_831906 : Nat := 189852283270812176732951

theorem tailTrace_831906 : CollatzResearch.WordTrace tailWord_831906 prefixEnd_831906 189852283270812176732951 := by
  unfold tailWord_831906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585526131038528769620893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20228069682769410052322381 7585526131038528769620893)
  ·
    refine ⟨2844572299139448288607835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7585526131038528769620893 2844572299139448288607835)
    ·
      refine ⟨4266858448709172432911753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844572299139448288607835 4266858448709172432911753)
      ·
        refine ⟨3200143836531879324683815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4266858448709172432911753 3200143836531879324683815)
        ·
          refine ⟨4800215754797818987025723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200143836531879324683815 4800215754797818987025723)
          ·
            refine ⟨7200323632196728480538585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800215754797818987025723 7200323632196728480538585)
            ·
              refine ⟨5400242724147546360403939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200323632196728480538585 5400242724147546360403939)
              ·
                refine ⟨8100364086221319540605909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400242724147546360403939 8100364086221319540605909)
                ·
                  refine ⟨189852283270812176732951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8100364086221319540605909 189852283270812176732951)
                  ·
                    rfl

theorem cell21_831906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_831906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_831906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_831906 prefixEnd_831906 := by exact prefixLift 831906
  have htrace : WordTrace (prefixWord ++ tailWord_831906) baseStart_831906 baseEnd_831906 := by
    simpa [prefixWord, tailWord_831906, baseEnd_831906] using wordTrace_append hprefix tailTrace_831906
  have hstable : (prefixWord ++ tailWord_831906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831906).length < 2 ^ (prefixWord ++ tailWord_831906).sum := by decide
  have hdescent : baseEnd_831906 < baseStart_831906 := by decide
  rcases family_descends (prefixWord ++ tailWord_831906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832058 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_832058 : Nat := 118140960795 + 832058 * 2 ^ 59
def prefixEnd_832058 : Nat := 4983230072969 + 3 ^ 40 * 832058 * 2
def baseEnd_832058 : Nat := 189886971741693690199307

theorem tailTrace_832058 : CollatzResearch.WordTrace tailWord_832058 prefixEnd_832058 189886971741693690199307 := by
  unfold tailWord_832058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586912104900861259504207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20231765613068963358677885 7586912104900861259504207)
  ·
    refine ⟨11380368157351291889256311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7586912104900861259504207 11380368157351291889256311)
    ·
      refine ⟨17070552236026937833884467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380368157351291889256311 17070552236026937833884467)
      ·
        refine ⟨25605828354040406750826701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070552236026937833884467 25605828354040406750826701)
        ·
          refine ⟨9602185632765152531560013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25605828354040406750826701 9602185632765152531560013)
          ·
            refine ⟨3600819612286932199335005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9602185632765152531560013 3600819612286932199335005)
            ·
              refine ⟨1350307354607599574750627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3600819612286932199335005 1350307354607599574750627)
              ·
                refine ⟨2025461031911399362125941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350307354607599574750627 2025461031911399362125941)
                ·
                  refine ⟨189886971741693690199307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025461031911399362125941 189886971741693690199307)
                  ·
                    rfl

theorem cell21_832058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_832058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832058 prefixEnd_832058 := by exact prefixLift 832058
  have htrace : WordTrace (prefixWord ++ tailWord_832058) baseStart_832058 baseEnd_832058 := by
    simpa [prefixWord, tailWord_832058, baseEnd_832058] using wordTrace_append hprefix tailTrace_832058
  have hstable : (prefixWord ++ tailWord_832058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832058).length < 2 ^ (prefixWord ++ tailWord_832058).sum := by decide
  have hdescent : baseEnd_832058 < baseStart_832058 := by decide
  rcases family_descends (prefixWord ++ tailWord_832058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832109 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 3]
def baseStart_832109 : Nat := 118140960795 + 832109 * 2 ^ 59
def prefixEnd_832109 : Nat := 4983230072969 + 3 ^ 40 * 832109 * 2
def baseEnd_832109 : Nat := 189898610636528934849203

theorem tailTrace_832109 : CollatzResearch.WordTrace tailWord_832109 prefixEnd_832109 189898610636528934849203 := by
  unfold tailWord_832109
  simp only [CollatzResearch.WordTrace]
  refine ⟨30349508542418680748123381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20233005694945787165415587 30349508542418680748123381)
  ·
    refine ⟨2845266425851751320136567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30349508542418680748123381 2845266425851751320136567)
    ·
      refine ⟨4267899638777626980204851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2845266425851751320136567 4267899638777626980204851)
      ·
        refine ⟨6401849458166440470307277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267899638777626980204851 6401849458166440470307277)
        ·
          refine ⟨2400693546812415176365229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6401849458166440470307277 2400693546812415176365229)
          ·
            refine ⟨900260080054655691136961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2400693546812415176365229 900260080054655691136961)
            ·
              refine ⟨675195060040991768352721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900260080054655691136961 675195060040991768352721)
              ·
                refine ⟨506396295030743826264541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675195060040991768352721 506396295030743826264541)
                ·
                  refine ⟨189898610636528934849203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506396295030743826264541 189898610636528934849203)
                  ·
                    rfl

theorem cell21_832109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_832109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832109 prefixEnd_832109 := by exact prefixLift 832109
  have htrace : WordTrace (prefixWord ++ tailWord_832109) baseStart_832109 baseEnd_832109 := by
    simpa [prefixWord, tailWord_832109, baseEnd_832109] using wordTrace_append hprefix tailTrace_832109
  have hstable : (prefixWord ++ tailWord_832109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832109).length < 2 ^ (prefixWord ++ tailWord_832109).sum := by decide
  have hdescent : baseEnd_832109 < baseStart_832109 := by decide
  rcases family_descends (prefixWord ++ tailWord_832109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832151 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 3]
def baseStart_832151 : Nat := 118140960795 + 832151 * 2 ^ 59
def prefixEnd_832151 : Nat := 4983230072969 + 3 ^ 40 * 832151 * 2
def baseEnd_832151 : Nat := 189908195608746195149117

theorem tailTrace_832151 : CollatzResearch.WordTrace tailWord_832151 prefixEnd_832151 189908195608746195149117 := by
  unfold tailWord_832151
  simp only [CollatzResearch.WordTrace]
  refine ⟨30351040408266521921152307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20234026938844347947434871 30351040408266521921152307)
  ·
    refine ⟨45526560612399782881728461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30351040408266521921152307 45526560612399782881728461)
    ·
      refine ⟨17072460229649918580648173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45526560612399782881728461 17072460229649918580648173)
      ·
        refine ⟨6402172586118719467743065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17072460229649918580648173 6402172586118719467743065)
        ·
          refine ⟨4801629439589039600807299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6402172586118719467743065 4801629439589039600807299)
          ·
            refine ⟨7202444159383559401210949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4801629439589039600807299 7202444159383559401210949)
            ·
              refine ⟨1350458279884417387727053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7202444159383559401210949 1350458279884417387727053)
              ·
                refine ⟨506421854956656520397645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350458279884417387727053 506421854956656520397645)
                ·
                  refine ⟨189908195608746195149117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506421854956656520397645 189908195608746195149117)
                  ·
                    rfl

theorem cell21_832151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3].length) (baseStart_832151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832151 prefixEnd_832151 := by exact prefixLift 832151
  have htrace : WordTrace (prefixWord ++ tailWord_832151) baseStart_832151 baseEnd_832151 := by
    simpa [prefixWord, tailWord_832151, baseEnd_832151] using wordTrace_append hprefix tailTrace_832151
  have hstable : (prefixWord ++ tailWord_832151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832151).length < 2 ^ (prefixWord ++ tailWord_832151).sum := by decide
  have hdescent : baseEnd_832151 < baseStart_832151 := by decide
  rcases family_descends (prefixWord ++ tailWord_832151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832196 : List Nat := [2, 3, 3, 1, 1, 2, 4, 5]
def baseStart_832196 : Nat := 118140960795 + 832196 * 2 ^ 59
def prefixEnd_832196 : Nat := 4983230072969 + 3 ^ 40 * 832196 * 2
def baseEnd_832196 : Nat := 63306155073945372299675

theorem tailTrace_832196 : CollatzResearch.WordTrace tailWord_832196 prefixEnd_832196 63306155073945372299675 := by
  unfold tailWord_832196
  simp only [CollatzResearch.WordTrace]
  refine ⟨15176340846551747303270221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20235121128735663071026961 15176340846551747303270221)
  ·
    refine ⟨5691127817456905238726333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15176340846551747303270221 5691127817456905238726333)
    ·
      refine ⟨2134172931546339464522375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5691127817456905238726333 2134172931546339464522375)
      ·
        refine ⟨3201259397319509196783563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134172931546339464522375 3201259397319509196783563)
        ·
          refine ⟨4801889095979263795175345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201259397319509196783563 4801889095979263795175345)
          ·
            refine ⟨3601416821984447846381509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4801889095979263795175345 3601416821984447846381509)
            ·
              refine ⟨675265654122083971196533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3601416821984447846381509 675265654122083971196533)
              ·
                refine ⟨63306155073945372299675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675265654122083971196533 63306155073945372299675)
                ·
                  rfl

theorem cell21_832196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_832196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832196 prefixEnd_832196 := by exact prefixLift 832196
  have htrace : WordTrace (prefixWord ++ tailWord_832196) baseStart_832196 baseEnd_832196 := by
    simpa [prefixWord, tailWord_832196, baseEnd_832196] using wordTrace_append hprefix tailTrace_832196
  have hstable : (prefixWord ++ tailWord_832196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832196).length < 2 ^ (prefixWord ++ tailWord_832196).sum := by decide
  have hdescent : baseEnd_832196 < baseStart_832196 := by decide
  rcases family_descends (prefixWord ++ tailWord_832196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832213 : List Nat := [1, 3, 2, 5, 2, 1, 7]
def baseStart_832213 : Nat := 118140960795 + 832213 * 2 ^ 59
def prefixEnd_832213 : Nat := 4983230072969 + 3 ^ 40 * 832213 * 2
def baseEnd_832213 : Nat := 21102482761494207235073

theorem tailTrace_832213 : CollatzResearch.WordTrace tailWord_832213 prefixEnd_832213 21102482761494207235073 := by
  unfold tailWord_832213
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353301734041906509909293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20235534489361271006606195 30353301734041906509909293)
  ·
    refine ⟨11382488150265714941215985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30353301734041906509909293 11382488150265714941215985)
    ·
      refine ⟨8536866112699286205911989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11382488150265714941215985 8536866112699286205911989)
      ·
        refine ⟨800331198065558081804249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8536866112699286205911989 800331198065558081804249)
        ·
          refine ⟨600248398549168561353187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800331198065558081804249 600248398549168561353187)
          ·
            refine ⟨900372597823752842029781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600248398549168561353187 900372597823752842029781)
            ·
              refine ⟨21102482761494207235073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 900372597823752842029781 21102482761494207235073)
              ·
                rfl

theorem cell21_832213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 7].length) (baseStart_832213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832213 prefixEnd_832213 := by exact prefixLift 832213
  have htrace : WordTrace (prefixWord ++ tailWord_832213) baseStart_832213 baseEnd_832213 := by
    simpa [prefixWord, tailWord_832213, baseEnd_832213] using wordTrace_append hprefix tailTrace_832213
  have hstable : (prefixWord ++ tailWord_832213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832213).length < 2 ^ (prefixWord ++ tailWord_832213).sum := by decide
  have hdescent : baseEnd_832213 < baseStart_832213 := by decide
  rcases family_descends (prefixWord ++ tailWord_832213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832224 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_832224 : Nat := 118140960795 + 832224 * 2 ^ 59
def prefixEnd_832224 : Nat := 4983230072969 + 3 ^ 40 * 832224 * 2
def baseEnd_832224 : Nat := 189924855203314290432301

theorem tailTrace_832224 : CollatzResearch.WordTrace tailWord_832224 prefixEnd_832224 189924855203314290432301 := by
  unfold tailWord_832224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15176851468501027694279863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20235801958001370259039817 15176851468501027694279863)
  ·
    refine ⟨22765277202751541541419795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15176851468501027694279863 22765277202751541541419795)
    ·
      refine ⟨34147915804127312312129693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22765277202751541541419795 34147915804127312312129693)
      ·
        refine ⟨12805468426547742117048635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34147915804127312312129693 12805468426547742117048635)
        ·
          refine ⟨19208202639821613175572953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12805468426547742117048635 19208202639821613175572953)
          ·
            refine ⟨14406151979866209881679715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19208202639821613175572953 14406151979866209881679715)
            ·
              refine ⟨21609227969799314822519573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14406151979866209881679715 21609227969799314822519573)
              ·
                refine ⟨1012932561084342882305605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21609227969799314822519573 1012932561084342882305605)
                ·
                  refine ⟨189924855203314290432301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1012932561084342882305605 189924855203314290432301)
                  ·
                    rfl

theorem cell21_832224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_832224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832224 prefixEnd_832224 := by exact prefixLift 832224
  have htrace : WordTrace (prefixWord ++ tailWord_832224) baseStart_832224 baseEnd_832224 := by
    simpa [prefixWord, tailWord_832224, baseEnd_832224] using wordTrace_append hprefix tailTrace_832224
  have hstable : (prefixWord ++ tailWord_832224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832224).length < 2 ^ (prefixWord ++ tailWord_832224).sum := by decide
  have hdescent : baseEnd_832224 < baseStart_832224 := by decide
  rcases family_descends (prefixWord ++ tailWord_832224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832227 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 5]
def baseStart_832227 : Nat := 118140960795 + 832227 * 2 ^ 59
def prefixEnd_832227 : Nat := 4983230072969 + 3 ^ 40 * 832227 * 2
def baseEnd_832227 : Nat := 189925539844186951882295

theorem tailTrace_832227 : CollatzResearch.WordTrace tailWord_832227 prefixEnd_832227 189925539844186951882295 := by
  unfold tailWord_832227
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353812355991186900918935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20235874903994124600612623 30353812355991186900918935)
  ·
    refine ⟨45530718533986780351378403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30353812355991186900918935 45530718533986780351378403)
    ·
      refine ⟨68296077800980170527067605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45530718533986780351378403 68296077800980170527067605)
      ·
        refine ⟨1600689323460472746728147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68296077800980170527067605 1600689323460472746728147)
        ·
          refine ⟨2401033985190709120092221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600689323460472746728147 2401033985190709120092221)
          ·
            refine ⟨900387744446515920034583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2401033985190709120092221 900387744446515920034583)
            ·
              refine ⟨1350581616669773880051875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900387744446515920034583 1350581616669773880051875)
              ·
                refine ⟨2025872425004660820077813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350581616669773880051875 2025872425004660820077813)
                ·
                  refine ⟨189925539844186951882295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2025872425004660820077813 189925539844186951882295)
                  ·
                    rfl

theorem cell21_832227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_832227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832227 prefixEnd_832227 := by exact prefixLift 832227
  have htrace : WordTrace (prefixWord ++ tailWord_832227) baseStart_832227 baseEnd_832227 := by
    simpa [prefixWord, tailWord_832227, baseEnd_832227] using wordTrace_append hprefix tailTrace_832227
  have hstable : (prefixWord ++ tailWord_832227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832227).length < 2 ^ (prefixWord ++ tailWord_832227).sum := by decide
  have hdescent : baseEnd_832227 < baseStart_832227 := by decide
  rcases family_descends (prefixWord ++ tailWord_832227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832300 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 4]
def baseStart_832300 : Nat := 118140960795 + 832300 * 2 ^ 59
def prefixEnd_832300 : Nat := 4983230072969 + 3 ^ 40 * 832300 * 2
def baseEnd_832300 : Nat := 189942199438755047165479

theorem tailTrace_832300 : CollatzResearch.WordTrace tailWord_832300 prefixEnd_832300 189942199438755047165479 := by
  unfold tailWord_832300
  simp only [CollatzResearch.WordTrace]
  refine ⟨15178237442363360184163177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20237649923151146912217569 15178237442363360184163177)
  ·
    refine ⟨11383678081772520138122383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15178237442363360184163177 11383678081772520138122383)
    ·
      refine ⟨17075517122658780207183575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11383678081772520138122383 17075517122658780207183575)
      ·
        refine ⟨25613275683988170310775363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17075517122658780207183575 25613275683988170310775363)
        ·
          refine ⟨38419913525982255466163045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25613275683988170310775363 38419913525982255466163045)
          ·
            refine ⟨7203733786121672899905571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38419913525982255466163045 7203733786121672899905571)
            ·
              refine ⟨10805600679182509349858357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203733786121672899905571 10805600679182509349858357)
              ·
                refine ⟨1013025063673360251549221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10805600679182509349858357 1013025063673360251549221)
                ·
                  refine ⟨189942199438755047165479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013025063673360251549221 189942199438755047165479)
                  ·
                    rfl

theorem cell21_832300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 4].length) (baseStart_832300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832300 prefixEnd_832300 := by exact prefixLift 832300
  have htrace : WordTrace (prefixWord ++ tailWord_832300) baseStart_832300 baseEnd_832300 := by
    simpa [prefixWord, tailWord_832300, baseEnd_832300] using wordTrace_append hprefix tailTrace_832300
  have hstable : (prefixWord ++ tailWord_832300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832300).length < 2 ^ (prefixWord ++ tailWord_832300).sum := by decide
  have hdescent : baseEnd_832300 < baseStart_832300 := by decide
  rcases family_descends (prefixWord ++ tailWord_832300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832345 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_832345 : Nat := 118140960795 + 832345 * 2 ^ 59
def prefixEnd_832345 : Nat := 4983230072969 + 3 ^ 40 * 832345 * 2
def baseEnd_832345 : Nat := 189952469051844968915387

theorem tailTrace_832345 : CollatzResearch.WordTrace tailWord_832345 prefixEnd_832345 189952469051844968915387 := by
  unfold tailWord_832345
  simp only [CollatzResearch.WordTrace]
  refine ⟨30358116169563693053714489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20238744113042462035809659 30358116169563693053714489)
  ·
    refine ⟨22768587127172769790285867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30358116169563693053714489 22768587127172769790285867)
    ·
      refine ⟨34152880690759154685428801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22768587127172769790285867 34152880690759154685428801)
      ·
        refine ⟨25614660518069366014071601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34152880690759154685428801 25614660518069366014071601)
        ·
          refine ⟨19210995388552024510553701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25614660518069366014071601 19210995388552024510553701)
          ·
            refine ⟨3602061635353504595728819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19210995388552024510553701 3602061635353504595728819)
            ·
              refine ⟨5403092453030256893593229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602061635353504595728819 5403092453030256893593229)
              ·
                refine ⟨2026159669886346335097461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5403092453030256893593229 2026159669886346335097461)
                ·
                  refine ⟨189952469051844968915387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2026159669886346335097461 189952469051844968915387)
                  ·
                    rfl

theorem cell21_832345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_832345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832345 prefixEnd_832345 := by exact prefixLift 832345
  have htrace : WordTrace (prefixWord ++ tailWord_832345) baseStart_832345 baseEnd_832345 := by
    simpa [prefixWord, tailWord_832345, baseEnd_832345] using wordTrace_append hprefix tailTrace_832345
  have hstable : (prefixWord ++ tailWord_832345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832345).length < 2 ^ (prefixWord ++ tailWord_832345).sum := by decide
  have hdescent : baseEnd_832345 < baseStart_832345 := by decide
  rcases family_descends (prefixWord ++ tailWord_832345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832435 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_832435 : Nat := 118140960795 + 832435 * 2 ^ 59
def prefixEnd_832435 : Nat := 4983230072969 + 3 ^ 40 * 832435 * 2
def baseEnd_832435 : Nat := 189973008278024812415203

theorem tailTrace_832435 : CollatzResearch.WordTrace tailWord_832435 prefixEnd_832435 189973008278024812415203 := by
  unfold tailWord_832435
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361398739237638424490759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20240932492825092282993839 30361398739237638424490759)
  ·
    refine ⟨45542098108856457636736139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30361398739237638424490759 45542098108856457636736139)
    ·
      refine ⟨68313147163284686455104209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45542098108856457636736139 68313147163284686455104209)
      ·
        refine ⟨51234860372463514841328157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68313147163284686455104209 51234860372463514841328157)
        ·
          refine ⟨19213072639673818065498059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51234860372463514841328157 19213072639673818065498059)
          ·
            refine ⟨28819608959510727098247089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19213072639673818065498059 28819608959510727098247089)
            ·
              refine ⟨21614706719633045323685317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28819608959510727098247089 21614706719633045323685317)
              ·
                refine ⟨4052757509931195998190997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21614706719633045323685317 4052757509931195998190997)
                ·
                  refine ⟨189973008278024812415203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4052757509931195998190997 189973008278024812415203)
                  ·
                    rfl

theorem cell21_832435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_832435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832435 prefixEnd_832435 := by exact prefixLift 832435
  have htrace : WordTrace (prefixWord ++ tailWord_832435) baseStart_832435 baseEnd_832435 := by
    simpa [prefixWord, tailWord_832435, baseEnd_832435] using wordTrace_append hprefix tailTrace_832435
  have hstable : (prefixWord ++ tailWord_832435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832435).length < 2 ^ (prefixWord ++ tailWord_832435).sum := by decide
  have hdescent : baseEnd_832435 < baseStart_832435 := by decide
  rcases family_descends (prefixWord ++ tailWord_832435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832455 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 3]
def baseStart_832455 : Nat := 118140960795 + 832455 * 2 ^ 59
def prefixEnd_832455 : Nat := 4983230072969 + 3 ^ 40 * 832455 * 2
def baseEnd_832455 : Nat := 189977572550509222081829

theorem tailTrace_832455 : CollatzResearch.WordTrace tailWord_832455 prefixEnd_832455 189977572550509222081829 := by
  unfold tailWord_832455
  simp only [CollatzResearch.WordTrace]
  refine ⟨30362128199165181840218819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20241418799443454560145879 30362128199165181840218819)
  ·
    refine ⟨45543192298747772760328229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30362128199165181840218819 45543192298747772760328229)
    ·
      refine ⟨8539348556015207392561543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45543192298747772760328229 8539348556015207392561543)
      ·
        refine ⟨12809022834022811088842315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539348556015207392561543 12809022834022811088842315)
        ·
          refine ⟨19213534251034216633263473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809022834022811088842315 19213534251034216633263473)
          ·
            refine ⟨14410150688275662474947605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19213534251034216633263473 14410150688275662474947605)
            ·
              refine ⟨675475813512921678513169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14410150688275662474947605 675475813512921678513169)
              ·
                refine ⟨506606860134691258884877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 675475813512921678513169 506606860134691258884877)
                ·
                  refine ⟨189977572550509222081829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506606860134691258884877 189977572550509222081829)
                  ·
                    rfl

theorem cell21_832455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3].length) (baseStart_832455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832455 prefixEnd_832455 := by exact prefixLift 832455
  have htrace : WordTrace (prefixWord ++ tailWord_832455) baseStart_832455 baseEnd_832455 := by
    simpa [prefixWord, tailWord_832455, baseEnd_832455] using wordTrace_append hprefix tailTrace_832455
  have hstable : (prefixWord ++ tailWord_832455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832455).length < 2 ^ (prefixWord ++ tailWord_832455).sum := by decide
  have hdescent : baseEnd_832455 < baseStart_832455 := by decide
  rcases family_descends (prefixWord ++ tailWord_832455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832483 : List Nat := [1, 1, 1, 6, 1, 1, 5, 5]
def baseStart_832483 : Nat := 118140960795 + 832483 * 2 ^ 59
def prefixEnd_832483 : Nat := 4983230072969 + 3 ^ 40 * 832483 * 2
def baseEnd_832483 : Nat := 63327987510662465205035

theorem tailTrace_832483 : CollatzResearch.WordTrace tailWord_832483 prefixEnd_832483 63327987510662465205035 := by
  unfold tailWord_832483
  simp only [CollatzResearch.WordTrace]
  refine ⟨30363149443063742622238103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20242099628709161748158735 30363149443063742622238103)
  ·
    refine ⟨45544724164595613933357155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30363149443063742622238103 45544724164595613933357155)
    ·
      refine ⟨68317086246893420900035733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45544724164595613933357155 68317086246893420900035733)
      ·
        refine ⟨3202363417823129104689175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68317086246893420900035733 3202363417823129104689175)
        ·
          refine ⟨4803545126734693657033763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202363417823129104689175 4803545126734693657033763)
          ·
            refine ⟨7205317690102040485550645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803545126734693657033763 7205317690102040485550645)
            ·
              refine ⟨675498533447066295520373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7205317690102040485550645 675498533447066295520373)
              ·
                refine ⟨63327987510662465205035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675498533447066295520373 63327987510662465205035)
                ·
                  rfl

theorem cell21_832483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 5].length) (baseStart_832483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832483 prefixEnd_832483 := by exact prefixLift 832483
  have htrace : WordTrace (prefixWord ++ tailWord_832483) baseStart_832483 baseEnd_832483 := by
    simpa [prefixWord, tailWord_832483, baseEnd_832483] using wordTrace_append hprefix tailTrace_832483
  have hstable : (prefixWord ++ tailWord_832483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832483).length < 2 ^ (prefixWord ++ tailWord_832483).sum := by decide
  have hdescent : baseEnd_832483 < baseStart_832483 := by decide
  rcases family_descends (prefixWord ++ tailWord_832483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832548 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_832548 : Nat := 118140960795 + 832548 * 2 ^ 59
def prefixEnd_832548 : Nat := 4983230072969 + 3 ^ 40 * 832548 * 2
def baseEnd_832548 : Nat := 189998796417561727031639

theorem tailTrace_832548 : CollatzResearch.WordTrace tailWord_832548 prefixEnd_832548 189998796417561727031639 := by
  unfold tailWord_832548
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182760093914129361677149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20243680125218839148902865 15182760093914129361677149)
  ·
    refine ⟨5693535035217798510628931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15182760093914129361677149 5693535035217798510628931)
    ·
      refine ⟨8540302552826697765943397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693535035217798510628931 8540302552826697765943397)
      ·
        refine ⟨1601306728655005831114387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8540302552826697765943397 1601306728655005831114387)
        ·
          refine ⟨2401960092982508746671581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601306728655005831114387 2401960092982508746671581)
          ·
            refine ⟨900735034868440780001843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2401960092982508746671581 900735034868440780001843)
            ·
              refine ⟨1351102552302661170002765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900735034868440780001843 1351102552302661170002765)
              ·
                refine ⟨506663457113497938751037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1351102552302661170002765 506663457113497938751037)
                ·
                  refine ⟨189998796417561727031639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506663457113497938751037 189998796417561727031639)
                  ·
                    rfl

theorem cell21_832548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_832548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832548 prefixEnd_832548 := by exact prefixLift 832548
  have htrace : WordTrace (prefixWord ++ tailWord_832548) baseStart_832548 baseEnd_832548 := by
    simpa [prefixWord, tailWord_832548, baseEnd_832548] using wordTrace_append hprefix tailTrace_832548
  have hstable : (prefixWord ++ tailWord_832548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832548).length < 2 ^ (prefixWord ++ tailWord_832548).sum := by decide
  have hdescent : baseEnd_832548 < baseStart_832548 := by decide
  rcases family_descends (prefixWord ++ tailWord_832548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832618 : List Nat := [3, 1, 3, 2, 2, 10]
def baseStart_832618 : Nat := 118140960795 + 832618 * 2 ^ 59
def prefixEnd_832618 : Nat := 4983230072969 + 3 ^ 40 * 832618 * 2
def baseEnd_832618 : Nat := 7037584124861376328327

theorem tailTrace_832618 : CollatzResearch.WordTrace tailWord_832618 prefixEnd_832618 7037584124861376328327 := by
  unfold tailWord_832618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592018324393665169600627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20245382198383107118935005 7592018324393665169600627)
  ·
    refine ⟨11388027486590497754400941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7592018324393665169600627 11388027486590497754400941)
    ·
      refine ⟨4270510307471436657900353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11388027486590497754400941 4270510307471436657900353)
      ·
        refine ⟨3202882730603577493425265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4270510307471436657900353 3202882730603577493425265)
        ·
          refine ⟨2402162047952683120068949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3202882730603577493425265 2402162047952683120068949)
          ·
            refine ⟨7037584124861376328327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2402162047952683120068949 7037584124861376328327)
            ·
              rfl

theorem cell21_832618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 10].length) (baseStart_832618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832618 prefixEnd_832618 := by exact prefixLift 832618
  have htrace : WordTrace (prefixWord ++ tailWord_832618) baseStart_832618 baseEnd_832618 := by
    simpa [prefixWord, tailWord_832618, baseEnd_832618] using wordTrace_append hprefix tailTrace_832618
  have hstable : (prefixWord ++ tailWord_832618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832618).length < 2 ^ (prefixWord ++ tailWord_832618).sum := by decide
  have hdescent : baseEnd_832618 < baseStart_832618 := by decide
  rcases family_descends (prefixWord ++ tailWord_832618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832621 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 4]
def baseStart_832621 : Nat := 118140960795 + 832621 * 2 ^ 59
def prefixEnd_832621 : Nat := 4983230072969 + 3 ^ 40 * 832621 * 2
def baseEnd_832621 : Nat := 190015456012129822314823

theorem tailTrace_832621 : CollatzResearch.WordTrace tailWord_832621 prefixEnd_832621 190015456012129822314823 := by
  unfold tailWord_832621
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368182716563792190761717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20245455144375861460507811 30368182716563792190761717)
  ·
    refine ⟨2847017129677855517883911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30368182716563792190761717 2847017129677855517883911)
    ·
      refine ⟨4270525694516783276825867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847017129677855517883911 4270525694516783276825867)
      ·
        refine ⟨6405788541775174915238801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270525694516783276825867 6405788541775174915238801)
        ·
          refine ⟨4804341406331381186429101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405788541775174915238801 4804341406331381186429101)
          ·
            refine ⟨1801628027374267944910913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4804341406331381186429101 1801628027374267944910913)
            ·
              refine ⟨1351221020530700958683185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801628027374267944910913 1351221020530700958683185)
              ·
                refine ⟨1013415765398025719012389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351221020530700958683185 1013415765398025719012389)
                ·
                  refine ⟨190015456012129822314823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013415765398025719012389 190015456012129822314823)
                  ·
                    rfl

theorem cell21_832621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_832621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832621 prefixEnd_832621 := by exact prefixLift 832621
  have htrace : WordTrace (prefixWord ++ tailWord_832621) baseStart_832621 baseEnd_832621 := by
    simpa [prefixWord, tailWord_832621, baseEnd_832621] using wordTrace_append hprefix tailTrace_832621
  have hstable : (prefixWord ++ tailWord_832621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832621).length < 2 ^ (prefixWord ++ tailWord_832621).sum := by decide
  have hdescent : baseEnd_832621 < baseStart_832621 := by decide
  rcases family_descends (prefixWord ++ tailWord_832621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832649 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_832649 : Nat := 118140960795 + 832649 * 2 ^ 59
def prefixEnd_832649 : Nat := 4983230072969 + 3 ^ 40 * 832649 * 2
def baseEnd_832649 : Nat := 190021845993607995848099

theorem tailTrace_832649 : CollatzResearch.WordTrace tailWord_832649 prefixEnd_832649 190021845993607995848099 := by
  unfold tailWord_832649
  simp only [CollatzResearch.WordTrace]
  refine ⟨30369203960462352972781001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20246135973641568648520667 30369203960462352972781001)
  ·
    refine ⟨22776902970346764729585751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30369203960462352972781001 22776902970346764729585751)
    ·
      refine ⟨34165354455520147094378627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22776902970346764729585751 34165354455520147094378627)
      ·
        refine ⟨51248031683280220641567941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34165354455520147094378627 51248031683280220641567941)
        ·
          refine ⟨9609005940615041370293989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51248031683280220641567941 9609005940615041370293989)
          ·
            refine ⟨1801688613865320256930123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9609005940615041370293989 1801688613865320256930123)
            ·
              refine ⟨2702532920797980385395185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801688613865320256930123 2702532920797980385395185)
              ·
                refine ⟨2026899690598485289046389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2702532920797980385395185 2026899690598485289046389)
                ·
                  refine ⟨190021845993607995848099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2026899690598485289046389 190021845993607995848099)
                  ·
                    rfl

theorem cell21_832649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_832649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832649 prefixEnd_832649 := by exact prefixLift 832649
  have htrace : WordTrace (prefixWord ++ tailWord_832649) baseStart_832649 baseEnd_832649 := by
    simpa [prefixWord, tailWord_832649, baseEnd_832649] using wordTrace_append hprefix tailTrace_832649
  have hstable : (prefixWord ++ tailWord_832649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832649).length < 2 ^ (prefixWord ++ tailWord_832649).sum := by decide
  have hdescent : baseEnd_832649 < baseStart_832649 := by decide
  rcases family_descends (prefixWord ++ tailWord_832649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832697 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 4]
def baseStart_832697 : Nat := 118140960795 + 832697 * 2 ^ 59
def prefixEnd_832697 : Nat := 4983230072969 + 3 ^ 40 * 832697 * 2
def baseEnd_832697 : Nat := 190032800247570579048001

theorem tailTrace_832697 : CollatzResearch.WordTrace tailWord_832697 prefixEnd_832697 190032800247570579048001 := by
  unfold tailWord_832697
  simp only [CollatzResearch.WordTrace]
  refine ⟨30370954664288457170528345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20247303109525638113685563 30370954664288457170528345)
  ·
    refine ⟨22778215998216342877896259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30370954664288457170528345 22778215998216342877896259)
    ·
      refine ⟨34167323997324514316844389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22778215998216342877896259 34167323997324514316844389)
      ·
        refine ⟨6406373249498346434408323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34167323997324514316844389 6406373249498346434408323)
        ·
          refine ⟨9609559874247519651612485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6406373249498346434408323 9609559874247519651612485)
          ·
            refine ⟨1801792476421409934677341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9609559874247519651612485 1801792476421409934677341)
            ·
              refine ⟨675672178658028725504003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1801792476421409934677341 675672178658028725504003)
              ·
                refine ⟨1013508267987043088256005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675672178658028725504003 1013508267987043088256005)
                ·
                  refine ⟨190032800247570579048001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013508267987043088256005 190032800247570579048001)
                  ·
                    rfl

theorem cell21_832697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_832697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832697 prefixEnd_832697 := by exact prefixLift 832697
  have htrace : WordTrace (prefixWord ++ tailWord_832697) baseStart_832697 baseEnd_832697 := by
    simpa [prefixWord, tailWord_832697, baseEnd_832697] using wordTrace_append hprefix tailTrace_832697
  have hstable : (prefixWord ++ tailWord_832697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832697).length < 2 ^ (prefixWord ++ tailWord_832697).sum := by decide
  have hdescent : baseEnd_832697 < baseStart_832697 := by decide
  rcases family_descends (prefixWord ++ tailWord_832697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832877 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_832877 : Nat := 118140960795 + 832877 * 2 ^ 59
def prefixEnd_832877 : Nat := 4983230072969 + 3 ^ 40 * 832877 * 2
def baseEnd_832877 : Nat := 190073878699930266047633

theorem tailTrace_832877 : CollatzResearch.WordTrace tailWord_832877 prefixEnd_832877 190073878699930266047633 := by
  unfold tailWord_832877
  simp only [CollatzResearch.WordTrace]
  refine ⟨30377519803636347912080885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20251679869090898608053923 30377519803636347912080885)
  ·
    refine ⟨2847892481590907616757583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30377519803636347912080885 2847892481590907616757583)
    ·
      refine ⟨4271838722386361425136375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847892481590907616757583 4271838722386361425136375)
      ·
        refine ⟨6407758083579542137704563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271838722386361425136375 6407758083579542137704563)
        ·
          refine ⟨9611637125369313206556845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407758083579542137704563 9611637125369313206556845)
          ·
            refine ⟨3604363922013492452458817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9611637125369313206556845 3604363922013492452458817)
            ·
              refine ⟨2703272941510119339344113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3604363922013492452458817 2703272941510119339344113)
              ·
                refine ⟨2027454706132589504508085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2703272941510119339344113 2027454706132589504508085)
                ·
                  refine ⟨190073878699930266047633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2027454706132589504508085 190073878699930266047633)
                  ·
                    rfl

theorem cell21_832877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_832877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832877 prefixEnd_832877 := by exact prefixLift 832877
  have htrace : WordTrace (prefixWord ++ tailWord_832877) baseStart_832877 baseEnd_832877 := by
    simpa [prefixWord, tailWord_832877, baseEnd_832877] using wordTrace_append hprefix tailTrace_832877
  have hstable : (prefixWord ++ tailWord_832877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832877).length < 2 ^ (prefixWord ++ tailWord_832877).sum := by decide
  have hdescent : baseEnd_832877 < baseStart_832877 := by decide
  rcases family_descends (prefixWord ++ tailWord_832877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832922 : List Nat := [3, 1, 1, 4, 1, 1, 4, 6]
def baseStart_832922 : Nat := 118140960795 + 832922 * 2 ^ 59
def prefixEnd_832922 : Nat := 4983230072969 + 3 ^ 40 * 832922 * 2
def baseEnd_832922 : Nat := 63361382771006729265847

theorem tailTrace_832922 : CollatzResearch.WordTrace tailWord_832922 prefixEnd_832922 63361382771006729265847 := by
  unfold tailWord_832922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594790272118330149367255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20252774058982213731646013 7594790272118330149367255)
  ·
    refine ⟨11392185408177495224050883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7594790272118330149367255 11392185408177495224050883)
    ·
      refine ⟨17088278112266242836076325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11392185408177495224050883 17088278112266242836076325)
      ·
        refine ⟨3204052146049920531764311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17088278112266242836076325 3204052146049920531764311)
        ·
          refine ⟨4806078219074880797646467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3204052146049920531764311 4806078219074880797646467)
          ·
            refine ⟨7209117328612321196469701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4806078219074880797646467 7209117328612321196469701)
            ·
              refine ⟨1351709499114810224338069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7209117328612321196469701 1351709499114810224338069)
              ·
                refine ⟨63361382771006729265847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1351709499114810224338069 63361382771006729265847)
                ·
                  rfl

theorem cell21_832922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_832922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832922 prefixEnd_832922 := by exact prefixLift 832922
  have htrace : WordTrace (prefixWord ++ tailWord_832922) baseStart_832922 baseEnd_832922 := by
    simpa [prefixWord, tailWord_832922, baseEnd_832922] using wordTrace_append hprefix tailTrace_832922
  have hstable : (prefixWord ++ tailWord_832922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832922).length < 2 ^ (prefixWord ++ tailWord_832922).sum := by decide
  have hdescent : baseEnd_832922 < baseStart_832922 := by decide
  rcases family_descends (prefixWord ++ tailWord_832922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832925 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 4]
def baseStart_832925 : Nat := 118140960795 + 832925 * 2 ^ 59
def prefixEnd_832925 : Nat := 4983230072969 + 3 ^ 40 * 832925 * 2
def baseEnd_832925 : Nat := 190084832953892849247535

theorem tailTrace_832925 : CollatzResearch.WordTrace tailWord_832925 prefixEnd_832925 190084832953892849247535 := by
  unfold tailWord_832925
  simp only [CollatzResearch.WordTrace]
  refine ⟨30379270507462452109828229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20252847004974968073218819 30379270507462452109828229)
  ·
    refine ⟨5696113220149209770592793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30379270507462452109828229 5696113220149209770592793)
    ·
      refine ⟨4272084915111907327944595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696113220149209770592793 4272084915111907327944595)
      ·
        refine ⟨6408127372667860991916893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272084915111907327944595 6408127372667860991916893)
        ·
          refine ⟨2403047764750447871968835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6408127372667860991916893 2403047764750447871968835)
          ·
            refine ⟨3604571647125671807953253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403047764750447871968835 3604571647125671807953253)
            ·
              refine ⟨675857183836063463991235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3604571647125671807953253 675857183836063463991235)
              ·
                refine ⟨1013785775754095195986853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675857183836063463991235 1013785775754095195986853)
                ·
                  refine ⟨190084832953892849247535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013785775754095195986853 190084832953892849247535)
                  ·
                    rfl

theorem cell21_832925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_832925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832925 prefixEnd_832925 := by exact prefixLift 832925
  have htrace : WordTrace (prefixWord ++ tailWord_832925) baseStart_832925 baseEnd_832925 := by
    simpa [prefixWord, tailWord_832925, baseEnd_832925] using wordTrace_append hprefix tailTrace_832925
  have hstable : (prefixWord ++ tailWord_832925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832925).length < 2 ^ (prefixWord ++ tailWord_832925).sum := by decide
  have hdescent : baseEnd_832925 < baseStart_832925 := by decide
  rcases family_descends (prefixWord ++ tailWord_832925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832962 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_832962 : Nat := 118140960795 + 832962 * 2 ^ 59
def prefixEnd_832962 : Nat := 4983230072969 + 3 ^ 40 * 832962 * 2
def baseEnd_832962 : Nat := 190093276857989007130793

theorem tailTrace_832962 : CollatzResearch.WordTrace tailWord_832962 prefixEnd_832962 190093276857989007130793 := by
  unfold tailWord_832962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595155002082101857231285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20253746672218938285950093 7595155002082101857231285)
  ·
    refine ⟨712045781445197049115433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7595155002082101857231285 712045781445197049115433)
    ·
      refine ⟨534034336083897786836575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712045781445197049115433 534034336083897786836575)
      ·
        refine ⟨801051504125846680254863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534034336083897786836575 801051504125846680254863)
        ·
          refine ⟨1201577256188770020382295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801051504125846680254863 1201577256188770020382295)
          ·
            refine ⟨1802365884283155030573443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201577256188770020382295 1802365884283155030573443)
            ·
              refine ⟨2703548826424732545860165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802365884283155030573443 2703548826424732545860165)
              ·
                refine ⟨506915404954637352348781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2703548826424732545860165 506915404954637352348781)
                ·
                  refine ⟨190093276857989007130793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506915404954637352348781 190093276857989007130793)
                  ·
                    rfl

theorem cell21_832962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_832962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832962 prefixEnd_832962 := by exact prefixLift 832962
  have htrace : WordTrace (prefixWord ++ tailWord_832962) baseStart_832962 baseEnd_832962 := by
    simpa [prefixWord, tailWord_832962, baseEnd_832962] using wordTrace_append hprefix tailTrace_832962
  have hstable : (prefixWord ++ tailWord_832962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832962).length < 2 ^ (prefixWord ++ tailWord_832962).sum := by decide
  have hdescent : baseEnd_832962 < baseStart_832962 := by decide
  rcases family_descends (prefixWord ++ tailWord_832962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832970 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_832970 : Nat := 118140960795 + 832970 * 2 ^ 59
def prefixEnd_832970 : Nat := 4983230072969 + 3 ^ 40 * 832970 * 2
def baseEnd_832970 : Nat := 190095102566982770997443

theorem tailTrace_832970 : CollatzResearch.WordTrace tailWord_832970 prefixEnd_832970 190095102566982770997443 := by
  unfold tailWord_832970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595227948074856198804091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20253941194866283196810909 7595227948074856198804091)
  ·
    refine ⟨11392841922112284298206137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7595227948074856198804091 11392841922112284298206137)
    ·
      refine ⟨8544631441584213223654603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11392841922112284298206137 8544631441584213223654603)
      ·
        refine ⟨12816947162376319835481905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8544631441584213223654603 12816947162376319835481905)
        ·
          refine ⟨9612710371782239876611429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12816947162376319835481905 9612710371782239876611429)
          ·
            refine ⟨1802383194709169976864643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9612710371782239876611429 1802383194709169976864643)
            ·
              refine ⟨2703574792063754965296965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802383194709169976864643 2703574792063754965296965)
              ·
                refine ⟨506920273511954055993181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2703574792063754965296965 506920273511954055993181)
                ·
                  refine ⟨190095102566982770997443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506920273511954055993181 190095102566982770997443)
                  ·
                    rfl

theorem cell21_832970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_832970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_832970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_832970 prefixEnd_832970 := by exact prefixLift 832970
  have htrace : WordTrace (prefixWord ++ tailWord_832970) baseStart_832970 baseEnd_832970 := by
    simpa [prefixWord, tailWord_832970, baseEnd_832970] using wordTrace_append hprefix tailTrace_832970
  have hstable : (prefixWord ++ tailWord_832970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832970).length < 2 ^ (prefixWord ++ tailWord_832970).sum := by decide
  have hdescent : baseEnd_832970 < baseStart_832970 := by decide
  rcases family_descends (prefixWord ++ tailWord_832970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833094 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_833094 : Nat := 118140960795 + 833094 * 2 ^ 59
def prefixEnd_833094 : Nat := 4983230072969 + 3 ^ 40 * 833094 * 2
def baseEnd_833094 : Nat := 190123401056386110930523

theorem tailTrace_833094 : CollatzResearch.WordTrace tailWord_833094 prefixEnd_833094 190123401056386110930523 := by
  unfold tailWord_833094
  simp only [CollatzResearch.WordTrace]
  refine ⟨949544826370318561647823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20256956295900129315153557 949544826370318561647823)
  ·
    refine ⟨1424317239555477842471735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949544826370318561647823 1424317239555477842471735)
    ·
      refine ⟨2136475859333216763707603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424317239555477842471735 2136475859333216763707603)
      ·
        refine ⟨3204713788999825145561405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136475859333216763707603 3204713788999825145561405)
        ·
          refine ⟨1201767670874934429585527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3204713788999825145561405 1201767670874934429585527)
          ·
            refine ⟨1802651506312401644378291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201767670874934429585527 1802651506312401644378291)
            ·
              refine ⟨2703977259468602466567437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802651506312401644378291 2703977259468602466567437)
              ·
                refine ⟨1013991472300725924962789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2703977259468602466567437 1013991472300725924962789)
                ·
                  refine ⟨190123401056386110930523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1013991472300725924962789 190123401056386110930523)
                  ·
                    rfl

theorem cell21_833094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_833094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833094 prefixEnd_833094 := by exact prefixLift 833094
  have htrace : WordTrace (prefixWord ++ tailWord_833094) baseStart_833094 baseEnd_833094 := by
    simpa [prefixWord, tailWord_833094, baseEnd_833094] using wordTrace_append hprefix tailTrace_833094
  have hstable : (prefixWord ++ tailWord_833094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833094).length < 2 ^ (prefixWord ++ tailWord_833094).sum := by decide
  have hdescent : baseEnd_833094 < baseStart_833094 := by decide
  rcases family_descends (prefixWord ++ tailWord_833094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833133 : List Nat := [1, 5, 1, 1, 13]
def baseStart_833133 : Nat := 118140960795 + 833133 * 2 ^ 59
def prefixEnd_833133 : Nat := 4983230072969 + 3 ^ 40 * 833133 * 2
def baseEnd_833133 : Nat := 2347312362811490244203

theorem tailTrace_833133 : CollatzResearch.WordTrace tailWord_833133 prefixEnd_833133 2347312362811490244203 := by
  unfold tailWord_833133
  simp only [CollatzResearch.WordTrace]
  refine ⟨30386856890708903633400053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20257904593805935755600035 30386856890708903633400053)
  ·
    refine ⟨2848767833503959715631255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30386856890708903633400053 2848767833503959715631255)
    ·
      refine ⟨4273151750255939573446883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2848767833503959715631255 4273151750255939573446883)
      ·
        refine ⟨6409727625383909360170325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4273151750255939573446883 6409727625383909360170325)
        ·
          refine ⟨2347312362811490244203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6409727625383909360170325 2347312362811490244203)
          ·
            rfl

theorem cell21_833133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 13].length) (baseStart_833133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833133 prefixEnd_833133 := by exact prefixLift 833133
  have htrace : WordTrace (prefixWord ++ tailWord_833133) baseStart_833133 baseEnd_833133 := by
    simpa [prefixWord, tailWord_833133, baseEnd_833133] using wordTrace_append hprefix tailTrace_833133
  have hstable : (prefixWord ++ tailWord_833133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833133).length < 2 ^ (prefixWord ++ tailWord_833133).sum := by decide
  have hdescent : baseEnd_833133 < baseStart_833133 := by decide
  rcases family_descends (prefixWord ++ tailWord_833133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833136 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_833136 : Nat := 118140960795 + 833136 * 2 ^ 59
def prefixEnd_833136 : Nat := 4983230072969 + 3 ^ 40 * 833136 * 2
def baseEnd_833136 : Nat := 190132986028603371230437

theorem tailTrace_833136 : CollatzResearch.WordTrace tailWord_833136 prefixEnd_833136 190132986028603371230437 := by
  unfold tailWord_833136
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193483154849017572879631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20257977539798690097172841 15193483154849017572879631)
  ·
    refine ⟨22790224732273526359319447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15193483154849017572879631 22790224732273526359319447)
    ·
      refine ⟨34185337098410289538979171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22790224732273526359319447 34185337098410289538979171)
      ·
        refine ⟨51278005647615434308468757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34185337098410289538979171 51278005647615434308468757)
        ·
          refine ⟨2403656514731973483209473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51278005647615434308468757 2403656514731973483209473)
          ·
            refine ⟨1802742386048980112407105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403656514731973483209473 1802742386048980112407105)
            ·
              refine ⟨1352056789536735084305329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802742386048980112407105 1352056789536735084305329)
              ·
                refine ⟨1014042592152551313228997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352056789536735084305329 1014042592152551313228997)
                ·
                  refine ⟨190132986028603371230437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014042592152551313228997 190132986028603371230437)
                  ·
                    rfl

theorem cell21_833136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_833136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833136 prefixEnd_833136 := by exact prefixLift 833136
  have htrace : WordTrace (prefixWord ++ tailWord_833136) baseStart_833136 baseEnd_833136 := by
    simpa [prefixWord, tailWord_833136, baseEnd_833136] using wordTrace_append hprefix tailTrace_833136
  have hstable : (prefixWord ++ tailWord_833136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833136).length < 2 ^ (prefixWord ++ tailWord_833136).sum := by decide
  have hdescent : baseEnd_833136 < baseStart_833136 := by decide
  rcases family_descends (prefixWord ++ tailWord_833136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833164 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 5]
def baseStart_833164 : Nat := 118140960795 + 833164 * 2 ^ 59
def prefixEnd_833164 : Nat := 4983230072969 + 3 ^ 40 * 833164 * 2
def baseEnd_833164 : Nat := 190139376010081544763713

theorem tailTrace_833164 : CollatzResearch.WordTrace tailWord_833164 prefixEnd_833164 190139376010081544763713 := by
  unfold tailWord_833164
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193993776798297963889273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20258658369064397285185697 15193993776798297963889273)
  ·
    refine ⟨11395495332598723472916955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15193993776798297963889273 11395495332598723472916955)
    ·
      refine ⟨17093242998898085209375433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11395495332598723472916955 17093242998898085209375433)
      ·
        refine ⟨12819932249173563907031575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17093242998898085209375433 12819932249173563907031575)
        ·
          refine ⟨19229898373760345860547363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12819932249173563907031575 19229898373760345860547363)
          ·
            refine ⟨28844847560640518790821045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19229898373760345860547363 28844847560640518790821045)
            ·
              refine ⟨2704204458810048636639473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28844847560640518790821045 2704204458810048636639473)
              ·
                refine ⟨2028153344107536477479605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704204458810048636639473 2028153344107536477479605)
                ·
                  refine ⟨190139376010081544763713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2028153344107536477479605 190139376010081544763713)
                  ·
                    rfl

theorem cell21_833164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 5].length) (baseStart_833164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833164 prefixEnd_833164 := by exact prefixLift 833164
  have htrace : WordTrace (prefixWord ++ tailWord_833164) baseStart_833164 baseEnd_833164 := by
    simpa [prefixWord, tailWord_833164, baseEnd_833164] using wordTrace_append hprefix tailTrace_833164
  have hstable : (prefixWord ++ tailWord_833164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833164).length < 2 ^ (prefixWord ++ tailWord_833164).sum := by decide
  have hdescent : baseEnd_833164 < baseStart_833164 := by decide
  rcases family_descends (prefixWord ++ tailWord_833164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833218 : List Nat := [3, 5, 1, 2, 1, 2, 2, 5]
def baseStart_833218 : Nat := 118140960795 + 833218 * 2 ^ 59
def prefixEnd_833218 : Nat := 4983230072969 + 3 ^ 40 * 833218 * 2
def baseEnd_833218 : Nat := 63383899848596483621201

theorem tailTrace_833218 : CollatzResearch.WordTrace tailWord_833218 prefixEnd_833218 63383899848596483621201 := by
  unfold tailWord_833218
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597489273850240787561077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20259971396933975433496205 7597489273850240787561077)
  ·
    refine ⟨712264619423460073833851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7597489273850240787561077 712264619423460073833851)
    ·
      refine ⟨1068396929135190110750777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 712264619423460073833851 1068396929135190110750777)
      ·
        refine ⟨801297696851392583063083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1068396929135190110750777 801297696851392583063083)
        ·
          refine ⟨1201946545277088874594625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801297696851392583063083 1201946545277088874594625)
          ·
            refine ⟨901459908957816655945969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201946545277088874594625 901459908957816655945969)
            ·
              refine ⟨676094931718362491959477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901459908957816655945969 676094931718362491959477)
              ·
                refine ⟨63383899848596483621201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 676094931718362491959477 63383899848596483621201)
                ·
                  rfl

theorem cell21_833218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_833218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833218 prefixEnd_833218 := by exact prefixLift 833218
  have htrace : WordTrace (prefixWord ++ tailWord_833218) baseStart_833218 baseEnd_833218 := by
    simpa [prefixWord, tailWord_833218, baseEnd_833218] using wordTrace_append hprefix tailTrace_833218
  have hstable : (prefixWord ++ tailWord_833218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833218).length < 2 ^ (prefixWord ++ tailWord_833218).sum := by decide
  have hdescent : baseEnd_833218 < baseStart_833218 := by decide
  rcases family_descends (prefixWord ++ tailWord_833218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833226 : List Nat := [3, 1, 2, 1, 5, 1, 1, 7]
def baseStart_833226 : Nat := 118140960795 + 833226 * 2 ^ 59
def prefixEnd_833226 : Nat := 4983230072969 + 3 ^ 40 * 833226 * 2
def baseEnd_833226 : Nat := 63384508418261071576751

theorem tailTrace_833226 : CollatzResearch.WordTrace tailWord_833226 prefixEnd_833226 63384508418261071576751 := by
  unfold tailWord_833226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597562219842995129133883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20260165919581320344357021 7597562219842995129133883)
  ·
    refine ⟨11396343329764492693700825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7597562219842995129133883 11396343329764492693700825)
    ·
      refine ⟨8547257497323369520275619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11396343329764492693700825 8547257497323369520275619)
      ·
        refine ⟨12820886245985054280413429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547257497323369520275619 12820886245985054280413429)
        ·
          refine ⟨1201958085561098838788759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12820886245985054280413429 1201958085561098838788759)
          ·
            refine ⟨1802937128341648258183139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201958085561098838788759 1802937128341648258183139)
            ·
              refine ⟨2704405692512472387274709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802937128341648258183139 2704405692512472387274709)
              ·
                refine ⟨63384508418261071576751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2704405692512472387274709 63384508418261071576751)
                ·
                  rfl

theorem cell21_833226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_833226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833226 prefixEnd_833226 := by exact prefixLift 833226
  have htrace : WordTrace (prefixWord ++ tailWord_833226) baseStart_833226 baseEnd_833226 := by
    simpa [prefixWord, tailWord_833226, baseEnd_833226] using wordTrace_append hprefix tailTrace_833226
  have hstable : (prefixWord ++ tailWord_833226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833226).length < 2 ^ (prefixWord ++ tailWord_833226).sum := by decide
  have hdescent : baseEnd_833226 < baseStart_833226 := by decide
  rcases family_descends (prefixWord ++ tailWord_833226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833299 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_833299 : Nat := 118140960795 + 833299 * 2 ^ 59
def prefixEnd_833299 : Nat := 4983230072969 + 3 ^ 40 * 833299 * 2
def baseEnd_833299 : Nat := 190170184849351310013437

theorem tailTrace_833299 : CollatzResearch.WordTrace tailWord_833299 prefixEnd_833299 190170184849351310013437 := by
  unfold tailWord_833299
  simp only [CollatzResearch.WordTrace]
  refine ⟨30392911408107513983942951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20261940938738342655961967 30392911408107513983942951)
  ·
    refine ⟨45589367112161270975914427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30392911408107513983942951 45589367112161270975914427)
    ·
      refine ⟨68384050668241906463871641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45589367112161270975914427 68384050668241906463871641)
      ·
        refine ⟨51288038001181429847903731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68384050668241906463871641 51288038001181429847903731)
        ·
          refine ⟨76932057001772144771855597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51288038001181429847903731 76932057001772144771855597)
          ·
            refine ⟨28849521375664554289445849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76932057001772144771855597 28849521375664554289445849)
            ·
              refine ⟨21637141031748415717084387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28849521375664554289445849 21637141031748415717084387)
              ·
                refine ⟨32455711547622623575626581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21637141031748415717084387 32455711547622623575626581)
                ·
                  refine ⟨190170184849351310013437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32455711547622623575626581 190170184849351310013437)
                  ·
                    rfl

theorem cell21_833299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_833299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833299 prefixEnd_833299 := by exact prefixLift 833299
  have htrace : WordTrace (prefixWord ++ tailWord_833299) baseStart_833299 baseEnd_833299 := by
    simpa [prefixWord, tailWord_833299, baseEnd_833299] using wordTrace_append hprefix tailTrace_833299
  have hstable : (prefixWord ++ tailWord_833299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833299).length < 2 ^ (prefixWord ++ tailWord_833299).sum := by decide
  have hdescent : baseEnd_833299 < baseStart_833299 := by decide
  rcases family_descends (prefixWord ++ tailWord_833299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833333 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_833333 : Nat := 118140960795 + 833333 * 2 ^ 59
def prefixEnd_833333 : Nat := 4983230072969 + 3 ^ 40 * 833333 * 2
def baseEnd_833333 : Nat := 190177944112574806446701

theorem tailTrace_833333 : CollatzResearch.WordTrace tailWord_833333 prefixEnd_833333 190177944112574806446701 := by
  unfold tailWord_833333
  simp only [CollatzResearch.WordTrace]
  refine ⟨30394151489984337790680653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20262767659989558527120435 30394151489984337790680653)
  ·
    refine ⟨11397806808744126671505245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30394151489984337790680653 11397806808744126671505245)
    ·
      refine ⟨4274177553279047501814467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11397806808744126671505245 4274177553279047501814467)
      ·
        refine ⟨6411266329918571252721701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274177553279047501814467 6411266329918571252721701)
        ·
          refine ⟨1202112436859732109885319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6411266329918571252721701 1202112436859732109885319)
          ·
            refine ⟨1803168655289598164827979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202112436859732109885319 1803168655289598164827979)
            ·
              refine ⟨2704752982934397247241969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803168655289598164827979 2704752982934397247241969)
              ·
                refine ⟨2028564737200797935431477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2704752982934397247241969 2028564737200797935431477)
                ·
                  refine ⟨190177944112574806446701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2028564737200797935431477 190177944112574806446701)
                  ·
                    rfl

theorem cell21_833333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_833333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833333 prefixEnd_833333 := by exact prefixLift 833333
  have htrace : WordTrace (prefixWord ++ tailWord_833333) baseStart_833333 baseEnd_833333 := by
    simpa [prefixWord, tailWord_833333, baseEnd_833333] using wordTrace_append hprefix tailTrace_833333
  have hstable : (prefixWord ++ tailWord_833333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833333).length < 2 ^ (prefixWord ++ tailWord_833333).sum := by decide
  have hdescent : baseEnd_833333 < baseStart_833333 := by decide
  rcases family_descends (prefixWord ++ tailWord_833333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833361 : List Nat := [1, 2, 2, 1, 5, 2, 8]
def baseStart_833361 : Nat := 118140960795 + 833361 * 2 ^ 59
def prefixEnd_833361 : Nat := 4983230072969 + 3 ^ 40 * 833361 * 2
def baseEnd_833361 : Nat := 21131592677116997775553

theorem tailTrace_833361 : CollatzResearch.WordTrace tailWord_833361 prefixEnd_833361 21131592677116997775553 := by
  unfold tailWord_833361
  simp only [CollatzResearch.WordTrace]
  refine ⟨30395172733882898572699937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20263448489255265715133291 30395172733882898572699937)
  ·
    refine ⟨22796379550412173929524953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30395172733882898572699937 22796379550412173929524953)
    ·
      refine ⟨17097284662809130447143715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22796379550412173929524953 17097284662809130447143715)
      ·
        refine ⟨25645926994213695670715573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17097284662809130447143715 25645926994213695670715573)
        ·
          refine ⟨2404305655707533969129585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25645926994213695670715573 2404305655707533969129585)
          ·
            refine ⟨1803229241780650476847189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2404305655707533969129585 1803229241780650476847189)
            ·
              refine ⟨21131592677116997775553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1803229241780650476847189 21131592677116997775553)
              ·
                rfl

theorem cell21_833361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 8].length) (baseStart_833361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833361 prefixEnd_833361 := by exact prefixLift 833361
  have htrace : WordTrace (prefixWord ++ tailWord_833361) baseStart_833361 baseEnd_833361 := by
    simpa [prefixWord, tailWord_833361, baseEnd_833361] using wordTrace_append hprefix tailTrace_833361
  have hstable : (prefixWord ++ tailWord_833361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833361).length < 2 ^ (prefixWord ++ tailWord_833361).sum := by decide
  have hdescent : baseEnd_833361 < baseStart_833361 := by decide
  rcases family_descends (prefixWord ++ tailWord_833361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833364 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_833364 : Nat := 118140960795 + 833364 * 2 ^ 59
def prefixEnd_833364 : Nat := 4983230072969 + 3 ^ 40 * 833364 * 2
def baseEnd_833364 : Nat := 190185018734925641429971

theorem tailTrace_833364 : CollatzResearch.WordTrace tailWord_833364 prefixEnd_833364 190185018734925641429971 := by
  unfold tailWord_833364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197641076436015042529573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20263521435248020056706097 15197641076436015042529573)
  ·
    refine ⟨2849557701831752820474295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15197641076436015042529573 2849557701831752820474295)
    ·
      refine ⟨4274336552747629230711443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849557701831752820474295 4274336552747629230711443)
      ·
        refine ⟨6411504829121443846067165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274336552747629230711443 6411504829121443846067165)
        ·
          refine ⟨2404314310920541442275187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6411504829121443846067165 2404314310920541442275187)
          ·
            refine ⟨3606471466380812163412781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404314310920541442275187 3606471466380812163412781)
            ·
              refine ⟨1352426799892804561279793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3606471466380812163412781 1352426799892804561279793)
              ·
                refine ⟨1014320099919603420959845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352426799892804561279793 1014320099919603420959845)
                ·
                  refine ⟨190185018734925641429971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014320099919603420959845 190185018734925641429971)
                  ·
                    rfl

theorem cell21_833364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_833364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833364 prefixEnd_833364 := by exact prefixLift 833364
  have htrace : WordTrace (prefixWord ++ tailWord_833364) baseStart_833364 baseEnd_833364 := by
    simpa [prefixWord, tailWord_833364, baseEnd_833364] using wordTrace_append hprefix tailTrace_833364
  have hstable : (prefixWord ++ tailWord_833364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833364).length < 2 ^ (prefixWord ++ tailWord_833364).sum := by decide
  have hdescent : baseEnd_833364 < baseStart_833364 := by decide
  rcases family_descends (prefixWord ++ tailWord_833364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833426 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_833426 : Nat := 118140960795 + 833426 * 2 ^ 59
def prefixEnd_833426 : Nat := 4983230072969 + 3 ^ 40 * 833426 * 2
def baseEnd_833426 : Nat := 190199167979627311396511

theorem tailTrace_833426 : CollatzResearch.WordTrace tailWord_833426 prefixEnd_833426 190199167979627311396511 := by
  unfold tailWord_833426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599385869661853668454033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20265028985764943115877421 7599385869661853668454033)
  ·
    refine ⟨5699539402246390251340525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7599385869661853668454033 5699539402246390251340525)
    ·
      refine ⟨2137327275842396344252697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5699539402246390251340525 2137327275842396344252697)
      ·
        refine ⟨1602995456881797258189523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2137327275842396344252697 1602995456881797258189523)
        ·
          refine ⟨2404493185322695887284285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602995456881797258189523 2404493185322695887284285)
          ·
            refine ⟨901684944496010957731607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2404493185322695887284285 901684944496010957731607)
            ·
              refine ⟨1352527416744016436597411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901684944496010957731607 1352527416744016436597411)
              ·
                refine ⟨2028791125116024654896117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352527416744016436597411 2028791125116024654896117)
                ·
                  refine ⟨190199167979627311396511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2028791125116024654896117 190199167979627311396511)
                  ·
                    rfl

theorem cell21_833426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_833426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833426 prefixEnd_833426 := by exact prefixLift 833426
  have htrace : WordTrace (prefixWord ++ tailWord_833426) baseStart_833426 baseEnd_833426 := by
    simpa [prefixWord, tailWord_833426, baseEnd_833426] using wordTrace_append hprefix tailTrace_833426
  have hstable : (prefixWord ++ tailWord_833426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833426).length < 2 ^ (prefixWord ++ tailWord_833426).sum := by decide
  have hdescent : baseEnd_833426 < baseStart_833426 := by decide
  rcases family_descends (prefixWord ++ tailWord_833426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833437 : List Nat := [1, 4, 2, 1, 2, 2, 1, 8]
def baseStart_833437 : Nat := 118140960795 + 833437 * 2 ^ 59
def prefixEnd_833437 : Nat := 4983230072969 + 3 ^ 40 * 833437 * 2
def baseEnd_833437 : Nat := 63400559443164578904385

theorem tailTrace_833437 : CollatzResearch.WordTrace tailWord_833437 prefixEnd_833437 63400559443164578904385 := by
  unfold tailWord_833437
  simp only [CollatzResearch.WordTrace]
  refine ⟨30397944681607563552466565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20265296454405042368311043 30397944681607563552466565)
  ·
    refine ⟨5699614627801418166087481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30397944681607563552466565 5699614627801418166087481)
    ·
      refine ⟨4274710970851063624565611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5699614627801418166087481 4274710970851063624565611)
      ·
        refine ⟨6412066456276595436848417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274710970851063624565611 6412066456276595436848417)
        ·
          refine ⟨4809049842207446577636313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6412066456276595436848417 4809049842207446577636313)
          ·
            refine ⟨3606787381655584933227235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4809049842207446577636313 3606787381655584933227235)
            ·
              refine ⟨5410181072483377399840853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3606787381655584933227235 5410181072483377399840853)
              ·
                refine ⟨63400559443164578904385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5410181072483377399840853 63400559443164578904385)
                ·
                  rfl

theorem cell21_833437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_833437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833437 prefixEnd_833437 := by exact prefixLift 833437
  have htrace : WordTrace (prefixWord ++ tailWord_833437) baseStart_833437 baseEnd_833437 := by
    simpa [prefixWord, tailWord_833437, baseEnd_833437] using wordTrace_append hprefix tailTrace_833437
  have hstable : (prefixWord ++ tailWord_833437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833437).length < 2 ^ (prefixWord ++ tailWord_833437).sum := by decide
  have hdescent : baseEnd_833437 < baseStart_833437 := by decide
  rcases family_descends (prefixWord ++ tailWord_833437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833482 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_833482 : Nat := 118140960795 + 833482 * 2 ^ 59
def prefixEnd_833482 : Nat := 4983230072969 + 3 ^ 40 * 833482 * 2
def baseEnd_833482 : Nat := 190211947942583658463063

theorem tailTrace_833482 : CollatzResearch.WordTrace tailWord_833482 prefixEnd_833482 190211947942583658463063 := by
  unfold tailWord_833482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599896491611134059463675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20266390644296357491903133 7599896491611134059463675)
  ·
    refine ⟨11399844737416701089195513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599896491611134059463675 11399844737416701089195513)
    ·
      refine ⟨8549883553062525816896635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11399844737416701089195513 8549883553062525816896635)
      ·
        refine ⟨12824825329593788725344953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549883553062525816896635 12824825329593788725344953)
        ·
          refine ⟨9618618997195341544008715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824825329593788725344953 9618618997195341544008715)
          ·
            refine ⟨14427928495793012316013073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618618997195341544008715 14427928495793012316013073)
            ·
              refine ⟨10820946371844759237009805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14427928495793012316013073 10820946371844759237009805)
              ·
                refine ⟨4057854889441784713878677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10820946371844759237009805 4057854889441784713878677)
                ·
                  refine ⟨190211947942583658463063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4057854889441784713878677 190211947942583658463063)
                  ·
                    rfl

theorem cell21_833482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_833482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833482 prefixEnd_833482 := by exact prefixLift 833482
  have htrace : WordTrace (prefixWord ++ tailWord_833482) baseStart_833482 baseEnd_833482 := by
    simpa [prefixWord, tailWord_833482, baseEnd_833482] using wordTrace_append hprefix tailTrace_833482
  have hstable : (prefixWord ++ tailWord_833482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833482).length < 2 ^ (prefixWord ++ tailWord_833482).sum := by decide
  have hdescent : baseEnd_833482 < baseStart_833482 := by decide
  rcases family_descends (prefixWord ++ tailWord_833482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833544 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_833544 : Nat := 118140960795 + 833544 * 2 ^ 59
def prefixEnd_833544 : Nat := 4983230072969 + 3 ^ 40 * 833544 * 2
def baseEnd_833544 : Nat := 190226097187285328429603

theorem tailTrace_833544 : CollatzResearch.WordTrace tailWord_833544 prefixEnd_833544 190226097187285328429603 := by
  unfold tailWord_833544
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200923646109960413305843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20267898194813280551074457 15200923646109960413305843)
  ·
    refine ⟨22801385469164940619958765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15200923646109960413305843 22801385469164940619958765)
    ·
      refine ⟨8550519550936852732484537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22801385469164940619958765 8550519550936852732484537)
      ·
        refine ⟨6412889663202639549363403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8550519550936852732484537 6412889663202639549363403)
        ·
          refine ⟨9619334494803959324045105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6412889663202639549363403 9619334494803959324045105)
          ·
            refine ⟨7214500871102969493033829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9619334494803959324045105 7214500871102969493033829)
            ·
              refine ⟨1352718913331806779943843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7214500871102969493033829 1352718913331806779943843)
              ·
                refine ⟨2029078369997710169915765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352718913331806779943843 2029078369997710169915765)
                ·
                  refine ⟨190226097187285328429603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029078369997710169915765 190226097187285328429603)
                  ·
                    rfl

theorem cell21_833544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_833544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833544 prefixEnd_833544 := by exact prefixLift 833544
  have htrace : WordTrace (prefixWord ++ tailWord_833544) baseStart_833544 baseEnd_833544 := by
    simpa [prefixWord, tailWord_833544, baseEnd_833544] using wordTrace_append hprefix tailTrace_833544
  have hstable : (prefixWord ++ tailWord_833544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833544).length < 2 ^ (prefixWord ++ tailWord_833544).sum := by decide
  have hdescent : baseEnd_833544 < baseStart_833544 := by decide
  rcases family_descends (prefixWord ++ tailWord_833544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833578 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_833578 : Nat := 118140960795 + 833578 * 2 ^ 59
def prefixEnd_833578 : Nat := 4983230072969 + 3 ^ 40 * 833578 * 2
def baseEnd_833578 : Nat := 190233856450508824862867

theorem tailTrace_833578 : CollatzResearch.WordTrace tailWord_833578 prefixEnd_833578 190233856450508824862867 := by
  unfold tailWord_833578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600771843524186158337347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20268724916064496422232925 7600771843524186158337347)
  ·
    refine ⟨11401157765286279237506021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7600771843524186158337347 11401157765286279237506021)
    ·
      refine ⟨2137717080991177357032379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11401157765286279237506021 2137717080991177357032379)
      ·
        refine ⟨3206575621486766035548569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137717080991177357032379 3206575621486766035548569)
        ·
          refine ⟨2404931716115074526661427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3206575621486766035548569 2404931716115074526661427)
          ·
            refine ⟨3607397574172611789992141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2404931716115074526661427 3607397574172611789992141)
            ·
              refine ⟨1352774090314729421247053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3607397574172611789992141 1352774090314729421247053)
              ·
                refine ⟨507290283868023532967645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352774090314729421247053 507290283868023532967645)
                ·
                  refine ⟨190233856450508824862867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507290283868023532967645 190233856450508824862867)
                  ·
                    rfl

theorem cell21_833578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_833578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833578 prefixEnd_833578 := by exact prefixLift 833578
  have htrace : WordTrace (prefixWord ++ tailWord_833578) baseStart_833578 baseEnd_833578 := by
    simpa [prefixWord, tailWord_833578, baseEnd_833578] using wordTrace_append hprefix tailTrace_833578
  have hstable : (prefixWord ++ tailWord_833578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833578).length < 2 ^ (prefixWord ++ tailWord_833578).sum := by decide
  have hdescent : baseEnd_833578 < baseStart_833578 := by decide
  rcases family_descends (prefixWord ++ tailWord_833578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833603 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_833603 : Nat := 118140960795 + 833603 * 2 ^ 59
def prefixEnd_833603 : Nat := 4983230072969 + 3 ^ 40 * 833603 * 2
def baseEnd_833603 : Nat := 190239561791114336946149

theorem tailTrace_833603 : CollatzResearch.WordTrace tailWord_833603 prefixEnd_833603 190239561791114336946149 := by
  unfold tailWord_833603
  simp only [CollatzResearch.WordTrace]
  refine ⟨30403999199006173903009463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20269332799337449268672975 30403999199006173903009463)
  ·
    refine ⟨45605998798509260854514195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30403999199006173903009463 45605998798509260854514195)
    ·
      refine ⟨68408998197763891281771293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45605998798509260854514195 68408998197763891281771293)
      ·
        refine ⟨25653374324161459230664235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68408998197763891281771293 25653374324161459230664235)
        ·
          refine ⟨38480061486242188845996353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25653374324161459230664235 38480061486242188845996353)
          ·
            refine ⟨28860046114681641634497265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38480061486242188845996353 28860046114681641634497265)
            ·
              refine ⟨21645034586011231225872949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28860046114681641634497265 21645034586011231225872949)
              ·
                refine ⟨2029221992438552927425589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21645034586011231225872949 2029221992438552927425589)
                ·
                  refine ⟨190239561791114336946149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029221992438552927425589 190239561791114336946149)
                  ·
                    rfl

theorem cell21_833603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_833603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833603 prefixEnd_833603 := by exact prefixLift 833603
  have htrace : WordTrace (prefixWord ++ tailWord_833603) baseStart_833603 baseEnd_833603 := by
    simpa [prefixWord, tailWord_833603, baseEnd_833603] using wordTrace_append hprefix tailTrace_833603
  have hstable : (prefixWord ++ tailWord_833603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833603).length < 2 ^ (prefixWord ++ tailWord_833603).sum := by decide
  have hdescent : baseEnd_833603 < baseStart_833603 := by decide
  rcases family_descends (prefixWord ++ tailWord_833603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833648 : List Nat := [2, 1, 1, 1, 5, 11]
def baseStart_833648 : Nat := 118140960795 + 833648 * 2 ^ 59
def prefixEnd_833648 : Nat := 4983230072969 + 3 ^ 40 * 833648 * 2
def baseEnd_833648 : Nat := 7046290052007565136891

theorem tailTrace_833648 : CollatzResearch.WordTrace tailWord_833648 prefixEnd_833648 7046290052007565136891 := by
  unfold tailWord_833648
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202820241921573294198799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20270426989228764392265065 15202820241921573294198799)
  ·
    refine ⟨22804230362882359941298199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202820241921573294198799 22804230362882359941298199)
    ·
      refine ⟨34206345544323539911947299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22804230362882359941298199 34206345544323539911947299)
      ·
        refine ⟨51309518316485309867920949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34206345544323539911947299 51309518316485309867920949)
        ·
          refine ⟨4810267342170497800117589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51309518316485309867920949 4810267342170497800117589)
          ·
            refine ⟨7046290052007565136891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4810267342170497800117589 7046290052007565136891)
            ·
              rfl

theorem cell21_833648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 11].length) (baseStart_833648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833648 prefixEnd_833648 := by exact prefixLift 833648
  have htrace : WordTrace (prefixWord ++ tailWord_833648) baseStart_833648 baseEnd_833648 := by
    simpa [prefixWord, tailWord_833648, baseEnd_833648] using wordTrace_append hprefix tailTrace_833648
  have hstable : (prefixWord ++ tailWord_833648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833648).length < 2 ^ (prefixWord ++ tailWord_833648).sum := by decide
  have hdescent : baseEnd_833648 < baseStart_833648 := by decide
  rcases family_descends (prefixWord ++ tailWord_833648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833654 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_833654 : Nat := 118140960795 + 833654 * 2 ^ 59
def prefixEnd_833654 : Nat := 4983230072969 + 3 ^ 40 * 833654 * 2
def baseEnd_833654 : Nat := 190251200685949581596045

theorem tailTrace_833654 : CollatzResearch.WordTrace tailWord_833654 prefixEnd_833654 190251200685949581596045 := by
  unfold tailWord_833654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900366207613838100819751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20270572881214273075410677 1900366207613838100819751)
  ·
    refine ⟨2850549311420757151229627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900366207613838100819751 2850549311420757151229627)
    ·
      refine ⟨4275823967131135726844441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850549311420757151229627 4275823967131135726844441)
      ·
        refine ⟨3206867975348351795133331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4275823967131135726844441 3206867975348351795133331)
        ·
          refine ⟨4810301963022527692699997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206867975348351795133331 4810301963022527692699997)
          ·
            refine ⟨1803863236133447884762499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4810301963022527692699997 1803863236133447884762499)
            ·
              refine ⟨2705794854200171827143749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803863236133447884762499 2705794854200171827143749)
              ·
                refine ⟨507336535162532217589453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2705794854200171827143749 507336535162532217589453)
                ·
                  refine ⟨190251200685949581596045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507336535162532217589453 190251200685949581596045)
                  ·
                    rfl

theorem cell21_833654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_833654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833654 prefixEnd_833654 := by exact prefixLift 833654
  have htrace : WordTrace (prefixWord ++ tailWord_833654) baseStart_833654 baseEnd_833654 := by
    simpa [prefixWord, tailWord_833654, baseEnd_833654] using wordTrace_append hprefix tailTrace_833654
  have hstable : (prefixWord ++ tailWord_833654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833654).length < 2 ^ (prefixWord ++ tailWord_833654).sum := by decide
  have hdescent : baseEnd_833654 < baseStart_833654 := by decide
  rcases family_descends (prefixWord ++ tailWord_833654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833682 : List Nat := [3, 2, 3, 1, 1, 1, 5, 5]
def baseStart_833682 : Nat := 118140960795 + 833682 * 2 ^ 59
def prefixEnd_833682 : Nat := 4983230072969 + 3 ^ 40 * 833682 * 2
def baseEnd_833682 : Nat := 63419196889142585043107

theorem tailTrace_833682 : CollatzResearch.WordTrace tailWord_833682 prefixEnd_833682 63419196889142585043107 := by
  unfold tailWord_833682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601720141429992598783825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20271253710479980263423533 7601720141429992598783825)
  ·
    refine ⟨5701290106072494449087869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7601720141429992598783825 5701290106072494449087869)
    ·
      refine ⟨2137983789777185418407951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5701290106072494449087869 2137983789777185418407951)
      ·
        refine ⟨3206975684665778127611927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137983789777185418407951 3206975684665778127611927)
        ·
          refine ⟨4810463526998667191417891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206975684665778127611927 4810463526998667191417891)
          ·
            refine ⟨7215695290498000787126837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810463526998667191417891 7215695290498000787126837)
            ·
              refine ⟨676471433484187573793141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7215695290498000787126837 676471433484187573793141)
              ·
                refine ⟨63419196889142585043107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 676471433484187573793141 63419196889142585043107)
                ·
                  rfl

theorem cell21_833682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_833682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833682 prefixEnd_833682 := by exact prefixLift 833682
  have htrace : WordTrace (prefixWord ++ tailWord_833682) baseStart_833682 baseEnd_833682 := by
    simpa [prefixWord, tailWord_833682, baseEnd_833682] using wordTrace_append hprefix tailTrace_833682
  have hstable : (prefixWord ++ tailWord_833682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833682).length < 2 ^ (prefixWord ++ tailWord_833682).sum := by decide
  have hdescent : baseEnd_833682 < baseStart_833682 := by decide
  rcases family_descends (prefixWord ++ tailWord_833682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833713 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_833713 : Nat := 118140960795 + 833713 * 2 ^ 59
def prefixEnd_833713 : Nat := 4983230072969 + 3 ^ 40 * 833713 * 2
def baseEnd_833713 : Nat := 190264665289778590112591

theorem tailTrace_833713 : CollatzResearch.WordTrace tailWord_833713 prefixEnd_833713 190264665289778590112591 := by
  unfold tailWord_833713
  simp only [CollatzResearch.WordTrace]
  refine ⟨30408011228607662689513793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20272007485738441793009195 30408011228607662689513793)
  ·
    refine ⟨22806008421455747017135345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30408011228607662689513793 22806008421455747017135345)
    ·
      refine ⟨17104506316091810262851509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22806008421455747017135345 17104506316091810262851509)
      ·
        refine ⟨1603547467133607212142329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17104506316091810262851509 1603547467133607212142329)
        ·
          refine ⟨1202660600350205409106747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603547467133607212142329 1202660600350205409106747)
          ·
            refine ⟨1803990900525308113660121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202660600350205409106747 1803990900525308113660121)
            ·
              refine ⟨1352993175393981085245091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803990900525308113660121 1352993175393981085245091)
              ·
                refine ⟨2029489763090971627867637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352993175393981085245091 2029489763090971627867637)
                ·
                  refine ⟨190264665289778590112591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029489763090971627867637 190264665289778590112591)
                  ·
                    rfl

theorem cell21_833713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_833713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833713 prefixEnd_833713 := by exact prefixLift 833713
  have htrace : WordTrace (prefixWord ++ tailWord_833713) baseStart_833713 baseEnd_833713 := by
    simpa [prefixWord, tailWord_833713, baseEnd_833713] using wordTrace_append hprefix tailTrace_833713
  have hstable : (prefixWord ++ tailWord_833713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833713).length < 2 ^ (prefixWord ++ tailWord_833713).sum := by decide
  have hdescent : baseEnd_833713 < baseStart_833713 := by decide
  rcases family_descends (prefixWord ++ tailWord_833713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833730 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_833730 : Nat := 118140960795 + 833730 * 2 ^ 59
def prefixEnd_833730 : Nat := 4983230072969 + 3 ^ 40 * 833730 * 2
def baseEnd_833730 : Nat := 190268544921390338329223

theorem tailTrace_833730 : CollatzResearch.WordTrace tailWord_833730 prefixEnd_833730 190268544921390338329223 := by
  unfold tailWord_833730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602157817386518648220661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20272420846364049728588429 7602157817386518648220661)
  ·
    refine ⟨712702295379986123270687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7602157817386518648220661 712702295379986123270687)
    ·
      refine ⟨1069053443069979184906031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 712702295379986123270687 1069053443069979184906031)
      ·
        refine ⟨1603580164604968777359047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069053443069979184906031 1603580164604968777359047)
        ·
          refine ⟨2405370246907453166038571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603580164604968777359047 2405370246907453166038571)
          ·
            refine ⟨3608055370361179749057857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405370246907453166038571 3608055370361179749057857)
            ·
              refine ⟨2706041527770884811793393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608055370361179749057857 2706041527770884811793393)
              ·
                refine ⟨2029531145828163608845045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706041527770884811793393 2029531145828163608845045)
                ·
                  refine ⟨190268544921390338329223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2029531145828163608845045 190268544921390338329223)
                  ·
                    rfl

theorem cell21_833730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_833730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833730 prefixEnd_833730 := by exact prefixLift 833730
  have htrace : WordTrace (prefixWord ++ tailWord_833730) baseStart_833730 baseEnd_833730 := by
    simpa [prefixWord, tailWord_833730, baseEnd_833730] using wordTrace_append hprefix tailTrace_833730
  have hstable : (prefixWord ++ tailWord_833730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833730).length < 2 ^ (prefixWord ++ tailWord_833730).sum := by decide
  have hdescent : baseEnd_833730 < baseStart_833730 := by decide
  rcases family_descends (prefixWord ++ tailWord_833730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833896 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_833896 : Nat := 118140960795 + 833896 * 2 ^ 59
def prefixEnd_833896 : Nat := 4983230072969 + 3 ^ 40 * 833896 * 2
def baseEnd_833896 : Nat := 190306428383010938562217

theorem tailTrace_833896 : CollatzResearch.WordTrace tailWord_833896 prefixEnd_833896 190306428383010938562217 := by
  unfold tailWord_833896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15207342893472342471712771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20276457191296456628950361 15207342893472342471712771)
  ·
    refine ⟨22811014340208513707569157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15207342893472342471712771 22811014340208513707569157)
    ·
      refine ⟨4277065188789096320169217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22811014340208513707569157 4277065188789096320169217)
      ·
        refine ⟨3207798891591822240126913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277065188789096320169217 3207798891591822240126913)
        ·
          refine ⟨2405849168693866680095185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207798891591822240126913 2405849168693866680095185)
          ·
            refine ⟨1804386876520400010071389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2405849168693866680095185 1804386876520400010071389)
            ·
              refine ⟨676645078695150003776771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804386876520400010071389 676645078695150003776771)
              ·
                refine ⟨1014967618042725005665157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676645078695150003776771 1014967618042725005665157)
                ·
                  refine ⟨190306428383010938562217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1014967618042725005665157 190306428383010938562217)
                  ·
                    rfl

theorem cell21_833896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_833896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833896 prefixEnd_833896 := by exact prefixLift 833896
  have htrace : WordTrace (prefixWord ++ tailWord_833896) baseStart_833896 baseEnd_833896 := by
    simpa [prefixWord, tailWord_833896, baseEnd_833896] using wordTrace_append hprefix tailTrace_833896
  have hstable : (prefixWord ++ tailWord_833896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833896).length < 2 ^ (prefixWord ++ tailWord_833896).sum := by decide
  have hdescent : baseEnd_833896 < baseStart_833896 := by decide
  rcases family_descends (prefixWord ++ tailWord_833896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833952 : List Nat := [2, 1, 1, 4, 1, 3, 1, 8]
def baseStart_833952 : Nat := 118140960795 + 833952 * 2 ^ 59
def prefixEnd_833952 : Nat := 4983230072969 + 3 ^ 40 * 833952 * 2
def baseEnd_833952 : Nat := 63439736115322428542923

theorem tailTrace_833952 : CollatzResearch.WordTrace tailWord_833952 prefixEnd_833952 63439736115322428542923 := by
  unfold tailWord_833952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15208364137370903253732055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20277818849827871004976073 15208364137370903253732055)
  ·
    refine ⟨22812546206056354880598083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15208364137370903253732055 22812546206056354880598083)
    ·
      refine ⟨34218819309084532320897125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22812546206056354880598083 34218819309084532320897125)
      ·
        refine ⟨6416028620453349810168211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34218819309084532320897125 6416028620453349810168211)
        ·
          refine ⟨9624042930680024715252317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416028620453349810168211 9624042930680024715252317)
          ·
            refine ⟨3609016099005009268219619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9624042930680024715252317 3609016099005009268219619)
            ·
              refine ⟨5413524148507513902329429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609016099005009268219619 5413524148507513902329429)
              ·
                refine ⟨63439736115322428542923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5413524148507513902329429 63439736115322428542923)
                ·
                  rfl

theorem cell21_833952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_833952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833952 prefixEnd_833952 := by exact prefixLift 833952
  have htrace : WordTrace (prefixWord ++ tailWord_833952) baseStart_833952 baseEnd_833952 := by
    simpa [prefixWord, tailWord_833952, baseEnd_833952] using wordTrace_append hprefix tailTrace_833952
  have hstable : (prefixWord ++ tailWord_833952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833952).length < 2 ^ (prefixWord ++ tailWord_833952).sum := by decide
  have hdescent : baseEnd_833952 < baseStart_833952 := by decide
  rcases family_descends (prefixWord ++ tailWord_833952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833955 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 4]
def baseStart_833955 : Nat := 118140960795 + 833955 * 2 ^ 59
def prefixEnd_833955 : Nat := 4983230072969 + 3 ^ 40 * 833955 * 2
def baseEnd_833955 : Nat := 190319892986839947078763

theorem tailTrace_833955 : CollatzResearch.WordTrace tailWord_833955 prefixEnd_833955 190319892986839947078763 := by
  unfold tailWord_833955
  simp only [CollatzResearch.WordTrace]
  refine ⟨30416837693730938019823319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20277891795820625346548879 30416837693730938019823319)
  ·
    refine ⟨45625256540596407029734979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30416837693730938019823319 45625256540596407029734979)
    ·
      refine ⟨68437884810894610544602469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45625256540596407029734979 68437884810894610544602469)
      ·
        refine ⟨12832103402042739477112963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68437884810894610544602469 12832103402042739477112963)
        ·
          refine ⟨19248155103064109215669445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12832103402042739477112963 19248155103064109215669445)
          ·
            refine ⟨3609029081824520477938021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19248155103064109215669445 3609029081824520477938021)
            ·
              refine ⟨676692952842097589613379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3609029081824520477938021 676692952842097589613379)
              ·
                refine ⟨1015039429263146384420069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676692952842097589613379 1015039429263146384420069)
                ·
                  refine ⟨190319892986839947078763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015039429263146384420069 190319892986839947078763)
                  ·
                    rfl

theorem cell21_833955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4].length) (baseStart_833955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833955 prefixEnd_833955 := by exact prefixLift 833955
  have htrace : WordTrace (prefixWord ++ tailWord_833955) baseStart_833955 baseEnd_833955 := by
    simpa [prefixWord, tailWord_833955, baseEnd_833955] using wordTrace_append hprefix tailTrace_833955
  have hstable : (prefixWord ++ tailWord_833955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833955).length < 2 ^ (prefixWord ++ tailWord_833955).sum := by decide
  have hdescent : baseEnd_833955 < baseStart_833955 := by decide
  rcases family_descends (prefixWord ++ tailWord_833955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833986 : List Nat := [3, 5, 2, 11]
def baseStart_833986 : Nat := 118140960795 + 833986 * 2 ^ 59
def prefixEnd_833986 : Nat := 4983230072969 + 3 ^ 40 * 833986 * 2
def baseEnd_833986 : Nat := 783238549832060831531

theorem tailTrace_833986 : CollatzResearch.WordTrace tailWord_833986 prefixEnd_833986 783238549832060831531 := by
  unfold tailWord_833986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604492089154657578550453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20278645571079086876134541 7604492089154657578550453)
  ·
    refine ⟨712921133358249147989105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7604492089154657578550453 712921133358249147989105)
    ·
      refine ⟨534690850018686860991829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 712921133358249147989105 534690850018686860991829)
      ·
        refine ⟨783238549832060831531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 534690850018686860991829 783238549832060831531)
        ·
          rfl

theorem cell21_833986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 11].length) (baseStart_833986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_833986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_833986 prefixEnd_833986 := by exact prefixLift 833986
  have htrace : WordTrace (prefixWord ++ tailWord_833986) baseStart_833986 baseEnd_833986 := by
    simpa [prefixWord, tailWord_833986, baseEnd_833986] using wordTrace_append hprefix tailTrace_833986
  have hstable : (prefixWord ++ tailWord_833986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833986).length < 2 ^ (prefixWord ++ tailWord_833986).sum := by decide
  have hdescent : baseEnd_833986 < baseStart_833986 := by decide
  rcases family_descends (prefixWord ++ tailWord_833986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834034 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 3]
def baseStart_834034 : Nat := 118140960795 + 834034 * 2 ^ 59
def prefixEnd_834034 : Nat := 4983230072969 + 3 ^ 40 * 834034 * 2
def baseEnd_834034 : Nat := 190337921863153365261935

theorem tailTrace_834034 : CollatzResearch.WordTrace tailWord_834034 prefixEnd_834034 190337921863153365261935 := by
  unfold tailWord_834034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604929765111183627987289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20279812706963156341299437 7604929765111183627987289)
  ·
    refine ⟨5703697323833387720990467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7604929765111183627987289 5703697323833387720990467)
    ·
      refine ⟨8555545985750081581485701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703697323833387720990467 8555545985750081581485701)
      ·
        refine ⟨1604164872328140296528569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8555545985750081581485701 1604164872328140296528569)
        ·
          refine ⟨1203123654246105222396427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604164872328140296528569 1203123654246105222396427)
          ·
            refine ⟨1804685481369157833594641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203123654246105222396427 1804685481369157833594641)
            ·
              refine ⟨1353514111026868375195981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804685481369157833594641 1353514111026868375195981)
              ·
                refine ⟨507567791635075640698493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353514111026868375195981 507567791635075640698493)
                ·
                  refine ⟨190337921863153365261935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507567791635075640698493 190337921863153365261935)
                  ·
                    rfl

theorem cell21_834034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_834034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834034 prefixEnd_834034 := by exact prefixLift 834034
  have htrace : WordTrace (prefixWord ++ tailWord_834034) baseStart_834034 baseEnd_834034 := by
    simpa [prefixWord, tailWord_834034, baseEnd_834034] using wordTrace_append hprefix tailTrace_834034
  have hstable : (prefixWord ++ tailWord_834034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834034).length < 2 ^ (prefixWord ++ tailWord_834034).sum := by decide
  have hdescent : baseEnd_834034 < baseStart_834034 := by decide
  rcases family_descends (prefixWord ++ tailWord_834034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834059 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_834059 : Nat := 118140960795 + 834059 * 2 ^ 59
def prefixEnd_834059 : Nat := 4983230072969 + 3 ^ 40 * 834059 * 2
def baseEnd_834059 : Nat := 190343627203758877345217

theorem tailTrace_834059 : CollatzResearch.WordTrace tailWord_834059 prefixEnd_834059 190343627203758877345217 := by
  unfold tailWord_834059
  simp only [CollatzResearch.WordTrace]
  refine ⟨30420630885354163781609231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20280420590236109187739487 30420630885354163781609231)
  ·
    refine ⟨45630946328031245672413847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30420630885354163781609231 45630946328031245672413847)
    ·
      refine ⟨68446419492046868508620771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45630946328031245672413847 68446419492046868508620771)
      ·
        refine ⟨102669629238070302762931157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68446419492046868508620771 102669629238070302762931157)
        ·
          refine ⟨2406319435267272721006199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 102669629238070302762931157 2406319435267272721006199)
          ·
            refine ⟨3609479152900909081509299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406319435267272721006199 3609479152900909081509299)
            ·
              refine ⟨5414218729351363622263949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609479152900909081509299 5414218729351363622263949)
              ·
                refine ⟨2030332023506761358348981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5414218729351363622263949 2030332023506761358348981)
                ·
                  refine ⟨190343627203758877345217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2030332023506761358348981 190343627203758877345217)
                  ·
                    rfl

theorem cell21_834059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_834059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834059 prefixEnd_834059 := by exact prefixLift 834059
  have htrace : WordTrace (prefixWord ++ tailWord_834059) baseStart_834059 baseEnd_834059 := by
    simpa [prefixWord, tailWord_834059, baseEnd_834059] using wordTrace_append hprefix tailTrace_834059
  have hstable : (prefixWord ++ tailWord_834059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834059).length < 2 ^ (prefixWord ++ tailWord_834059).sum := by decide
  have hdescent : baseEnd_834059 < baseStart_834059 := by decide
  rcases family_descends (prefixWord ++ tailWord_834059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834090 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_834090 : Nat := 118140960795 + 834090 * 2 ^ 59
def prefixEnd_834090 : Nat := 4983230072969 + 3 ^ 40 * 834090 * 2
def baseEnd_834090 : Nat := 190350701826109712328487

theorem tailTrace_834090 : CollatzResearch.WordTrace tailWord_834090 prefixEnd_834090 190350701826109712328487 := by
  unfold tailWord_834090
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605440387060464018996931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20281174365494570717325149 7605440387060464018996931)
  ·
    refine ⟨11408160580590696028495397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7605440387060464018996931 11408160580590696028495397)
    ·
      refine ⟨2139030108860755505342887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11408160580590696028495397 2139030108860755505342887)
      ·
        refine ⟨3208545163291133258014331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139030108860755505342887 3208545163291133258014331)
        ·
          refine ⟨4812817744936699887021497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208545163291133258014331 4812817744936699887021497)
          ·
            refine ⟨3609613308702524915266123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812817744936699887021497 3609613308702524915266123)
            ·
              refine ⟨5414419963053787372899185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609613308702524915266123 5414419963053787372899185)
              ·
                refine ⟨4060814972290340529674389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5414419963053787372899185 4060814972290340529674389)
                ·
                  refine ⟨190350701826109712328487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4060814972290340529674389 190350701826109712328487)
                  ·
                    rfl

theorem cell21_834090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_834090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834090 prefixEnd_834090 := by exact prefixLift 834090
  have htrace : WordTrace (prefixWord ++ tailWord_834090) baseStart_834090 baseEnd_834090 := by
    simpa [prefixWord, tailWord_834090, baseEnd_834090] using wordTrace_append hprefix tailTrace_834090
  have hstable : (prefixWord ++ tailWord_834090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834090).length < 2 ^ (prefixWord ++ tailWord_834090).sum := by decide
  have hdescent : baseEnd_834090 < baseStart_834090 := by decide
  rcases family_descends (prefixWord ++ tailWord_834090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834110 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_834110 : Nat := 118140960795 + 834110 * 2 ^ 59
def prefixEnd_834110 : Nat := 4983230072969 + 3 ^ 40 * 834110 * 2
def baseEnd_834110 : Nat := 190355266098594121995113

theorem tailTrace_834110 : CollatzResearch.WordTrace tailWord_834110 prefixEnd_834110 190355266098594121995113 := by
  unfold tailWord_834110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802811376021174936464473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20281660672112932994477189 3802811376021174936464473)
  ·
    refine ⟨2852108532015881202348355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3802811376021174936464473 2852108532015881202348355)
    ·
      refine ⟨4278162798023821803522533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852108532015881202348355 4278162798023821803522533)
      ·
        refine ⟨802155524629466588160475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4278162798023821803522533 802155524629466588160475)
        ·
          refine ⟨1203233286944199882240713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802155524629466588160475 1203233286944199882240713)
          ·
            refine ⟨902424965208149911680535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203233286944199882240713 902424965208149911680535)
            ·
              refine ⟨1353637447812224867520803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902424965208149911680535 1353637447812224867520803)
              ·
                refine ⟨2030456171718337301281205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353637447812224867520803 2030456171718337301281205)
                ·
                  refine ⟨190355266098594121995113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2030456171718337301281205 190355266098594121995113)
                  ·
                    rfl

theorem cell21_834110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_834110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834110 prefixEnd_834110 := by exact prefixLift 834110
  have htrace : WordTrace (prefixWord ++ tailWord_834110) baseStart_834110 baseEnd_834110 := by
    simpa [prefixWord, tailWord_834110, baseEnd_834110] using wordTrace_append hprefix tailTrace_834110
  have hstable : (prefixWord ++ tailWord_834110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834110).length < 2 ^ (prefixWord ++ tailWord_834110).sum := by decide
  have hdescent : baseEnd_834110 < baseStart_834110 := by decide
  rcases family_descends (prefixWord ++ tailWord_834110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834169 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 3]
def baseStart_834169 : Nat := 118140960795 + 834169 * 2 ^ 59
def prefixEnd_834169 : Nat := 4983230072969 + 3 ^ 40 * 834169 * 2
def baseEnd_834169 : Nat := 190368730702423130511659

theorem tailTrace_834169 : CollatzResearch.WordTrace tailWord_834169 prefixEnd_834169 190368730702423130511659 := by
  unfold tailWord_834169
  simp only [CollatzResearch.WordTrace]
  refine ⟨30424642914955652568113561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20283095276637101712075707 30424642914955652568113561)
  ·
    refine ⟨22818482186216739426085171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30424642914955652568113561 22818482186216739426085171)
    ·
      refine ⟨34227723279325109139127757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22818482186216739426085171 34227723279325109139127757)
      ·
        refine ⟨12835396229746915927172909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34227723279325109139127757 12835396229746915927172909)
        ·
          refine ⟨4813273586155093472689841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12835396229746915927172909 4813273586155093472689841)
          ·
            refine ⟨3609955189616320104517381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813273586155093472689841 3609955189616320104517381)
            ·
              refine ⟨676866598053060019597009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3609955189616320104517381 676866598053060019597009)
              ·
                refine ⟨507649948539795014697757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676866598053060019597009 507649948539795014697757)
                ·
                  refine ⟨190368730702423130511659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507649948539795014697757 190368730702423130511659)
                  ·
                    rfl

theorem cell21_834169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 3].length) (baseStart_834169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834169 prefixEnd_834169 := by exact prefixLift 834169
  have htrace : WordTrace (prefixWord ++ tailWord_834169) baseStart_834169 baseEnd_834169 := by
    simpa [prefixWord, tailWord_834169, baseEnd_834169] using wordTrace_append hprefix tailTrace_834169
  have hstable : (prefixWord ++ tailWord_834169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834169).length < 2 ^ (prefixWord ++ tailWord_834169).sum := by decide
  have hdescent : baseEnd_834169 < baseStart_834169 := by decide
  rcases family_descends (prefixWord ++ tailWord_834169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834287 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_834287 : Nat := 118140960795 + 834287 * 2 ^ 59
def prefixEnd_834287 : Nat := 4983230072969 + 3 ^ 40 * 834287 * 2
def baseEnd_834287 : Nat := 190395659910081147544751

theorem tailTrace_834287 : CollatzResearch.WordTrace tailWord_834287 prefixEnd_834287 190395659910081147544751 := by
  unfold tailWord_834287
  simp only [CollatzResearch.WordTrace]
  refine ⟨30428946728528158720909115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20285964485685439147272743 30428946728528158720909115)
  ·
    refine ⟨45643420092792238081363673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30428946728528158720909115 45643420092792238081363673)
    ·
      refine ⟨34232565069594178561022755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45643420092792238081363673 34232565069594178561022755)
      ·
        refine ⟨51348847604391267841534133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34232565069594178561022755 51348847604391267841534133)
        ·
          refine ⟨4813954462911681360143825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51348847604391267841534133 4813954462911681360143825)
          ·
            refine ⟨3610465847183761020107869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4813954462911681360143825 3610465847183761020107869)
            ·
              refine ⟨1353924692693910382540451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610465847183761020107869 1353924692693910382540451)
              ·
                refine ⟨2030887039040865573810677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353924692693910382540451 2030887039040865573810677)
                ·
                  refine ⟨190395659910081147544751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2030887039040865573810677 190395659910081147544751)
                  ·
                    rfl

theorem cell21_834287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_834287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834287 prefixEnd_834287 := by exact prefixLift 834287
  have htrace : WordTrace (prefixWord ++ tailWord_834287) baseStart_834287 baseEnd_834287 := by
    simpa [prefixWord, tailWord_834287, baseEnd_834287] using wordTrace_append hprefix tailTrace_834287
  have hstable : (prefixWord ++ tailWord_834287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834287).length < 2 ^ (prefixWord ++ tailWord_834287).sum := by decide
  have hdescent : baseEnd_834287 < baseStart_834287 := by decide
  rcases family_descends (prefixWord ++ tailWord_834287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834293 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 4]
def baseStart_834293 : Nat := 118140960795 + 834293 * 2 ^ 59
def prefixEnd_834293 : Nat := 4983230072969 + 3 ^ 40 * 834293 * 2
def baseEnd_834293 : Nat := 190397029191826470444739

theorem tailTrace_834293 : CollatzResearch.WordTrace tailWord_834293 prefixEnd_834293 190397029191826470444739 := by
  unfold tailWord_834293
  simp only [CollatzResearch.WordTrace]
  refine ⟨30429165566506421745627533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20286110377670947830418355 30429165566506421745627533)
  ·
    refine ⟨11410937087439908154610325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30429165566506421745627533 11410937087439908154610325)
    ·
      refine ⟨534887675973745694747359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11410937087439908154610325 534887675973745694747359)
      ·
        refine ⟨802331513960618542121039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534887675973745694747359 802331513960618542121039)
        ·
          refine ⟨1203497270940927813181559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802331513960618542121039 1203497270940927813181559)
          ·
            refine ⟨1805245906411391719772339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203497270940927813181559 1805245906411391719772339)
            ·
              refine ⟨2707868859617087579658509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1805245906411391719772339 2707868859617087579658509)
              ·
                refine ⟨1015450822356407842371941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2707868859617087579658509 1015450822356407842371941)
                ·
                  refine ⟨190397029191826470444739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015450822356407842371941 190397029191826470444739)
                  ·
                    rfl

theorem cell21_834293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_834293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834293 prefixEnd_834293 := by exact prefixLift 834293
  have htrace : WordTrace (prefixWord ++ tailWord_834293) baseStart_834293 baseEnd_834293 := by
    simpa [prefixWord, tailWord_834293, baseEnd_834293] using wordTrace_append hprefix tailTrace_834293
  have hstable : (prefixWord ++ tailWord_834293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834293).length < 2 ^ (prefixWord ++ tailWord_834293).sum := by decide
  have hdescent : baseEnd_834293 < baseStart_834293 := by decide
  rcases family_descends (prefixWord ++ tailWord_834293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834338 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_834338 : Nat := 118140960795 + 834338 * 2 ^ 59
def prefixEnd_834338 : Nat := 4983230072969 + 3 ^ 40 * 834338 * 2
def baseEnd_834338 : Nat := 190407298804916392194647

theorem tailTrace_834338 : CollatzResearch.WordTrace tailWord_834338 prefixEnd_834338 190407298804916392194647 := by
  unfold tailWord_834338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7607701712835848607753917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20287204567562262954010445 7607701712835848607753917)
  ·
    refine ⟨2852888142313443227907719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7607701712835848607753917 2852888142313443227907719)
    ·
      refine ⟨4279332213470164841861579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852888142313443227907719 4279332213470164841861579)
      ·
        refine ⟨6418998320205247262792369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4279332213470164841861579 6418998320205247262792369)
        ·
          refine ⟨4814248740153935447094277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418998320205247262792369 4814248740153935447094277)
          ·
            refine ⟨902671638778862896330177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4814248740153935447094277 902671638778862896330177)
            ·
              refine ⟨677003729084147172247633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902671638778862896330177 677003729084147172247633)
              ·
                refine ⟨507752796813110379185725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677003729084147172247633 507752796813110379185725)
                ·
                  refine ⟨190407298804916392194647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507752796813110379185725 190407298804916392194647)
                  ·
                    rfl

theorem cell21_834338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_834338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834338 prefixEnd_834338 := by exact prefixLift 834338
  have htrace : WordTrace (prefixWord ++ tailWord_834338) baseStart_834338 baseEnd_834338 := by
    simpa [prefixWord, tailWord_834338, baseEnd_834338] using wordTrace_append hprefix tailTrace_834338
  have hstable : (prefixWord ++ tailWord_834338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834338).length < 2 ^ (prefixWord ++ tailWord_834338).sum := by decide
  have hdescent : baseEnd_834338 < baseStart_834338 := by decide
  rcases family_descends (prefixWord ++ tailWord_834338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834366 : List Nat := [4, 2, 1, 2, 3, 1, 3, 5]
def baseStart_834366 : Nat := 118140960795 + 834366 * 2 ^ 59
def prefixEnd_834366 : Nat := 4983230072969 + 3 ^ 40 * 834366 * 2
def baseEnd_834366 : Nat := 63471229595464855242641

theorem tailTrace_834366 : CollatzResearch.WordTrace tailWord_834366 prefixEnd_834366 63471229595464855242641 := by
  unfold tailWord_834366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3803978511905244401629369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20287885396827970142023301 3803978511905244401629369)
  ·
    refine ⟨2852983883928933301222027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3803978511905244401629369 2852983883928933301222027)
    ·
      refine ⟨4279475825893399951833041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852983883928933301222027 4279475825893399951833041)
      ·
        refine ⟨3209606869420049963874781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4279475825893399951833041 3209606869420049963874781)
        ·
          refine ⟨1203602576032518736453043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3209606869420049963874781 1203602576032518736453043)
          ·
            refine ⟨1805403864048778104679565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203602576032518736453043 1805403864048778104679565)
            ·
              refine ⟨677026449018291789254837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1805403864048778104679565 677026449018291789254837)
              ·
                refine ⟨63471229595464855242641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677026449018291789254837 63471229595464855242641)
                ·
                  rfl

theorem cell21_834366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_834366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834366 prefixEnd_834366 := by exact prefixLift 834366
  have htrace : WordTrace (prefixWord ++ tailWord_834366) baseStart_834366 baseEnd_834366 := by
    simpa [prefixWord, tailWord_834366, baseEnd_834366] using wordTrace_append hprefix tailTrace_834366
  have hstable : (prefixWord ++ tailWord_834366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834366).length < 2 ^ (prefixWord ++ tailWord_834366).sum := by decide
  have hdescent : baseEnd_834366 < baseStart_834366 := by decide
  rcases family_descends (prefixWord ++ tailWord_834366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834380 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 3]
def baseStart_834380 : Nat := 118140960795 + 834380 * 2 ^ 59
def prefixEnd_834380 : Nat := 4983230072969 + 3 ^ 40 * 834380 * 2
def baseEnd_834380 : Nat := 190416883777133652494561

theorem tailTrace_834380 : CollatzResearch.WordTrace tailWord_834380 prefixEnd_834380 190416883777133652494561 := by
  unfold tailWord_834380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15216169358595617802022297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20288225811460823736029729 15216169358595617802022297)
  ·
    refine ⟨11412127018946713351516723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15216169358595617802022297 11412127018946713351516723)
    ·
      refine ⟨17118190528420070027275085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11412127018946713351516723 17118190528420070027275085)
      ·
        refine ⟨6419321448157526260228157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17118190528420070027275085 6419321448157526260228157)
        ·
          refine ⟨2407245543059072347585559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6419321448157526260228157 2407245543059072347585559)
          ·
            refine ⟨3610868314588608521378339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407245543059072347585559 3610868314588608521378339)
            ·
              refine ⟨5416302471882912782067509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610868314588608521378339 5416302471882912782067509)
              ·
                refine ⟨507778356739023073318829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5416302471882912782067509 507778356739023073318829)
                ·
                  refine ⟨190416883777133652494561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507778356739023073318829 190416883777133652494561)
                  ·
                    rfl

theorem cell21_834380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_834380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834380 prefixEnd_834380 := by exact prefixLift 834380
  have htrace : WordTrace (prefixWord ++ tailWord_834380) baseStart_834380 baseEnd_834380 := by
    simpa [prefixWord, tailWord_834380, baseEnd_834380] using wordTrace_append hprefix tailTrace_834380
  have hstable : (prefixWord ++ tailWord_834380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834380).length < 2 ^ (prefixWord ++ tailWord_834380).sum := by decide
  have hdescent : baseEnd_834380 < baseStart_834380 := by decide
  rcases family_descends (prefixWord ++ tailWord_834380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834394 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_834394 : Nat := 118140960795 + 834394 * 2 ^ 59
def prefixEnd_834394 : Nat := 4983230072969 + 3 ^ 40 * 834394 * 2
def baseEnd_834394 : Nat := 190420078767872739261199

theorem tailTrace_834394 : CollatzResearch.WordTrace tailWord_834394 prefixEnd_834394 190420078767872739261199 := by
  unfold tailWord_834394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608212334785128998763559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20288566226093677330036157 7608212334785128998763559)
  ·
    refine ⟨11412318502177693498145339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7608212334785128998763559 11412318502177693498145339)
    ·
      refine ⟨17118477753266540247218009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11412318502177693498145339 17118477753266540247218009)
      ·
        refine ⟨12838858314949905185413507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17118477753266540247218009 12838858314949905185413507)
        ·
          refine ⟨19258287472424857778120261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12838858314949905185413507 19258287472424857778120261)
          ·
            refine ⟨3610928901079660833397549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19258287472424857778120261 3610928901079660833397549)
            ·
              refine ⟨1354098337904872812524081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3610928901079660833397549 1354098337904872812524081)
              ·
                refine ⟨1015573753428654609393061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354098337904872812524081 1015573753428654609393061)
                ·
                  refine ⟨190420078767872739261199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1015573753428654609393061 190420078767872739261199)
                  ·
                    rfl

theorem cell21_834394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_834394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834394 prefixEnd_834394 := by exact prefixLift 834394
  have htrace : WordTrace (prefixWord ++ tailWord_834394) baseStart_834394 baseEnd_834394 := by
    simpa [prefixWord, tailWord_834394, baseEnd_834394] using wordTrace_append hprefix tailTrace_834394
  have hstable : (prefixWord ++ tailWord_834394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834394).length < 2 ^ (prefixWord ++ tailWord_834394).sum := by decide
  have hdescent : baseEnd_834394 < baseStart_834394 := by decide
  rcases family_descends (prefixWord ++ tailWord_834394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834425 : List Nat := [1, 2, 1, 3, 2, 5, 2, 5]
def baseStart_834425 : Nat := 118140960795 + 834425 * 2 ^ 59
def prefixEnd_834425 : Nat := 4983230072969 + 3 ^ 40 * 834425 * 2
def baseEnd_834425 : Nat := 63475717796741191414823

theorem tailTrace_834425 : CollatzResearch.WordTrace tailWord_834425 prefixEnd_834425 63475717796741191414823 := by
  unfold tailWord_834425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30433980002028208289432729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20289320001352138859621819 30433980002028208289432729)
  ·
    refine ⟨22825485001521156217074547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30433980002028208289432729 22825485001521156217074547)
    ·
      refine ⟨34238227502281734325611821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22825485001521156217074547 34238227502281734325611821)
      ·
        refine ⟨12839335313355650372104433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34238227502281734325611821 12839335313355650372104433)
        ·
          refine ⟨9629501485016737779078325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12839335313355650372104433 9629501485016737779078325)
          ·
            refine ⟨902765764220319166788593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9629501485016737779078325 902765764220319166788593)
            ·
              refine ⟨677074323165239375091445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902765764220319166788593 677074323165239375091445)
              ·
                refine ⟨63475717796741191414823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677074323165239375091445 63475717796741191414823)
                ·
                  rfl

theorem cell21_834425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 5].length) (baseStart_834425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834425 prefixEnd_834425 := by exact prefixLift 834425
  have htrace : WordTrace (prefixWord ++ tailWord_834425) baseStart_834425 baseEnd_834425 := by
    simpa [prefixWord, tailWord_834425, baseEnd_834425] using wordTrace_append hprefix tailTrace_834425
  have hstable : (prefixWord ++ tailWord_834425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834425).length < 2 ^ (prefixWord ++ tailWord_834425).sum := by decide
  have hdescent : baseEnd_834425 < baseStart_834425 := by decide
  rcases family_descends (prefixWord ++ tailWord_834425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834453 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_834453 : Nat := 118140960795 + 834453 * 2 ^ 59
def prefixEnd_834453 : Nat := 4983230072969 + 3 ^ 40 * 834453 * 2
def baseEnd_834453 : Nat := 190433543371701747777745

theorem tailTrace_834453 : CollatzResearch.WordTrace tailWord_834453 prefixEnd_834453 190433543371701747777745 := by
  unfold tailWord_834453
  simp only [CollatzResearch.WordTrace]
  refine ⟨30435001245926769071452013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20290000830617846047634675 30435001245926769071452013)
  ·
    refine ⟨11413125467222538401794505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30435001245926769071452013 11413125467222538401794505)
    ·
      refine ⟨8559844100416903801345879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11413125467222538401794505 8559844100416903801345879)
      ·
        refine ⟨12839766150625355702018819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8559844100416903801345879 12839766150625355702018819)
        ·
          refine ⟨19259649225938033553028229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839766150625355702018819 19259649225938033553028229)
          ·
            refine ⟨3611184229863381291192793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19259649225938033553028229 3611184229863381291192793)
            ·
              refine ⟨2708388172397535968394595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611184229863381291192793 2708388172397535968394595)
              ·
                refine ⟨4062582258596303952591893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708388172397535968394595 4062582258596303952591893)
                ·
                  refine ⟨190433543371701747777745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4062582258596303952591893 190433543371701747777745)
                  ·
                    rfl

theorem cell21_834453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_834453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834453 prefixEnd_834453 := by exact prefixLift 834453
  have htrace : WordTrace (prefixWord ++ tailWord_834453) baseStart_834453 baseEnd_834453 := by
    simpa [prefixWord, tailWord_834453, baseEnd_834453] using wordTrace_append hprefix tailTrace_834453
  have hstable : (prefixWord ++ tailWord_834453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834453).length < 2 ^ (prefixWord ++ tailWord_834453).sum := by decide
  have hdescent : baseEnd_834453 < baseStart_834453 := by decide
  rcases family_descends (prefixWord ++ tailWord_834453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834467 : List Nat := [1, 1, 1, 4, 1, 2, 3, 8]
def baseStart_834467 : Nat := 118140960795 + 834467 * 2 ^ 59
def prefixEnd_834467 : Nat := 4983230072969 + 3 ^ 40 * 834467 * 2
def baseEnd_834467 : Nat := 63478912787480278181461

theorem tailTrace_834467 : CollatzResearch.WordTrace tailWord_834467 prefixEnd_834467 63478912787480278181461 := by
  unfold tailWord_834467
  simp only [CollatzResearch.WordTrace]
  refine ⟨30435511867876049462461655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20290341245250699641641103 30435511867876049462461655)
  ·
    refine ⟨45653267801814074193692483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30435511867876049462461655 45653267801814074193692483)
    ·
      refine ⟨68479901702721111290538725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45653267801814074193692483 68479901702721111290538725)
      ·
        refine ⟨12839981569260208366976011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68479901702721111290538725 12839981569260208366976011)
        ·
          refine ⟨19259972353890312550464017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12839981569260208366976011 19259972353890312550464017)
          ·
            refine ⟨14444979265417734412848013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19259972353890312550464017 14444979265417734412848013)
            ·
              refine ⟨5416867224531650404818005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14444979265417734412848013 5416867224531650404818005)
              ·
                refine ⟨63478912787480278181461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5416867224531650404818005 63478912787480278181461)
                ·
                  rfl

theorem cell21_834467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_834467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834467 prefixEnd_834467 := by exact prefixLift 834467
  have htrace : WordTrace (prefixWord ++ tailWord_834467) baseStart_834467 baseEnd_834467 := by
    simpa [prefixWord, tailWord_834467, baseEnd_834467] using wordTrace_append hprefix tailTrace_834467
  have hstable : (prefixWord ++ tailWord_834467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834467).length < 2 ^ (prefixWord ++ tailWord_834467).sum := by decide
  have hdescent : baseEnd_834467 < baseStart_834467 := by decide
  rcases family_descends (prefixWord ++ tailWord_834467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834518 : List Nat := [5, 2, 1, 1, 2, 3, 1, 6]
def baseStart_834518 : Nat := 118140960795 + 834518 * 2 ^ 59
def prefixEnd_834518 : Nat := 4983230072969 + 3 ^ 40 * 834518 * 2
def baseEnd_834518 : Nat := 63482792419092026398093

theorem tailTrace_834518 : CollatzResearch.WordTrace tailWord_834518 prefixEnd_834518 63482792419092026398093 := by
  unfold tailWord_834518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902335749418205323285513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20291581327127523448378805 1902335749418205323285513)
  ·
    refine ⟨1426751812063653992464135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902335749418205323285513 1426751812063653992464135)
    ·
      refine ⟨2140127718095480988696203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426751812063653992464135 2140127718095480988696203)
      ·
        refine ⟨3210191577143221483044305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140127718095480988696203 3210191577143221483044305)
        ·
          refine ⟨2407643682857416112283229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210191577143221483044305 2407643682857416112283229)
          ·
            refine ⟨902866381071531042106211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407643682857416112283229 902866381071531042106211)
            ·
              refine ⟨1354299571607296563159317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902866381071531042106211 1354299571607296563159317)
              ·
                refine ⟨63482792419092026398093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1354299571607296563159317 63482792419092026398093)
                ·
                  rfl

theorem cell21_834518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_834518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834518 prefixEnd_834518 := by exact prefixLift 834518
  have htrace : WordTrace (prefixWord ++ tailWord_834518) baseStart_834518 baseEnd_834518 := by
    simpa [prefixWord, tailWord_834518, baseEnd_834518] using wordTrace_append hprefix tailTrace_834518
  have hstable : (prefixWord ++ tailWord_834518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834518).length < 2 ^ (prefixWord ++ tailWord_834518).sum := by decide
  have hdescent : baseEnd_834518 < baseStart_834518 := by decide
  rcases family_descends (prefixWord ++ tailWord_834518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834622 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_834622 : Nat := 118140960795 + 834622 * 2 ^ 59
def prefixEnd_834622 : Nat := 4983230072969 + 3 ^ 40 * 834622 * 2
def baseEnd_834622 : Nat := 190472111474195009460733

theorem tailTrace_834622 : CollatzResearch.WordTrace tailWord_834622 prefixEnd_834622 190472111474195009460733 := by
  unfold tailWord_834622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805145647789313866794265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20294110121543007289569413 3805145647789313866794265)
  ·
    refine ⟨2853859235841985400095699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3805145647789313866794265 2853859235841985400095699)
    ·
      refine ⟨4280788853762978100143549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853859235841985400095699 4280788853762978100143549)
      ·
        refine ⟨1605295820161116787553831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4280788853762978100143549 1605295820161116787553831)
        ·
          refine ⟨2407943730241675181330747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605295820161116787553831 2407943730241675181330747)
          ·
            refine ⟨3611915595362512771996121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407943730241675181330747 3611915595362512771996121)
            ·
              refine ⟨2708936696521884578997091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3611915595362512771996121 2708936696521884578997091)
              ·
                refine ⟨4063405044782826868495637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2708936696521884578997091 4063405044782826868495637)
                ·
                  refine ⟨190472111474195009460733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4063405044782826868495637 190472111474195009460733)
                  ·
                    rfl

theorem cell21_834622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_834622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834622 prefixEnd_834622 := by exact prefixLift 834622
  have htrace : WordTrace (prefixWord ++ tailWord_834622) baseStart_834622 baseEnd_834622 := by
    simpa [prefixWord, tailWord_834622, baseEnd_834622] using wordTrace_append hprefix tailTrace_834622
  have hstable : (prefixWord ++ tailWord_834622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834622).length < 2 ^ (prefixWord ++ tailWord_834622).sum := by decide
  have hdescent : baseEnd_834622 < baseStart_834622 := by decide
  rcases family_descends (prefixWord ++ tailWord_834622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834625 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 5]
def baseStart_834625 : Nat := 118140960795 + 834625 * 2 ^ 59
def prefixEnd_834625 : Nat := 4983230072969 + 3 ^ 40 * 834625 * 2
def baseEnd_834625 : Nat := 190472796115067670910727

theorem tailTrace_834625 : CollatzResearch.WordTrace tailWord_834625 prefixEnd_834625 190472796115067670910727 := by
  unfold tailWord_834625
  simp only [CollatzResearch.WordTrace]
  refine ⟨30441274601303642446713329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20294183067535761631142219 30441274601303642446713329)
  ·
    refine ⟨22830955950977731835034997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30441274601303642446713329 22830955950977731835034997)
    ·
      refine ⟨2140402120404162359534531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22830955950977731835034997 2140402120404162359534531)
      ·
        refine ⟨3210603180606243539301797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140402120404162359534531 3210603180606243539301797)
        ·
          refine ⟨601988096363670663619087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3210603180606243539301797 601988096363670663619087)
          ·
            refine ⟨902982144545505995428631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601988096363670663619087 902982144545505995428631)
            ·
              refine ⟨1354473216818258993142947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902982144545505995428631 1354473216818258993142947)
              ·
                refine ⟨2031709825227388489714421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354473216818258993142947 2031709825227388489714421)
                ·
                  refine ⟨190472796115067670910727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2031709825227388489714421 190472796115067670910727)
                  ·
                    rfl

theorem cell21_834625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 5].length) (baseStart_834625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834625 prefixEnd_834625 := by exact prefixLift 834625
  have htrace : WordTrace (prefixWord ++ tailWord_834625) baseStart_834625 baseEnd_834625 := by
    simpa [prefixWord, tailWord_834625, baseEnd_834625] using wordTrace_append hprefix tailTrace_834625
  have hstable : (prefixWord ++ tailWord_834625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834625).length < 2 ^ (prefixWord ++ tailWord_834625).sum := by decide
  have hdescent : baseEnd_834625 < baseStart_834625 := by decide
  rcases family_descends (prefixWord ++ tailWord_834625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834743 : List Nat := [1, 1, 3, 1, 4, 1, 1, 6, 3]
def baseStart_834743 : Nat := 118140960795 + 834743 * 2 ^ 59
def prefixEnd_834743 : Nat := 4983230072969 + 3 ^ 40 * 834743 * 2
def baseEnd_834743 : Nat := 190499725322725687943819

theorem tailTrace_834743 : CollatzResearch.WordTrace tailWord_834743 prefixEnd_834743 190499725322725687943819 := by
  unfold tailWord_834743
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445578414876148599508883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20297052276584099066339255 30445578414876148599508883)
  ·
    refine ⟨45668367622314222899263325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30445578414876148599508883 45668367622314222899263325)
    ·
      refine ⟨17125637858367833587223747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45668367622314222899263325 17125637858367833587223747)
      ·
        refine ⟨25688456787551750380835621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17125637858367833587223747 25688456787551750380835621)
        ·
          refine ⟨4816585647665953196406679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25688456787551750380835621 4816585647665953196406679)
          ·
            refine ⟨7224878471498929794610019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816585647665953196406679 7224878471498929794610019)
            ·
              refine ⟨10837317707248394691915029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7224878471498929794610019 10837317707248394691915029)
              ·
                refine ⟨507999267527268501183517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10837317707248394691915029 507999267527268501183517)
                ·
                  refine ⟨190499725322725687943819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507999267527268501183517 190499725322725687943819)
                  ·
                    rfl

theorem cell21_834743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3].length) (baseStart_834743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834743 prefixEnd_834743 := by exact prefixLift 834743
  have htrace : WordTrace (prefixWord ++ tailWord_834743) baseStart_834743 baseEnd_834743 := by
    simpa [prefixWord, tailWord_834743, baseEnd_834743] using wordTrace_append hprefix tailTrace_834743
  have hstable : (prefixWord ++ tailWord_834743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834743).length < 2 ^ (prefixWord ++ tailWord_834743).sum := by decide
  have hdescent : baseEnd_834743 < baseStart_834743 := by decide
  rcases family_descends (prefixWord ++ tailWord_834743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834847 : List Nat := [1, 1, 2, 4, 4, 9]
def baseStart_834847 : Nat := 118140960795 + 834847 * 2 ^ 59
def prefixEnd_834847 : Nat := 4983230072969 + 3 ^ 40 * 834847 * 2
def baseEnd_834847 : Nat := 7056424427394245118899

theorem tailTrace_834847 : CollatzResearch.WordTrace tailWord_834847 prefixEnd_834847 7056424427394245118899 := by
  unfold tailWord_834847
  simp only [CollatzResearch.WordTrace]
  refine ⟨30449371606499374361294795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20299581070999582907529863 30449371606499374361294795)
  ·
    refine ⟨45674057409749061541942193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30449371606499374361294795 45674057409749061541942193)
    ·
      refine ⟨34255543057311796156456645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45674057409749061541942193 34255543057311796156456645)
      ·
        refine ⟨6422914323245961779335621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34255543057311796156456645 6422914323245961779335621)
        ·
          refine ⟨1204296435608617833625429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6422914323245961779335621 1204296435608617833625429)
          ·
            refine ⟨7056424427394245118899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1204296435608617833625429 7056424427394245118899)
            ·
              rfl

theorem cell21_834847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 9].length) (baseStart_834847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834847 prefixEnd_834847 := by exact prefixLift 834847
  have htrace : WordTrace (prefixWord ++ tailWord_834847) baseStart_834847 baseEnd_834847 := by
    simpa [prefixWord, tailWord_834847, baseEnd_834847] using wordTrace_append hprefix tailTrace_834847
  have hstable : (prefixWord ++ tailWord_834847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834847).length < 2 ^ (prefixWord ++ tailWord_834847).sum := by decide
  have hdescent : baseEnd_834847 < baseStart_834847 := by decide
  rcases family_descends (prefixWord ++ tailWord_834847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834853 : List Nat := [1, 3, 1, 2, 4, 3, 2, 2, 3]
def baseStart_834853 : Nat := 118140960795 + 834853 * 2 ^ 59
def prefixEnd_834853 : Nat := 4983230072969 + 3 ^ 40 * 834853 * 2
def baseEnd_834853 : Nat := 190524828821389941110261

theorem tailTrace_834853 : CollatzResearch.WordTrace tailWord_834853 prefixEnd_834853 190524828821389941110261 := by
  unfold tailWord_834853
  simp only [CollatzResearch.WordTrace]
  refine ⟨30449590444477637386013213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20299726962985091590675475 30449590444477637386013213)
  ·
    refine ⟨11418596416679114019754955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30449590444477637386013213 11418596416679114019754955)
    ·
      refine ⟨17127894625018671029632433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11418596416679114019754955 17127894625018671029632433)
      ·
        refine ⟨12845920968764003272224325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17127894625018671029632433 12845920968764003272224325)
        ·
          refine ⟨2408610181643250613542061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12845920968764003272224325 2408610181643250613542061)
          ·
            refine ⟨903228818116218980078273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2408610181643250613542061 903228818116218980078273)
            ·
              refine ⟨677421613587164235058705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903228818116218980078273 677421613587164235058705)
              ·
                refine ⟨508066210190373176294029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677421613587164235058705 508066210190373176294029)
                ·
                  refine ⟨190524828821389941110261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508066210190373176294029 190524828821389941110261)
                  ·
                    rfl

theorem cell21_834853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_834853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834853 prefixEnd_834853 := by exact prefixLift 834853
  have htrace : WordTrace (prefixWord ++ tailWord_834853) baseStart_834853 baseEnd_834853 := by
    simpa [prefixWord, tailWord_834853, baseEnd_834853] using wordTrace_append hprefix tailTrace_834853
  have hstable : (prefixWord ++ tailWord_834853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834853).length < 2 ^ (prefixWord ++ tailWord_834853).sum := by decide
  have hdescent : baseEnd_834853 < baseStart_834853 := by decide
  rcases family_descends (prefixWord ++ tailWord_834853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834881 : List Nat := [1, 2, 5, 2, 1, 2, 3, 5]
def baseStart_834881 : Nat := 118140960795 + 834881 * 2 ^ 59
def prefixEnd_834881 : Nat := 4983230072969 + 3 ^ 40 * 834881 * 2
def baseEnd_834881 : Nat := 63510406267622704881179

theorem tailTrace_834881 : CollatzResearch.WordTrace tailWord_834881 prefixEnd_834881 63510406267622704881179 := by
  unfold tailWord_834881
  simp only [CollatzResearch.WordTrace]
  refine ⟨30450611688376198168032497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20300407792250798778688331 30450611688376198168032497)
  ·
    refine ⟨22837958766282148626024373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30450611688376198168032497 22837958766282148626024373)
    ·
      refine ⟨2141058634338951433689785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22837958766282148626024373 2141058634338951433689785)
      ·
        refine ⟨1605793975754213575267339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141058634338951433689785 1605793975754213575267339)
        ·
          refine ⟨2408690963631320362901009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605793975754213575267339 2408690963631320362901009)
          ·
            refine ⟨1806518222723490272175757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408690963631320362901009 1806518222723490272175757)
            ·
              refine ⟨677444333521308852065909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1806518222723490272175757 677444333521308852065909)
              ·
                refine ⟨63510406267622704881179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 677444333521308852065909 63510406267622704881179)
                ·
                  rfl

theorem cell21_834881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 5].length) (baseStart_834881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834881 prefixEnd_834881 := by exact prefixLift 834881
  have htrace : WordTrace (prefixWord ++ tailWord_834881) baseStart_834881 baseEnd_834881 := by
    simpa [prefixWord, tailWord_834881, baseEnd_834881] using wordTrace_append hprefix tailTrace_834881
  have hstable : (prefixWord ++ tailWord_834881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834881).length < 2 ^ (prefixWord ++ tailWord_834881).sum := by decide
  have hdescent : baseEnd_834881 < baseStart_834881 := by decide
  rcases family_descends (prefixWord ++ tailWord_834881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_834946 : List Nat := [3, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_834946 : Nat := 118140960795 + 834946 * 2 ^ 59
def prefixEnd_834946 : Nat := 4983230072969 + 3 ^ 40 * 834946 * 2
def baseEnd_834946 : Nat := 190546052688442446060071

theorem tailTrace_834946 : CollatzResearch.WordTrace tailWord_834946 prefixEnd_834946 190546052688442446060071 := by
  unfold tailWord_834946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7613245608285178567287173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20301988288760476179432461 7613245608285178567287173)
  ·
    refine ⟨1427483551553470981366345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7613245608285178567287173 1427483551553470981366345)
    ·
      refine ⟨1070612663665103236024759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427483551553470981366345 1070612663665103236024759)
      ·
        refine ⟨1605918995497654854037139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070612663665103236024759 1605918995497654854037139)
        ·
          refine ⟨2408878493246482281055709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1605918995497654854037139 2408878493246482281055709)
          ·
            refine ⟨903329434967430855395891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2408878493246482281055709 903329434967430855395891)
            ·
              refine ⟨1354994152451146283093837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903329434967430855395891 1354994152451146283093837)
              ·
                refine ⟨508122807169179856160189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354994152451146283093837 508122807169179856160189)
                ·
                  refine ⟨190546052688442446060071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508122807169179856160189 190546052688442446060071)
                  ·
                    rfl

theorem cell21_834946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_834946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_834946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_834946 prefixEnd_834946 := by exact prefixLift 834946
  have htrace : WordTrace (prefixWord ++ tailWord_834946) baseStart_834946 baseEnd_834946 := by
    simpa [prefixWord, tailWord_834946, baseEnd_834946] using wordTrace_append hprefix tailTrace_834946
  have hstable : (prefixWord ++ tailWord_834946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_834946).length < 2 ^ (prefixWord ++ tailWord_834946).sum := by decide
  have hdescent : baseEnd_834946 < baseStart_834946 := by decide
  rcases family_descends (prefixWord ++ tailWord_834946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835106 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_835106 : Nat := 118140960795 + 835106 * 2 ^ 59
def prefixEnd_835106 : Nat := 4983230072969 + 3 ^ 40 * 835106 * 2
def baseEnd_835106 : Nat := 190582566868317723393077

theorem tailTrace_835106 : CollatzResearch.WordTrace tailWord_835106 prefixEnd_835106 190582566868317723393077 := by
  unfold tailWord_835106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614704528140265398743293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20305878741707374396648781 7614704528140265398743293)
  ·
    refine ⟨2855514198052599524528735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7614704528140265398743293 2855514198052599524528735)
    ·
      refine ⟨4283271297078899286793103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855514198052599524528735 4283271297078899286793103)
      ·
        refine ⟨6424906945618348930189655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283271297078899286793103 6424906945618348930189655)
        ·
          refine ⟨9637360418427523395284483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424906945618348930189655 9637360418427523395284483)
          ·
            refine ⟨14456040627641285092926725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637360418427523395284483 14456040627641285092926725)
            ·
              refine ⟨2710507617682740954923761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14456040627641285092926725 2710507617682740954923761)
              ·
                refine ⟨2032880713262055716192821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2710507617682740954923761 2032880713262055716192821)
                ·
                  refine ⟨190582566868317723393077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2032880713262055716192821 190582566868317723393077)
                  ·
                    rfl

theorem cell21_835106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_835106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835106 prefixEnd_835106 := by exact prefixLift 835106
  have htrace : WordTrace (prefixWord ++ tailWord_835106) baseStart_835106 baseEnd_835106 := by
    simpa [prefixWord, tailWord_835106, baseEnd_835106] using wordTrace_append hprefix tailTrace_835106
  have hstable : (prefixWord ++ tailWord_835106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835106).length < 2 ^ (prefixWord ++ tailWord_835106).sum := by decide
  have hdescent : baseEnd_835106 < baseStart_835106 := by decide
  rcases family_descends (prefixWord ++ tailWord_835106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835123 : List Nat := [1, 1, 1, 2, 4, 3, 3, 3, 3]
def baseStart_835123 : Nat := 118140960795 + 835123 * 2 ^ 59
def prefixEnd_835123 : Nat := 4983230072969 + 3 ^ 40 * 835123 * 2
def baseEnd_835123 : Nat := 190586446499929471609709

theorem tailTrace_835123 : CollatzResearch.WordTrace tailWord_835123 prefixEnd_835123 190586446499929471609709 := by
  unfold tailWord_835123
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459438153499473498342023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20306292102332982332228015 30459438153499473498342023)
  ·
    refine ⟨45689157230249210247513035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30459438153499473498342023 45689157230249210247513035)
    ·
      refine ⟨68533735845373815371269553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45689157230249210247513035 68533735845373815371269553)
      ·
        refine ⟨51400301884030361528452165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68533735845373815371269553 51400301884030361528452165)
        ·
          refine ⟨9637556603255692786584781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51400301884030361528452165 9637556603255692786584781)
          ·
            refine ⟨3614083726220884794969293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9637556603255692786584781 3614083726220884794969293)
            ·
              refine ⟨1355281397332831798113485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3614083726220884794969293 1355281397332831798113485)
              ·
                refine ⟨508230523999811924292557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355281397332831798113485 508230523999811924292557)
                ·
                  refine ⟨190586446499929471609709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508230523999811924292557 190586446499929471609709)
                  ·
                    rfl

theorem cell21_835123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 3, 3].length) (baseStart_835123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835123 prefixEnd_835123 := by exact prefixLift 835123
  have htrace : WordTrace (prefixWord ++ tailWord_835123) baseStart_835123 baseEnd_835123 := by
    simpa [prefixWord, tailWord_835123, baseEnd_835123] using wordTrace_append hprefix tailTrace_835123
  have hstable : (prefixWord ++ tailWord_835123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835123).length < 2 ^ (prefixWord ++ tailWord_835123).sum := by decide
  have hdescent : baseEnd_835123 < baseStart_835123 := by decide
  rcases family_descends (prefixWord ++ tailWord_835123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835137 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_835137 : Nat := 118140960795 + 835137 * 2 ^ 59
def prefixEnd_835137 : Nat := 4983230072969 + 3 ^ 40 * 835137 * 2
def baseEnd_835137 : Nat := 190589641490668558376347

theorem tailTrace_835137 : CollatzResearch.WordTrace tailWord_835137 prefixEnd_835137 190589641490668558376347 := by
  unfold tailWord_835137
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459948775448753889351665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20306632516965835926234443 30459948775448753889351665)
  ·
    refine ⟨22844961581586565417013749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30459948775448753889351665 22844961581586565417013749)
    ·
      refine ⟨2141715148273740507845039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22844961581586565417013749 2141715148273740507845039)
      ·
        refine ⟨3212572722410610761767559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2141715148273740507845039 3212572722410610761767559)
        ·
          refine ⟨4818859083615916142651339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212572722410610761767559 4818859083615916142651339)
          ·
            refine ⟨7228288625423874213977009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818859083615916142651339 7228288625423874213977009)
            ·
              refine ⟨5421216469067905660482757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7228288625423874213977009 5421216469067905660482757)
              ·
                refine ⟨1016478087950232311340517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5421216469067905660482757 1016478087950232311340517)
                ·
                  refine ⟨190589641490668558376347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016478087950232311340517 190589641490668558376347)
                  ·
                    rfl

theorem cell21_835137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_835137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835137 prefixEnd_835137 := by exact prefixLift 835137
  have htrace : WordTrace (prefixWord ++ tailWord_835137) baseStart_835137 baseEnd_835137 := by
    simpa [prefixWord, tailWord_835137, baseEnd_835137] using wordTrace_append hprefix tailTrace_835137
  have hstable : (prefixWord ++ tailWord_835137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835137).length < 2 ^ (prefixWord ++ tailWord_835137).sum := by decide
  have hdescent : baseEnd_835137 < baseStart_835137 := by decide
  rcases family_descends (prefixWord ++ tailWord_835137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835154 : List Nat := [3, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_835154 : Nat := 118140960795 + 835154 * 2 ^ 59
def prefixEnd_835154 : Nat := 4983230072969 + 3 ^ 40 * 835154 * 2
def baseEnd_835154 : Nat := 190593521122280306592979

theorem tailTrace_835154 : CollatzResearch.WordTrace tailWord_835154 prefixEnd_835154 190593521122280306592979 := by
  unfold tailWord_835154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615142204096791448180129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20307045877591443861813677 7615142204096791448180129)
  ·
    refine ⟨5711356653072593586135097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7615142204096791448180129 5711356653072593586135097)
    ·
      refine ⟨4283517489804445189601323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5711356653072593586135097 4283517489804445189601323)
      ·
        refine ⟨6425276234706667784401985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283517489804445189601323 6425276234706667784401985)
        ·
          refine ⟨4818957176030000838301489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425276234706667784401985 4818957176030000838301489)
          ·
            refine ⟨3614217882022500628726117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4818957176030000838301489 3614217882022500628726117)
            ·
              refine ⟨677665852879218867886147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3614217882022500628726117 677665852879218867886147)
              ·
                refine ⟨1016498779318828301829221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677665852879218867886147 1016498779318828301829221)
                ·
                  refine ⟨190593521122280306592979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016498779318828301829221 190593521122280306592979)
                  ·
                    rfl

theorem cell21_835154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_835154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835154 prefixEnd_835154 := by exact prefixLift 835154
  have htrace : WordTrace (prefixWord ++ tailWord_835154) baseStart_835154 baseEnd_835154 := by
    simpa [prefixWord, tailWord_835154, baseEnd_835154] using wordTrace_append hprefix tailTrace_835154
  have hstable : (prefixWord ++ tailWord_835154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835154).length < 2 ^ (prefixWord ++ tailWord_835154).sum := by decide
  have hdescent : baseEnd_835154 < baseStart_835154 := by decide
  rcases family_descends (prefixWord ++ tailWord_835154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835258 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_835258 : Nat := 118140960795 + 835258 * 2 ^ 59
def prefixEnd_835258 : Nat := 4983230072969 + 3 ^ 40 * 835258 * 2
def baseEnd_835258 : Nat := 190617255339199236859433

theorem tailTrace_835258 : CollatzResearch.WordTrace tailWord_835258 prefixEnd_835258 190617255339199236859433 := by
  unfold tailWord_835258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616090502002597888626607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20309574672006927703004285 7616090502002597888626607)
  ·
    refine ⟨11424135753003896832939911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616090502002597888626607 11424135753003896832939911)
    ·
      refine ⟨17136203629505845249409867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11424135753003896832939911 17136203629505845249409867)
      ·
        refine ⟨25704305444258767874114801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17136203629505845249409867 25704305444258767874114801)
        ·
          refine ⟨19278229083194075905586101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25704305444258767874114801 19278229083194075905586101)
          ·
            refine ⟨1807333976549444616148697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19278229083194075905586101 1807333976549444616148697)
            ·
              refine ⟨1355500482412083462111523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807333976549444616148697 1355500482412083462111523)
              ·
                refine ⟨2033250723618125193167285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355500482412083462111523 2033250723618125193167285)
                ·
                  refine ⟨190617255339199236859433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2033250723618125193167285 190617255339199236859433)
                  ·
                    rfl

theorem cell21_835258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_835258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835258 prefixEnd_835258 := by exact prefixLift 835258
  have htrace : WordTrace (prefixWord ++ tailWord_835258) baseStart_835258 baseEnd_835258 := by
    simpa [prefixWord, tailWord_835258, baseEnd_835258] using wordTrace_append hprefix tailTrace_835258
  have hstable : (prefixWord ++ tailWord_835258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835258).length < 2 ^ (prefixWord ++ tailWord_835258).sum := by decide
  have hdescent : baseEnd_835258 < baseStart_835258 := by decide
  rcases family_descends (prefixWord ++ tailWord_835258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835365 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 4]
def baseStart_835365 : Nat := 118140960795 + 835365 * 2 ^ 59
def prefixEnd_835365 : Nat := 4983230072969 + 3 ^ 40 * 835365 * 2
def baseEnd_835365 : Nat := 190641674196990828575881

theorem tailTrace_835365 : CollatzResearch.WordTrace tailWord_835365 prefixEnd_835365 190641674196990828575881 := by
  unfold tailWord_835365
  simp only [CollatzResearch.WordTrace]
  refine ⟨30468264618622748828651549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20312176412415165885767699 30468264618622748828651549)
  ·
    refine ⟨11425599231983530810744331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30468264618622748828651549 11425599231983530810744331)
    ·
      refine ⟨17138398847975296216116497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11425599231983530810744331 17138398847975296216116497)
      ·
        refine ⟨12853799135981472162087373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17138398847975296216116497 12853799135981472162087373)
        ·
          refine ⟨4820174675993052060782765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12853799135981472162087373 4820174675993052060782765)
          ·
            refine ⟨1807565503497394522793537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4820174675993052060782765 1807565503497394522793537)
            ·
              refine ⟨1355674127623045892095153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807565503497394522793537 1355674127623045892095153)
              ·
                refine ⟨1016755595717284419071365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355674127623045892095153 1016755595717284419071365)
                ·
                  refine ⟨190641674196990828575881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016755595717284419071365 190641674196990828575881)
                  ·
                    rfl

theorem cell21_835365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_835365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835365 prefixEnd_835365 := by exact prefixLift 835365
  have htrace : WordTrace (prefixWord ++ tailWord_835365) baseStart_835365 baseEnd_835365 := by
    simpa [prefixWord, tailWord_835365, baseEnd_835365] using wordTrace_append hprefix tailTrace_835365
  have hstable : (prefixWord ++ tailWord_835365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835365).length < 2 ^ (prefixWord ++ tailWord_835365).sum := by decide
  have hdescent : baseEnd_835365 < baseStart_835365 := by decide
  rcases family_descends (prefixWord ++ tailWord_835365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835368 : List Nat := [2, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_835368 : Nat := 118140960795 + 835368 * 2 ^ 59
def prefixEnd_835368 : Nat := 4983230072969 + 3 ^ 40 * 835368 * 2
def baseEnd_835368 : Nat := 190642358837863490025875

theorem tailTrace_835368 : CollatzResearch.WordTrace tailWord_835368 prefixEnd_835368 190642358837863490025875 := by
  unfold tailWord_835368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15234187018805940170505379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20312249358407920227340505 15234187018805940170505379)
  ·
    refine ⟨22851280528208910255758069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15234187018805940170505379 22851280528208910255758069)
    ·
      refine ⟨2142307549519585336477319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22851280528208910255758069 2142307549519585336477319)
      ·
        refine ⟨3213461324279378004715979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142307549519585336477319 3213461324279378004715979)
        ·
          refine ⟨4820191986419067007073969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213461324279378004715979 4820191986419067007073969)
          ·
            refine ⟨3615143989814300255305477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4820191986419067007073969 3615143989814300255305477)
            ·
              refine ⟨677839498090181297869777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3615143989814300255305477 677839498090181297869777)
              ·
                refine ⟨508379623567635973402333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677839498090181297869777 508379623567635973402333)
                ·
                  refine ⟨190642358837863490025875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508379623567635973402333 190642358837863490025875)
                  ·
                    rfl

theorem cell21_835368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_835368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835368 prefixEnd_835368 := by exact prefixLift 835368
  have htrace : WordTrace (prefixWord ++ tailWord_835368) baseStart_835368 baseEnd_835368 := by
    simpa [prefixWord, tailWord_835368, baseEnd_835368] using wordTrace_append hprefix tailTrace_835368
  have hstable : (prefixWord ++ tailWord_835368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835368).length < 2 ^ (prefixWord ++ tailWord_835368).sum := by decide
  have hdescent : baseEnd_835368 < baseStart_835368 := by decide
  rcases family_descends (prefixWord ++ tailWord_835368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835382 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_835382 : Nat := 118140960795 + 835382 * 2 ^ 59
def prefixEnd_835382 : Nat := 4983230072969 + 3 ^ 40 * 835382 * 2
def baseEnd_835382 : Nat := 190645553828602576792513

theorem tailTrace_835382 : CollatzResearch.WordTrace tailWord_835382 prefixEnd_835382 190645553828602576792513 := by
  unfold tailWord_835382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904305291222572545751275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20312589773040773821346933 1904305291222572545751275)
  ·
    refine ⟨2856457936833858818626913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1904305291222572545751275 2856457936833858818626913)
    ·
      refine ⟨2142343452625394113970185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2856457936833858818626913 2142343452625394113970185)
      ·
        refine ⟨1606757589469045585477639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142343452625394113970185 1606757589469045585477639)
        ·
          refine ⟨2410136384203568378216459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606757589469045585477639 2410136384203568378216459)
          ·
            refine ⟨3615204576305352567324689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410136384203568378216459 3615204576305352567324689)
            ·
              refine ⟨2711403432229014425493517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615204576305352567324689 2711403432229014425493517)
              ·
                refine ⟨1016776287085880409560069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2711403432229014425493517 1016776287085880409560069)
                ·
                  refine ⟨190645553828602576792513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1016776287085880409560069 190645553828602576792513)
                  ·
                    rfl

theorem cell21_835382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_835382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835382 prefixEnd_835382 := by exact prefixLift 835382
  have htrace : WordTrace (prefixWord ++ tailWord_835382) baseStart_835382 baseEnd_835382 := by
    simpa [prefixWord, tailWord_835382, baseEnd_835382] using wordTrace_append hprefix tailTrace_835382
  have hstable : (prefixWord ++ tailWord_835382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835382).length < 2 ^ (prefixWord ++ tailWord_835382).sum := by decide
  have hdescent : baseEnd_835382 < baseStart_835382 := by decide
  rcases family_descends (prefixWord ++ tailWord_835382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_835424 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 6]
def baseStart_835424 : Nat := 118140960795 + 835424 * 2 ^ 59
def prefixEnd_835424 : Nat := 4983230072969 + 3 ^ 40 * 835424 * 2
def baseEnd_835424 : Nat := 190655138800819837092427

theorem tailTrace_835424 : CollatzResearch.WordTrace tailWord_835424 prefixEnd_835424 190655138800819837092427 := by
  unfold tailWord_835424
  simp only [CollatzResearch.WordTrace]
  refine ⟨15235208262704500952524663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20313611016939334603366217 15235208262704500952524663)
  ·
    refine ⟨22852812394056751428786995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15235208262704500952524663 22852812394056751428786995)
    ·
      refine ⟨34279218591085127143180493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22852812394056751428786995 34279218591085127143180493)
      ·
        refine ⟨12854706971656922678692685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34279218591085127143180493 12854706971656922678692685)
        ·
          refine ⟨4820515114371346004509757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12854706971656922678692685 4820515114371346004509757)
          ·
            refine ⟨1807693167889254751691159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4820515114371346004509757 1807693167889254751691159)
            ·
              refine ⟨2711539751833882127536739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807693167889254751691159 2711539751833882127536739)
              ·
                refine ⟨4067309627750823191305109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711539751833882127536739 4067309627750823191305109)
                ·
                  refine ⟨190655138800819837092427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4067309627750823191305109 190655138800819837092427)
                  ·
                    rfl

theorem cell21_835424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 6].length) (baseStart_835424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_835424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_835424 prefixEnd_835424 := by exact prefixLift 835424
  have htrace : WordTrace (prefixWord ++ tailWord_835424) baseStart_835424 baseEnd_835424 := by
    simpa [prefixWord, tailWord_835424, baseEnd_835424] using wordTrace_append hprefix tailTrace_835424
  have hstable : (prefixWord ++ tailWord_835424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_835424).length < 2 ^ (prefixWord ++ tailWord_835424).sum := by decide
  have hdescent : baseEnd_835424 < baseStart_835424 := by decide
  rcases family_descends (prefixWord ++ tailWord_835424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
