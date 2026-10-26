import V185TrunkScan23Chunk1305

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7735493 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 3, 5]
def baseStart_7735493 : Nat := 118140960795 + 7735493 * 2 ^ 59
def prefixEnd_7735493 : Nat := 4983230072969 + 3 ^ 40 * 7735493 * 2
def baseEnd_7735493 : Nat := 1324008669496669527254207

theorem tailTrace_7735493 : CollatzResearch.WordTrace tailWord_7735493 prefixEnd_7735493 1324008669496669527254207 := by
  unfold tailWord_7735493
  simp only [CollatzResearch.WordTrace]
  refine ⟨282136608164637452870011133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188091072109758301913340755 282136608164637452870011133)
  ·
    refine ⟨105801228061739044826254175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282136608164637452870011133 105801228061739044826254175)
    ·
      refine ⟨158701842092608567239381263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105801228061739044826254175 158701842092608567239381263)
      ·
        refine ⟨238052763138912850859071895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158701842092608567239381263 238052763138912850859071895)
        ·
          refine ⟨357079144708369276288607843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238052763138912850859071895 357079144708369276288607843)
          ·
            refine ⟨535618717062553914432911765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357079144708369276288607843 535618717062553914432911765)
            ·
              refine ⟨25107127362307214739042739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535618717062553914432911765 25107127362307214739042739)
              ·
                refine ⟨37660691043460822108564109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25107127362307214739042739 37660691043460822108564109)
                ·
                  refine ⟨14122759141297808290711541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37660691043460822108564109 14122759141297808290711541)
                  ·
                    refine ⟨1324008669496669527254207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14122759141297808290711541 1324008669496669527254207)
                    ·
                      rfl

theorem cell23_7735493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_7735493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735493 prefixEnd_7735493 := by exact prefixLift 7735493
  have htrace : WordTrace (prefixWord ++ tailWord_7735493) baseStart_7735493 baseEnd_7735493 := by
    simpa [prefixWord, tailWord_7735493, baseEnd_7735493] using wordTrace_append hprefix tailTrace_7735493
  have hstable : (prefixWord ++ tailWord_7735493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735493).length < 2 ^ (prefixWord ++ tailWord_7735493).sum := by decide
  have hdescent : baseEnd_7735493 < baseStart_7735493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735550 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_7735550 : Nat := 118140960795 + 7735550 * 2 ^ 59
def prefixEnd_7735550 : Nat := 4983230072969 + 3 ^ 40 * 7735550 * 2
def baseEnd_7735550 : Nat := 3972055276887314858749859

theorem tailTrace_7735550 : CollatzResearch.WordTrace tailWord_7735550 prefixEnd_7735550 3972055276887314858749859 := by
  unfold tailWord_7735550
  simp only [CollatzResearch.WordTrace]
  refine ⟨35267335890678868950604513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188092458083620634403224069 35267335890678868950604513)
  ·
    refine ⟨26450501918009151712953385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35267335890678868950604513 26450501918009151712953385)
    ·
      refine ⟨19837876438506863784715039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26450501918009151712953385 19837876438506863784715039)
      ·
        refine ⟨29756814657760295677072559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19837876438506863784715039 29756814657760295677072559)
        ·
          refine ⟨44635221986640443515608839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29756814657760295677072559 44635221986640443515608839)
          ·
            refine ⟨66952832979960665273413259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44635221986640443515608839 66952832979960665273413259)
            ·
              refine ⟨100429249469940997910119889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66952832979960665273413259 100429249469940997910119889)
              ·
                refine ⟨75321937102455748432589917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100429249469940997910119889 75321937102455748432589917)
                ·
                  refine ⟨28245726413420905662221219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75321937102455748432589917 28245726413420905662221219)
                  ·
                    refine ⟨42368589620131358493331829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28245726413420905662221219 42368589620131358493331829)
                    ·
                      refine ⟨3972055276887314858749859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42368589620131358493331829 3972055276887314858749859)
                      ·
                        rfl

theorem cell23_7735550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_7735550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735550 prefixEnd_7735550 := by exact prefixLift 7735550
  have htrace : WordTrace (prefixWord ++ tailWord_7735550) baseStart_7735550 baseEnd_7735550 := by
    simpa [prefixWord, tailWord_7735550, baseEnd_7735550] using wordTrace_append hprefix tailTrace_7735550
  have hstable : (prefixWord ++ tailWord_7735550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735550).length < 2 ^ (prefixWord ++ tailWord_7735550).sum := by decide
  have hdescent : baseEnd_7735550 < baseStart_7735550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735553 : List Nat := [1, 2, 4, 1, 1, 2, 3, 9]
def baseStart_7735553 : Nat := 118140960795 + 7735553 * 2 ^ 59
def prefixEnd_7735553 : Nat := 4983230072969 + 3 ^ 40 * 7735553 * 2
def baseEnd_7735553 : Nat := 147113215456639938778235

theorem tailTrace_7735553 : CollatzResearch.WordTrace tailWord_7735553 prefixEnd_7735553 147113215456639938778235 := by
  unfold tailWord_7735553
  simp only [CollatzResearch.WordTrace]
  refine ⟨282138796544420083117195313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188092531029613388744796875 282138796544420083117195313)
  ·
    refine ⟨211604097408315062337896485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282138796544420083117195313 211604097408315062337896485)
    ·
      refine ⟨39675768264059074188355591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211604097408315062337896485 39675768264059074188355591)
      ·
        refine ⟨59513652396088611282533387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39675768264059074188355591 59513652396088611282533387)
        ·
          refine ⟨89270478594132916923800081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59513652396088611282533387 89270478594132916923800081)
          ·
            refine ⟨66952858945599687692850061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89270478594132916923800081 66952858945599687692850061)
            ·
              refine ⟨25107322104599882884818773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66952858945599687692850061 25107322104599882884818773)
              ·
                refine ⟨147113215456639938778235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25107322104599882884818773 147113215456639938778235)
                ·
                  rfl

theorem cell23_7735553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 9].length) (baseStart_7735553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735553 prefixEnd_7735553 := by exact prefixLift 7735553
  have htrace : WordTrace (prefixWord ++ tailWord_7735553) baseStart_7735553 baseEnd_7735553 := by
    simpa [prefixWord, tailWord_7735553, baseEnd_7735553] using wordTrace_append hprefix tailTrace_7735553
  have hstable : (prefixWord ++ tailWord_7735553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735553).length < 2 ^ (prefixWord ++ tailWord_7735553).sum := by decide
  have hdescent : baseEnd_7735553 < baseStart_7735553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735598 : List Nat := [4, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7735598 : Nat := 118140960795 + 7735598 * 2 ^ 59
def prefixEnd_7735598 : Nat := 4983230072969 + 3 ^ 40 * 7735598 * 2
def baseEnd_7735598 : Nat := 3972079923958730670949639

theorem tailTrace_7735598 : CollatzResearch.WordTrace tailWord_7735598 prefixEnd_7735598 3972079923958730670949639 := by
  unfold tailWord_7735598
  simp only [CollatzResearch.WordTrace]
  refine ⟨35267554728657131975322931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188093625219504703868388965 35267554728657131975322931)
  ·
    refine ⟨52901332092985697962984397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35267554728657131975322931 52901332092985697962984397)
    ·
      refine ⟨19837999534869636736119149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52901332092985697962984397 19837999534869636736119149)
      ·
        refine ⟨7439249825576113776044681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19837999534869636736119149 7439249825576113776044681)
        ·
          refine ⟨5579437369182085332033511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7439249825576113776044681 5579437369182085332033511)
          ·
            refine ⟨8369156053773127998050267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579437369182085332033511 8369156053773127998050267)
            ·
              refine ⟨12553734080659691997075401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369156053773127998050267 12553734080659691997075401)
              ·
                refine ⟨9415300560494768997806551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12553734080659691997075401 9415300560494768997806551)
                ·
                  refine ⟨14122950840742153496709827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9415300560494768997806551 14122950840742153496709827)
                  ·
                    refine ⟨21184426261113230245064741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14122950840742153496709827 21184426261113230245064741)
                    ·
                      refine ⟨3972079923958730670949639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21184426261113230245064741 3972079923958730670949639)
                      ·
                        rfl

theorem cell23_7735598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7735598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735598 prefixEnd_7735598 := by exact prefixLift 7735598
  have htrace : WordTrace (prefixWord ++ tailWord_7735598) baseStart_7735598 baseEnd_7735598 := by
    simpa [prefixWord, tailWord_7735598, baseEnd_7735598] using wordTrace_append hprefix tailTrace_7735598
  have hstable : (prefixWord ++ tailWord_7735598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735598).length < 2 ^ (prefixWord ++ tailWord_7735598).sum := by decide
  have hdescent : baseEnd_7735598 < baseStart_7735598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735601 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 1, 2, 3]
def baseStart_7735601 : Nat := 118140960795 + 7735601 * 2 ^ 59
def prefixEnd_7735601 : Nat := 4983230072969 + 3 ^ 40 * 7735601 * 2
def baseEnd_7735601 : Nat := 3972081464400694159212125

theorem tailTrace_7735601 : CollatzResearch.WordTrace tailWord_7735601 prefixEnd_7735601 3972081464400694159212125 := by
  unfold tailWord_7735601
  simp only [CollatzResearch.WordTrace]
  refine ⟨282140547248246187314942657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188093698165497458209961771 282140547248246187314942657)
  ·
    refine ⟨211605410436184640486206993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282140547248246187314942657 211605410436184640486206993)
    ·
      refine ⟨158704057827138480364655245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211605410436184640486206993 158704057827138480364655245)
      ·
        refine ⟨59514021685176930136745717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158704057827138480364655245 59514021685176930136745717)
        ·
          refine ⟨5579439532985337200319911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59514021685176930136745717 5579439532985337200319911)
          ·
            refine ⟨8369159299478005800479867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5579439532985337200319911 8369159299478005800479867)
            ·
              refine ⟨12553738949217008700719801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369159299478005800479867 12553738949217008700719801)
              ·
                refine ⟨9415304211912756525539851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12553738949217008700719801 9415304211912756525539851)
                ·
                  refine ⟨14122956317869134788309777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9415304211912756525539851 14122956317869134788309777)
                  ·
                    refine ⟨10592217238401851091232333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14122956317869134788309777 10592217238401851091232333)
                    ·
                      refine ⟨3972081464400694159212125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592217238401851091232333 3972081464400694159212125)
                      ·
                        rfl

theorem cell23_7735601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_7735601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735601 prefixEnd_7735601 := by exact prefixLift 7735601
  have htrace : WordTrace (prefixWord ++ tailWord_7735601) baseStart_7735601 baseEnd_7735601 := by
    simpa [prefixWord, tailWord_7735601, baseEnd_7735601] using wordTrace_append hprefix tailTrace_7735601
  have hstable : (prefixWord ++ tailWord_7735601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735601).length < 2 ^ (prefixWord ++ tailWord_7735601).sum := by decide
  have hdescent : baseEnd_7735601 < baseStart_7735601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735677 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 5]
def baseStart_7735677 : Nat := 118140960795 + 7735677 * 2 ^ 59
def prefixEnd_7735677 : Nat := 4983230072969 + 3 ^ 40 * 7735677 * 2
def baseEnd_7735677 : Nat := 441346720992270651317975

theorem tailTrace_7735677 : CollatzResearch.WordTrace tailWord_7735677 prefixEnd_7735677 441346720992270651317975 := by
  unfold tailWord_7735677
  simp only [CollatzResearch.WordTrace]
  refine ⟨282143319195970852294709285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188095546130647234863139523 282143319195970852294709285)
  ·
    refine ⟨52901872349244534805257991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282143319195970852294709285 52901872349244534805257991)
    ·
      refine ⟨79352808523866802207886987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52901872349244534805257991 79352808523866802207886987)
      ·
        refine ⟨119029212785800203311830481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79352808523866802207886987 119029212785800203311830481)
        ·
          refine ⟨89271909589350152483872861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119029212785800203311830481 89271909589350152483872861)
          ·
            refine ⟨33476966096006307181452323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89271909589350152483872861 33476966096006307181452323)
            ·
              refine ⟨50215449144009460772178485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33476966096006307181452323 50215449144009460772178485)
              ·
                refine ⟨4707698357250886947391733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50215449144009460772178485 4707698357250886947391733)
                ·
                  refine ⟨441346720992270651317975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707698357250886947391733 441346720992270651317975)
                  ·
                    rfl

theorem cell23_7735677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_7735677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735677 prefixEnd_7735677 := by exact prefixLift 7735677
  have htrace : WordTrace (prefixWord ++ tailWord_7735677) baseStart_7735677 baseEnd_7735677 := by
    simpa [prefixWord, tailWord_7735677, baseEnd_7735677] using wordTrace_append hprefix tailTrace_7735677
  have hstable : (prefixWord ++ tailWord_7735677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735677).length < 2 ^ (prefixWord ++ tailWord_7735677).sum := by decide
  have hdescent : baseEnd_7735677 < baseStart_7735677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735694 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_7735694 : Nat := 118140960795 + 7735694 * 2 ^ 59
def prefixEnd_7735694 : Nat := 4983230072969 + 3 ^ 40 * 7735694 * 2
def baseEnd_7735694 : Nat := 441347690900173588372133

theorem tailTrace_7735694 : CollatzResearch.WordTrace tailWord_7735694 prefixEnd_7735694 441347690900173588372133 := by
  unfold tailWord_7735694
  simp only [CollatzResearch.WordTrace]
  refine ⟨35267992404613658024759767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188095959491272842798718757 35267992404613658024759767)
  ·
    refine ⟨52901988606920487037139651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35267992404613658024759767 52901988606920487037139651)
    ·
      refine ⟨79352982910380730555709477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52901988606920487037139651 79352982910380730555709477)
      ·
        refine ⟨14878684295696386979195527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79352982910380730555709477 14878684295696386979195527)
        ·
          refine ⟨22318026443544580468793291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14878684295696386979195527 22318026443544580468793291)
          ·
            refine ⟨33477039665316870703189937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22318026443544580468793291 33477039665316870703189937)
            ·
              refine ⟨25107779748987653027392453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33477039665316870703189937 25107779748987653027392453)
              ·
                refine ⟨4707708702935184942636085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25107779748987653027392453 4707708702935184942636085)
                ·
                  refine ⟨441347690900173588372133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707708702935184942636085 441347690900173588372133)
                  ·
                    rfl

theorem cell23_7735694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_7735694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735694 prefixEnd_7735694 := by exact prefixLift 7735694
  have htrace : WordTrace (prefixWord ++ tailWord_7735694) baseStart_7735694 baseEnd_7735694 := by
    simpa [prefixWord, tailWord_7735694, baseEnd_7735694] using wordTrace_append hprefix tailTrace_7735694
  have hstable : (prefixWord ++ tailWord_7735694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735694).length < 2 ^ (prefixWord ++ tailWord_7735694).sum := by decide
  have hdescent : baseEnd_7735694 < baseStart_7735694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735745 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 5]
def baseStart_7735745 : Nat := 118140960795 + 7735745 * 2 ^ 59
def prefixEnd_7735745 : Nat := 4983230072969 + 3 ^ 40 * 7735745 * 2
def baseEnd_7735745 : Nat := 441350600623882399534607

theorem tailTrace_7735745 : CollatzResearch.WordTrace tailWord_7735745 prefixEnd_7735745 441350600623882399534607 := by
  unfold tailWord_7735745
  simp only [CollatzResearch.WordTrace]
  refine ⟨282145799359724499908184689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188097199573149666605456459 282145799359724499908184689)
  ·
    refine ⟨211609349519793374931138517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282145799359724499908184689 211609349519793374931138517)
    ·
      refine ⟨4959594129370157224948559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 211609349519793374931138517 4959594129370157224948559)
      ·
        refine ⟨7439391194055235837422839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4959594129370157224948559 7439391194055235837422839)
        ·
          refine ⟨11159086791082853756134259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439391194055235837422839 11159086791082853756134259)
          ·
            refine ⟨16738630186624280634201389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159086791082853756134259 16738630186624280634201389)
            ·
              refine ⟨6276986319984105237825521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16738630186624280634201389 6276986319984105237825521)
              ·
                refine ⟨4707739739988078928369141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6276986319984105237825521 4707739739988078928369141)
                ·
                  refine ⟨441350600623882399534607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4707739739988078928369141 441350600623882399534607)
                  ·
                    rfl

theorem cell23_7735745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 5].length) (baseStart_7735745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735745 prefixEnd_7735745 := by exact prefixLift 7735745
  have htrace : WordTrace (prefixWord ++ tailWord_7735745) baseStart_7735745 baseEnd_7735745 := by
    simpa [prefixWord, tailWord_7735745, baseEnd_7735745] using wordTrace_append hprefix tailTrace_7735745
  have hstable : (prefixWord ++ tailWord_7735745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735745).length < 2 ^ (prefixWord ++ tailWord_7735745).sum := by decide
  have hdescent : baseEnd_7735745 < baseStart_7735745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735778 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_7735778 : Nat := 118140960795 + 7735778 * 2 ^ 59
def prefixEnd_7735778 : Nat := 4983230072969 + 3 ^ 40 * 7735778 * 2
def baseEnd_7735778 : Nat := 3972172350476539966698811

theorem tailTrace_7735778 : CollatzResearch.WordTrace tailWord_7735778 prefixEnd_7735778 3972172350476539966698811 := by
  unfold tailWord_7735778
  simp only [CollatzResearch.WordTrace]
  refine ⟨70536750742151236636033997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188098001979069964362757325 70536750742151236636033997)
  ·
    refine ⟨26451281528306713738512749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70536750742151236636033997 26451281528306713738512749)
    ·
      refine ⟨9919230573115017651942281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26451281528306713738512749 9919230573115017651942281)
      ·
        refine ⟨7439422929836263238956711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9919230573115017651942281 7439422929836263238956711)
        ·
          refine ⟨11159134394754394858435067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439422929836263238956711 11159134394754394858435067)
          ·
            refine ⟨16738701592131592287652601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159134394754394858435067 16738701592131592287652601)
            ·
              refine ⟨12554026194098694215739451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16738701592131592287652601 12554026194098694215739451)
              ·
                refine ⟨18831039291148041323609177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554026194098694215739451 18831039291148041323609177)
                ·
                  refine ⟨14123279468361030992706883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18831039291148041323609177 14123279468361030992706883)
                  ·
                    refine ⟨21184919202541546489060325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14123279468361030992706883 21184919202541546489060325)
                    ·
                      refine ⟨3972172350476539966698811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21184919202541546489060325 3972172350476539966698811)
                      ·
                        rfl

theorem cell23_7735778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_7735778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735778 prefixEnd_7735778 := by exact prefixLift 7735778
  have htrace : WordTrace (prefixWord ++ tailWord_7735778) baseStart_7735778 baseEnd_7735778 := by
    simpa [prefixWord, tailWord_7735778, baseEnd_7735778] using wordTrace_append hprefix tailTrace_7735778
  have hstable : (prefixWord ++ tailWord_7735778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735778).length < 2 ^ (prefixWord ++ tailWord_7735778).sum := by decide
  have hdescent : baseEnd_7735778 < baseStart_7735778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735781 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7735781 : Nat := 118140960795 + 7735781 * 2 ^ 59
def prefixEnd_7735781 : Nat := 4983230072969 + 3 ^ 40 * 7735781 * 2
def baseEnd_7735781 : Nat := 3972173890918503454961297

theorem tailTrace_7735781 : CollatzResearch.WordTrace tailWord_7735781 prefixEnd_7735781 3972173890918503454961297 := by
  unfold tailWord_7735781
  simp only [CollatzResearch.WordTrace]
  refine ⟨282147112387594078056495197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188098074925062718704330131 282147112387594078056495197)
  ·
    refine ⟨105805167145347779271185699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282147112387594078056495197 105805167145347779271185699)
    ·
      refine ⟨158707750718021668906778549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105805167145347779271185699 158707750718021668906778549)
      ·
        refine ⟨14878851629814531460010489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158707750718021668906778549 14878851629814531460010489)
        ·
          refine ⟨11159138722360898595007867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14878851629814531460010489 11159138722360898595007867)
          ·
            refine ⟨16738708083541347892511801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159138722360898595007867 16738708083541347892511801)
            ·
              refine ⟨12554031062656010919383851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16738708083541347892511801 12554031062656010919383851)
              ·
                refine ⟨18831046593984016379075777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554031062656010919383851 18831046593984016379075777)
                ·
                  refine ⟨14123284945488012284306833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18831046593984016379075777 14123284945488012284306833)
                  ·
                    refine ⟨10592463709116009213230125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14123284945488012284306833 10592463709116009213230125)
                    ·
                      refine ⟨3972173890918503454961297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592463709116009213230125 3972173890918503454961297)
                      ·
                        rfl

theorem cell23_7735781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7735781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735781 prefixEnd_7735781 := by exact prefixLift 7735781
  have htrace : WordTrace (prefixWord ++ tailWord_7735781) baseStart_7735781 baseEnd_7735781 := by
    simpa [prefixWord, tailWord_7735781, baseEnd_7735781] using wordTrace_append hprefix tailTrace_7735781
  have hstable : (prefixWord ++ tailWord_7735781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735781).length < 2 ^ (prefixWord ++ tailWord_7735781).sum := by decide
  have hdescent : baseEnd_7735781 < baseStart_7735781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735811 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 1, 1, 3]
def baseStart_7735811 : Nat := 118140960795 + 7735811 * 2 ^ 59
def prefixEnd_7735811 : Nat := 4983230072969 + 3 ^ 40 * 7735811 * 2
def baseEnd_7735811 : Nat := 3972189295338138337586159

theorem tailTrace_7735811 : CollatzResearch.WordTrace tailWord_7735811 prefixEnd_7735811 3972189295338138337586159 := by
  unfold tailWord_7735811
  simp only [CollatzResearch.WordTrace]
  refine ⟨282148206577485393180087287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188098804384990262120058191 282148206577485393180087287)
  ·
    refine ⟨423222309866228089770130931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282148206577485393180087287 423222309866228089770130931)
    ·
      refine ⟨634833464799342134655196397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423222309866228089770130931 634833464799342134655196397)
      ·
        refine ⟨238062549299753300495698649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 634833464799342134655196397 238062549299753300495698649)
        ·
          refine ⟨178546911974814975371773987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238062549299753300495698649 178546911974814975371773987)
          ·
            refine ⟨267820367962222463057660981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178546911974814975371773987 267820367962222463057660981)
            ·
              refine ⟨25108159496458355911655717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267820367962222463057660981 25108159496458355911655717)
              ·
                refine ⟨4707779905585941733435447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25108159496458355911655717 4707779905585941733435447)
                ·
                  refine ⟨7061669858378912600153171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4707779905585941733435447 7061669858378912600153171)
                  ·
                    refine ⟨10592504787568368900229757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7061669858378912600153171 10592504787568368900229757)
                    ·
                      refine ⟨3972189295338138337586159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592504787568368900229757 3972189295338138337586159)
                      ·
                        rfl

theorem cell23_7735811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_7735811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735811 prefixEnd_7735811 := by exact prefixLift 7735811
  have htrace : WordTrace (prefixWord ++ tailWord_7735811) baseStart_7735811 baseEnd_7735811 := by
    simpa [prefixWord, tailWord_7735811, baseEnd_7735811] using wordTrace_append hprefix tailTrace_7735811
  have hstable : (prefixWord ++ tailWord_7735811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735811).length < 2 ^ (prefixWord ++ tailWord_7735811).sum := by decide
  have hdescent : baseEnd_7735811 < baseStart_7735811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735827 : List Nat := [1, 1, 1, 2, 1, 5, 4, 1, 1, 6]
def baseStart_7735827 : Nat := 118140960795 + 7735827 * 2 ^ 59
def prefixEnd_7735827 : Nat := 4983230072969 + 3 ^ 40 * 7735827 * 2
def baseEnd_7735827 : Nat := 1324065837009536758328695

theorem tailTrace_7735827 : CollatzResearch.WordTrace tailWord_7735827 prefixEnd_7735827 1324065837009536758328695 := by
  unfold tailWord_7735827
  simp only [CollatzResearch.WordTrace]
  refine ⟨282148790145427427912669735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188099193430284951941779823 282148790145427427912669735)
  ·
    refine ⟨423223185218141141869004603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282148790145427427912669735 423223185218141141869004603)
    ·
      refine ⟨634834777827211712803506905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423223185218141141869004603 634834777827211712803506905)
      ·
        refine ⟨476126083370408784602630179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634834777827211712803506905 476126083370408784602630179)
        ·
          refine ⟨714189125055613176903945269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476126083370408784602630179 714189125055613176903945269)
          ·
            refine ⟨66955230473963735334744869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 714189125055613176903945269 66955230473963735334744869)
            ·
              refine ⟨12554105713868200375264663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66955230473963735334744869 12554105713868200375264663)
              ·
                refine ⟨18831158570802300562896995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554105713868200375264663 18831158570802300562896995)
                ·
                  refine ⟨28246737856203450844345493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18831158570802300562896995 28246737856203450844345493)
                  ·
                    refine ⟨1324065837009536758328695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28246737856203450844345493 1324065837009536758328695)
                    ·
                      rfl

theorem cell23_7735827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 6].length) (baseStart_7735827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735827 prefixEnd_7735827 := by exact prefixLift 7735827
  have htrace : WordTrace (prefixWord ++ tailWord_7735827) baseStart_7735827 baseEnd_7735827 := by
    simpa [prefixWord, tailWord_7735827, baseEnd_7735827] using wordTrace_append hprefix tailTrace_7735827
  have hstable : (prefixWord ++ tailWord_7735827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735827).length < 2 ^ (prefixWord ++ tailWord_7735827).sum := by decide
  have hdescent : baseEnd_7735827 < baseStart_7735827 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735828 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_7735828 : Nat := 118140960795 + 7735828 * 2 ^ 59
def prefixEnd_7735828 : Nat := 4983230072969 + 3 ^ 40 * 7735828 * 2
def baseEnd_7735828 : Nat := 3972198024509264771073581

theorem tailTrace_7735828 : CollatzResearch.WordTrace tailWord_7735828 prefixEnd_7735828 3972198024509264771073581 := by
  unfold tailWord_7735828
  simp only [CollatzResearch.WordTrace]
  refine ⟨141074413309211902541728069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188099217745615870055637425 141074413309211902541728069)
  ·
    refine ⟨26451452495477231726574013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141074413309211902541728069 26451452495477231726574013)
    ·
      refine ⟨9919294685803961897465255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26451452495477231726574013 9919294685803961897465255)
      ·
        refine ⟨14878942028705942846197883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9919294685803961897465255 14878942028705942846197883)
        ·
          refine ⟨22318413043058914269296825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14878942028705942846197883 22318413043058914269296825)
          ·
            refine ⟨16738809782294185701972619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22318413043058914269296825 16738809782294185701972619)
            ·
              refine ⟨25108214673441278552958929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16738809782294185701972619 25108214673441278552958929)
              ·
                refine ⟨18831161005080958914719197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25108214673441278552958929 18831161005080958914719197)
                ·
                  refine ⟨7061685376905359593019699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18831161005080958914719197 7061685376905359593019699)
                  ·
                    refine ⟨10592528065358039389529549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7061685376905359593019699 10592528065358039389529549)
                    ·
                      refine ⟨3972198024509264771073581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592528065358039389529549 3972198024509264771073581)
                      ·
                        rfl

theorem cell23_7735828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_7735828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735828 prefixEnd_7735828 := by exact prefixLift 7735828
  have htrace : WordTrace (prefixWord ++ tailWord_7735828) baseStart_7735828 baseEnd_7735828 := by
    simpa [prefixWord, tailWord_7735828, baseEnd_7735828] using wordTrace_append hprefix tailTrace_7735828
  have hstable : (prefixWord ++ tailWord_7735828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735828).length < 2 ^ (prefixWord ++ tailWord_7735828).sum := by decide
  have hdescent : baseEnd_7735828 < baseStart_7735828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735848 : List Nat := [2, 1, 5, 2, 1, 3, 2, 1, 1, 5]
def baseStart_7735848 : Nat := 118140960795 + 7735848 * 2 ^ 59
def prefixEnd_7735848 : Nat := 4983230072969 + 3 ^ 40 * 7735848 * 2
def baseEnd_7735848 : Nat := 1324069431374118230941163

theorem tailTrace_7735848 : CollatzResearch.WordTrace tailWord_7735848 prefixEnd_7735848 1324069431374118230941163 := by
  unfold tailWord_7735848
  simp only [CollatzResearch.WordTrace]
  refine ⟨141074778039175674249592099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188099704052234232332789465 141074778039175674249592099)
  ·
    refine ⟨211612167058763511374388149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141074778039175674249592099 211612167058763511374388149)
    ·
      refine ⟨19838640661759079191348889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211612167058763511374388149 19838640661759079191348889)
      ·
        refine ⟨14878980496319309393511667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19838640661759079191348889 14878980496319309393511667)
        ·
          refine ⟨22318470744478964090267501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14878980496319309393511667 22318470744478964090267501)
          ·
            refine ⟨8369426529179611533850313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22318470744478964090267501 8369426529179611533850313)
            ·
              refine ⟨6277069896884708650387735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8369426529179611533850313 6277069896884708650387735)
              ·
                refine ⟨9415604845327062975581603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277069896884708650387735 9415604845327062975581603)
                ·
                  refine ⟨14123407267990594463372405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9415604845327062975581603 14123407267990594463372405)
                  ·
                    refine ⟨1324069431374118230941163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14123407267990594463372405 1324069431374118230941163)
                    ·
                      rfl

theorem cell23_7735848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_7735848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735848 prefixEnd_7735848 := by exact prefixLift 7735848
  have htrace : WordTrace (prefixWord ++ tailWord_7735848) baseStart_7735848 baseEnd_7735848 := by
    simpa [prefixWord, tailWord_7735848, baseEnd_7735848] using wordTrace_append hprefix tailTrace_7735848
  have hstable : (prefixWord ++ tailWord_7735848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735848).length < 2 ^ (prefixWord ++ tailWord_7735848).sum := by decide
  have hdescent : baseEnd_7735848 < baseStart_7735848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735868 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_7735868 : Nat := 118140960795 + 7735868 * 2 ^ 59
def prefixEnd_7735868 : Nat := 4983230072969 + 3 ^ 40 * 7735868 * 2
def baseEnd_7735868 : Nat := 3972218563735444614573397

theorem tailTrace_7735868 : CollatzResearch.WordTrace tailWord_7735868 prefixEnd_7735868 3972218563735444614573397 := by
  unfold tailWord_7735868
  simp only [CollatzResearch.WordTrace]
  refine ⟨141075142769139445957456129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188100190358852594609941505 141075142769139445957456129)
  ·
    refine ⟨105806357076854584468092097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141075142769139445957456129 105806357076854584468092097)
    ·
      refine ⟨79354767807640938351069073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105806357076854584468092097 79354767807640938351069073)
      ·
        refine ⟨59516075855730703763301805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79354767807640938351069073 59516075855730703763301805)
        ·
          refine ⟨22318528445899013911238177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59516075855730703763301805 22318528445899013911238177)
          ·
            refine ⟨16738896334424260433428633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22318528445899013911238177 16738896334424260433428633)
            ·
              refine ⟨12554172250818195325071475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16738896334424260433428633 12554172250818195325071475)
              ·
                refine ⟨18831258376227292987607213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554172250818195325071475 18831258376227292987607213)
                ·
                  refine ⟨7061721891085234870352705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18831258376227292987607213 7061721891085234870352705)
                  ·
                    refine ⟨5296291418313926152764529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7061721891085234870352705 5296291418313926152764529)
                    ·
                      refine ⟨3972218563735444614573397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296291418313926152764529 3972218563735444614573397)
                      ·
                        rfl

theorem cell23_7735868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_7735868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735868 prefixEnd_7735868 := by exact prefixLift 7735868
  have htrace : WordTrace (prefixWord ++ tailWord_7735868) baseStart_7735868 baseEnd_7735868 := by
    simpa [prefixWord, tailWord_7735868, baseEnd_7735868] using wordTrace_append hprefix tailTrace_7735868
  have hstable : (prefixWord ++ tailWord_7735868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735868).length < 2 ^ (prefixWord ++ tailWord_7735868).sum := by decide
  have hdescent : baseEnd_7735868 < baseStart_7735868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735878 : List Nat := [6, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_7735878 : Nat := 118140960795 + 7735878 * 2 ^ 59
def prefixEnd_7735878 : Nat := 4983230072969 + 3 ^ 40 * 7735878 * 2
def baseEnd_7735878 : Nat := 1324074566180663191816117

theorem tailTrace_7735878 : CollatzResearch.WordTrace tailWord_7735878 prefixEnd_7735878 1324074566180663191816117 := by
  unfold tailWord_7735878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8817207820882583238211759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188100433512161775748517525 8817207820882583238211759)
  ·
    refine ⟨13225811731323874857317639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8817207820882583238211759 13225811731323874857317639)
    ·
      refine ⟨19838717596985812285976459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13225811731323874857317639 19838717596985812285976459)
      ·
        refine ⟨29758076395478718428964689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19838717596985812285976459 29758076395478718428964689)
        ·
          refine ⟨22318557296609038821723517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29758076395478718428964689 22318557296609038821723517)
          ·
            refine ⟨8369458986228389558146319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22318557296609038821723517 8369458986228389558146319)
            ·
              refine ⟨12554188479342584337219479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8369458986228389558146319 12554188479342584337219479)
              ·
                refine ⟨18831282719013876505829219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554188479342584337219479 18831282719013876505829219)
                ·
                  refine ⟨28246924078520814758743829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18831282719013876505829219 28246924078520814758743829)
                  ·
                    refine ⟨1324074566180663191816117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28246924078520814758743829 1324074566180663191816117)
                    ·
                      rfl

theorem cell23_7735878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_7735878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735878 prefixEnd_7735878 := by exact prefixLift 7735878
  have htrace : WordTrace (prefixWord ++ tailWord_7735878) baseStart_7735878 baseEnd_7735878 := by
    simpa [prefixWord, tailWord_7735878, baseEnd_7735878] using wordTrace_append hprefix tailTrace_7735878
  have hstable : (prefixWord ++ tailWord_7735878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735878).length < 2 ^ (prefixWord ++ tailWord_7735878).sum := by decide
  have hdescent : baseEnd_7735878 < baseStart_7735878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735962 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7735962 : Nat := 118140960795 + 7735962 * 2 ^ 59
def prefixEnd_7735962 : Nat := 4983230072969 + 3 ^ 40 * 7735962 * 2
def baseEnd_7735962 : Nat := 3972266830916967246797965

theorem tailTrace_7735962 : CollatzResearch.WordTrace tailWord_7735962 prefixEnd_7735962 3972266830916967246797965 := by
  unfold tailWord_7735962
  simp only [CollatzResearch.WordTrace]
  refine ⟨70538428499984586492208535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188102475999958897312556093 70538428499984586492208535)
  ·
    refine ⟨105807642749976879738312803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70538428499984586492208535 105807642749976879738312803)
    ·
      refine ⟨158711464124965319607469205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105807642749976879738312803 158711464124965319607469205)
      ·
        refine ⟨7439599880857749356600119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 158711464124965319607469205 7439599880857749356600119)
        ·
          refine ⟨11159399821286624034900179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7439599880857749356600119 11159399821286624034900179)
          ·
            refine ⟨16739099731929936052350269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159399821286624034900179 16739099731929936052350269)
            ·
              refine ⟨6277162399473726019631351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16739099731929936052350269 6277162399473726019631351)
              ·
                refine ⟨9415743599210589029447027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277162399473726019631351 9415743599210589029447027)
                ·
                  refine ⟨14123615398815883544170541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9415743599210589029447027 14123615398815883544170541)
                  ·
                    refine ⟨5296355774555956329063953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14123615398815883544170541 5296355774555956329063953)
                    ·
                      refine ⟨3972266830916967246797965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296355774555956329063953 3972266830916967246797965)
                      ·
                        rfl

theorem cell23_7735962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7735962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735962 prefixEnd_7735962 := by exact prefixLift 7735962
  have htrace : WordTrace (prefixWord ++ tailWord_7735962) baseStart_7735962 baseEnd_7735962 := by
    simpa [prefixWord, tailWord_7735962, baseEnd_7735962] using wordTrace_append hprefix tailTrace_7735962
  have hstable : (prefixWord ++ tailWord_7735962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735962).length < 2 ^ (prefixWord ++ tailWord_7735962).sum := by decide
  have hdescent : baseEnd_7735962 < baseStart_7735962 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7735991 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_7735991 : Nat := 118140960795 + 7735991 * 2 ^ 59
def prefixEnd_7735991 : Nat := 4983230072969 + 3 ^ 40 * 7735991 * 2
def baseEnd_7735991 : Nat := 3972281721855947633335331

theorem tailTrace_7735991 : CollatzResearch.WordTrace tailWord_7735991 prefixEnd_7735991 3972281721855947633335331 := by
  unfold tailWord_7735991
  simp only [CollatzResearch.WordTrace]
  refine ⟨282154771716833283921639827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188103181144555522614426551 282154771716833283921639827)
  ·
    refine ⟨423232157575249925882459741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282154771716833283921639827 423232157575249925882459741)
    ·
      refine ⟨158712059090718722205922403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423232157575249925882459741 158712059090718722205922403)
      ·
        refine ⟨238068088636078083308883605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158712059090718722205922403 238068088636078083308883605)
        ·
          refine ⟨11159441654816160155103919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 238068088636078083308883605 11159441654816160155103919)
          ·
            refine ⟨16739162482224240232655879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11159441654816160155103919 16739162482224240232655879)
            ·
              refine ⟨25108743723336360348983819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16739162482224240232655879 25108743723336360348983819)
              ·
                refine ⟨37663115585004540523475729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25108743723336360348983819 37663115585004540523475729)
                ·
                  refine ⟨28247336688753405392606797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37663115585004540523475729 28247336688753405392606797)
                  ·
                    refine ⟨10592751258282527022227549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28247336688753405392606797 10592751258282527022227549)
                    ·
                      refine ⟨3972281721855947633335331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592751258282527022227549 3972281721855947633335331)
                      ·
                        rfl

theorem cell23_7735991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_7735991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7735991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7735991 prefixEnd_7735991 := by exact prefixLift 7735991
  have htrace : WordTrace (prefixWord ++ tailWord_7735991) baseStart_7735991 baseEnd_7735991 := by
    simpa [prefixWord, tailWord_7735991, baseEnd_7735991] using wordTrace_append hprefix tailTrace_7735991
  have hstable : (prefixWord ++ tailWord_7735991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7735991).length < 2 ^ (prefixWord ++ tailWord_7735991).sum := by decide
  have hdescent : baseEnd_7735991 < baseStart_7735991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7735991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736007 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 10]
def baseStart_7736007 : Nat := 118140960795 + 7736007 * 2 ^ 59
def prefixEnd_7736007 : Nat := 4983230072969 + 3 ^ 40 * 7736007 * 2
def baseEnd_7736007 : Nat := 1324096645848806523578419

theorem tailTrace_7736007 : CollatzResearch.WordTrace tailWord_7736007 prefixEnd_7736007 1324096645848806523578419 := by
  unfold tailWord_7736007
  simp only [CollatzResearch.WordTrace]
  refine ⟨282155355284775318654222275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188103570189850212436148183 282155355284775318654222275)
  ·
    refine ⟨423233032927162977981333413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282155355284775318654222275 423233032927162977981333413)
    ·
      refine ⟨79356193673843058371500015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423233032927162977981333413 79356193673843058371500015)
      ·
        refine ⟨119034290510764587557250023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79356193673843058371500015 119034290510764587557250023)
        ·
          refine ⟨178551435766146881335875035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119034290510764587557250023 178551435766146881335875035)
          ·
            refine ⟨267827153649220322003812553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178551435766146881335875035 267827153649220322003812553)
            ·
              refine ⟨200870365236915241502859415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267827153649220322003812553 200870365236915241502859415)
              ·
                refine ⟨301305547855372862254289123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200870365236915241502859415 301305547855372862254289123)
                ·
                  refine ⟨451958321783059293381433685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301305547855372862254289123 451958321783059293381433685)
                  ·
                    refine ⟨1324096645848806523578419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 451958321783059293381433685 1324096645848806523578419)
                    ·
                      rfl

theorem cell23_7736007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_7736007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736007 prefixEnd_7736007 := by exact prefixLift 7736007
  have htrace : WordTrace (prefixWord ++ tailWord_7736007) baseStart_7736007 baseEnd_7736007 := by
    simpa [prefixWord, tailWord_7736007, baseEnd_7736007] using wordTrace_append hprefix tailTrace_7736007
  have hstable : (prefixWord ++ tailWord_7736007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736007).length < 2 ^ (prefixWord ++ tailWord_7736007).sum := by decide
  have hdescent : baseEnd_7736007 < baseStart_7736007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736031 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 2, 4, 2]
def baseStart_7736031 : Nat := 118140960795 + 7736031 * 2 ^ 59
def prefixEnd_7736031 : Nat := 4983230072969 + 3 ^ 40 * 7736031 * 2
def baseEnd_7736031 : Nat := 3972302261082127476835147

theorem tailTrace_7736031 : CollatzResearch.WordTrace tailWord_7736031 prefixEnd_7736031 3972302261082127476835147 := by
  unfold tailWord_7736031
  simp only [CollatzResearch.WordTrace]
  refine ⟨282156230636688370753095947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188104153757792247168730631 282156230636688370753095947)
  ·
    refine ⟨423234345955032556129643921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282156230636688370753095947 423234345955032556129643921)
    ·
      refine ⟨317425759466274417097232941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423234345955032556129643921 317425759466274417097232941)
      ·
        refine ⟨119034659799852906411462353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317425759466274417097232941 119034659799852906411462353)
        ·
          refine ⟨89275994849889679808596765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119034659799852906411462353 89275994849889679808596765)
          ·
            refine ⟨33478498068708629928223787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89275994849889679808596765 33478498068708629928223787)
            ·
              refine ⟨50217747103062944892335681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33478498068708629928223787 50217747103062944892335681)
              ·
                refine ⟨37663310327297208669251761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50217747103062944892335681 37663310327297208669251761)
                ·
                  refine ⟨28247482745472906501938821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37663310327297208669251761 28247482745472906501938821)
                  ·
                    refine ⟨5296403014776169969113529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28247482745472906501938821 5296403014776169969113529)
                    ·
                      refine ⟨3972302261082127476835147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296403014776169969113529 3972302261082127476835147)
                      ·
                        rfl

theorem cell23_7736031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_7736031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736031 prefixEnd_7736031 := by exact prefixLift 7736031
  have htrace : WordTrace (prefixWord ++ tailWord_7736031) baseStart_7736031 baseEnd_7736031 := by
    simpa [prefixWord, tailWord_7736031, baseEnd_7736031] using wordTrace_append hprefix tailTrace_7736031
  have hstable : (prefixWord ++ tailWord_7736031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736031).length < 2 ^ (prefixWord ++ tailWord_7736031).sum := by decide
  have hdescent : baseEnd_7736031 < baseStart_7736031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736081 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 3]
def baseStart_7736081 : Nat := 118140960795 + 7736081 * 2 ^ 59
def prefixEnd_7736081 : Nat := 4983230072969 + 3 ^ 40 * 7736081 * 2
def baseEnd_7736081 : Nat := 3972327935114852281209917

theorem tailTrace_7736081 : CollatzResearch.WordTrace tailWord_7736081 prefixEnd_7736081 3972327935114852281209917 := by
  unfold tailWord_7736081
  simp only [CollatzResearch.WordTrace]
  refine ⟨282158054286507229292416097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188105369524338152861610731 282158054286507229292416097)
  ·
    refine ⟨211618540714880421969312073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282158054286507229292416097 211618540714880421969312073)
    ·
      refine ⟨158713905536160316476984055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211618540714880421969312073 158713905536160316476984055)
      ·
        refine ⟨238070858304240474715476083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158713905536160316476984055 238070858304240474715476083)
        ·
          refine ⟨357106287456360712073214125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238070858304240474715476083 357106287456360712073214125)
          ·
            refine ⟨133914857796135267027455297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357106287456360712073214125 133914857796135267027455297)
            ·
              refine ⟨100436143347101450270591473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133914857796135267027455297 100436143347101450270591473)
              ·
                refine ⟨75327107510326087702943605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100436143347101450270591473 75327107510326087702943605)
                ·
                  refine ⟨7061916329093070722150963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75327107510326087702943605 7061916329093070722150963)
                  ·
                    refine ⟨10592874493639606083226445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7061916329093070722150963 10592874493639606083226445)
                    ·
                      refine ⟨3972327935114852281209917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592874493639606083226445 3972327935114852281209917)
                      ·
                        rfl

theorem cell23_7736081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 1, 3].length) (baseStart_7736081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736081 prefixEnd_7736081 := by exact prefixLift 7736081
  have htrace : WordTrace (prefixWord ++ tailWord_7736081) baseStart_7736081 baseEnd_7736081 := by
    simpa [prefixWord, tailWord_7736081, baseEnd_7736081] using wordTrace_append hprefix tailTrace_7736081
  have hstable : (prefixWord ++ tailWord_7736081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736081).length < 2 ^ (prefixWord ++ tailWord_7736081).sum := by decide
  have hdescent : baseEnd_7736081 < baseStart_7736081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736138 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_7736138 : Nat := 118140960795 + 7736138 * 2 ^ 59
def prefixEnd_7736138 : Nat := 4983230072969 + 3 ^ 40 * 7736138 * 2
def baseEnd_7736138 : Nat := 3972357203512158558197155

theorem tailTrace_7736138 : CollatzResearch.WordTrace tailWord_7736138 prefixEnd_7736138 3972357203512158558197155 := by
  unfold tailWord_7736138
  simp only [CollatzResearch.WordTrace]
  refine ⟨70540033311825182006810267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188106755498200485351494045 70540033311825182006810267)
  ·
    refine ⟨105810049967737773010215401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70540033311825182006810267 105810049967737773010215401)
    ·
      refine ⟨79357537475803329757661551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105810049967737773010215401 79357537475803329757661551)
      ·
        refine ⟨119036306213704994636492327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79357537475803329757661551 119036306213704994636492327)
        ·
          refine ⟨178554459320557491954738491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119036306213704994636492327 178554459320557491954738491)
          ·
            refine ⟨267831688980836237932107737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178554459320557491954738491 267831688980836237932107737)
            ·
              refine ⟨200873766735627178449080803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267831688980836237932107737 200873766735627178449080803)
              ·
                refine ⟨301310650103440767673621205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200873766735627178449080803 301310650103440767673621205)
                ·
                  refine ⟨7061968361799392992350497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 301310650103440767673621205 7061968361799392992350497)
                  ·
                    refine ⟨5296476271349544744262873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7061968361799392992350497 5296476271349544744262873)
                    ·
                      refine ⟨3972357203512158558197155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296476271349544744262873 3972357203512158558197155)
                      ·
                        rfl

theorem cell23_7736138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_7736138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736138 prefixEnd_7736138 := by exact prefixLift 7736138
  have htrace : WordTrace (prefixWord ++ tailWord_7736138) baseStart_7736138 baseEnd_7736138 := by
    simpa [prefixWord, tailWord_7736138, baseEnd_7736138] using wordTrace_append hprefix tailTrace_7736138
  have hstable : (prefixWord ++ tailWord_7736138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736138).length < 2 ^ (prefixWord ++ tailWord_7736138).sum := by decide
  have hdescent : baseEnd_7736138 < baseStart_7736138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736168 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7736168 : Nat := 118140960795 + 7736168 * 2 ^ 59
def prefixEnd_7736168 : Nat := 4983230072969 + 3 ^ 40 * 7736168 * 2
def baseEnd_7736168 : Nat := 3972372607931793440822017

theorem tailTrace_7736168 : CollatzResearch.WordTrace tailWord_7736168 prefixEnd_7736168 3972372607931793440822017 := by
  unfold tailWord_7736168
  simp only [CollatzResearch.WordTrace]
  refine ⟨141080613718596021575416579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188107484958128028767222105 141080613718596021575416579)
  ·
    refine ⟨211620920577894032363124869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141080613718596021575416579 211620920577894032363124869)
    ·
      refine ⟨39678922608355131068085913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211620920577894032363124869 39678922608355131068085913)
      ·
        refine ⟨29759191956266348301064435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39678922608355131068085913 29759191956266348301064435)
        ·
          refine ⟨44638787934399522451596653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29759191956266348301064435 44638787934399522451596653)
          ·
            refine ⟨16739545475399820919348745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44638787934399522451596653 16739545475399820919348745)
            ·
              refine ⟨12554659106549865689511559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16739545475399820919348745 12554659106549865689511559)
              ·
                refine ⟨18831988659824798534267339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554659106549865689511559 18831988659824798534267339)
                ·
                  refine ⟨28247982989737197801401009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18831988659824798534267339 28247982989737197801401009)
                  ·
                    refine ⟨21185987242302898351050757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28247982989737197801401009 21185987242302898351050757)
                    ·
                      refine ⟨3972372607931793440822017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21185987242302898351050757 3972372607931793440822017)
                      ·
                        rfl

theorem cell23_7736168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7736168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736168 prefixEnd_7736168 := by exact prefixLift 7736168
  have htrace : WordTrace (prefixWord ++ tailWord_7736168) baseStart_7736168 baseEnd_7736168 := by
    simpa [prefixWord, tailWord_7736168, baseEnd_7736168] using wordTrace_append hprefix tailTrace_7736168
  have hstable : (prefixWord ++ tailWord_7736168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736168).length < 2 ^ (prefixWord ++ tailWord_7736168).sum := by decide
  have hdescent : baseEnd_7736168 < baseStart_7736168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736171 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3]
def baseStart_7736171 : Nat := 118140960795 + 7736171 * 2 ^ 59
def prefixEnd_7736171 : Nat := 4983230072969 + 3 ^ 40 * 7736171 * 2
def baseEnd_7736171 : Nat := 3972374148373756929084503

theorem tailTrace_7736171 : CollatzResearch.WordTrace tailWord_7736171 prefixEnd_7736171 3972374148373756929084503 := by
  unfold tailWord_7736171
  simp only [CollatzResearch.WordTrace]
  refine ⟨282161336856181174663192367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188107557904120783108794911 282161336856181174663192367)
  ·
    refine ⟨423242005284271761994788551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282161336856181174663192367 423242005284271761994788551)
    ·
      refine ⟨634863007926407642992182827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423242005284271761994788551 634863007926407642992182827)
      ·
        refine ⟨952294511889611464488274241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634863007926407642992182827 952294511889611464488274241)
        ·
          refine ⟨714220883917208598366205681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952294511889611464488274241 714220883917208598366205681)
          ·
            refine ⟨535665662937906448774654261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714220883917208598366205681 535665662937906448774654261)
            ·
              refine ⟨50218655900428729572623837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535665662937906448774654261 50218655900428729572623837)
              ·
                refine ⟨18831995962660773589733939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50218655900428729572623837 18831995962660773589733939)
                ·
                  refine ⟨28247993943991160384600909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18831995962660773589733939 28247993943991160384600909)
                  ·
                    refine ⟨10592997728996685144225341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28247993943991160384600909 10592997728996685144225341)
                    ·
                      refine ⟨3972374148373756929084503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10592997728996685144225341 3972374148373756929084503)
                      ·
                        rfl

theorem cell23_7736171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 3, 3].length) (baseStart_7736171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736171 prefixEnd_7736171 := by exact prefixLift 7736171
  have htrace : WordTrace (prefixWord ++ tailWord_7736171) baseStart_7736171 baseEnd_7736171 := by
    simpa [prefixWord, tailWord_7736171, baseEnd_7736171] using wordTrace_append hprefix tailTrace_7736171
  have hstable : (prefixWord ++ tailWord_7736171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736171).length < 2 ^ (prefixWord ++ tailWord_7736171).sum := by decide
  have hdescent : baseEnd_7736171 < baseStart_7736171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736221 : List Nat := [1, 4, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7736221 : Nat := 118140960795 + 7736221 * 2 ^ 59
def prefixEnd_7736221 : Nat := 4983230072969 + 3 ^ 40 * 7736221 * 2
def baseEnd_7736221 : Nat := 1324133274135493911153091

theorem tailTrace_7736221 : CollatzResearch.WordTrace tailWord_7736221 prefixEnd_7736221 1324133274135493911153091 := by
  unfold tailWord_7736221
  simp only [CollatzResearch.WordTrace]
  refine ⟨282163160506000033202512517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188108773670666688801675011 282163160506000033202512517)
  ·
    refine ⟨52905592594875006225471097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282163160506000033202512517 52905592594875006225471097)
    ·
      refine ⟨39679194446156254669103323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52905592594875006225471097 39679194446156254669103323)
      ·
        refine ⟨59518791669234382003654985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39679194446156254669103323 59518791669234382003654985)
        ·
          refine ⟨44639093751925786502741239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59518791669234382003654985 44639093751925786502741239)
          ·
            refine ⟨66958640627888679754111859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44639093751925786502741239 66958640627888679754111859)
            ·
              refine ⟨100437960941833019631167789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66958640627888679754111859 100437960941833019631167789)
              ·
                refine ⟨37664235353187382361687921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100437960941833019631167789 37664235353187382361687921)
                ·
                  refine ⟨28248176514890536771265941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37664235353187382361687921 28248176514890536771265941)
                  ·
                    refine ⟨1324133274135493911153091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28248176514890536771265941 1324133274135493911153091)
                    ·
                      rfl

theorem cell23_7736221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7736221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736221 prefixEnd_7736221 := by exact prefixLift 7736221
  have htrace : WordTrace (prefixWord ++ tailWord_7736221) baseStart_7736221 baseEnd_7736221 := by
    simpa [prefixWord, tailWord_7736221, baseEnd_7736221] using wordTrace_append hprefix tailTrace_7736221
  have hstable : (prefixWord ++ tailWord_7736221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736221).length < 2 ^ (prefixWord ++ tailWord_7736221).sum := by decide
  have hdescent : baseEnd_7736221 < baseStart_7736221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736245 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_7736245 : Nat := 118140960795 + 7736245 * 2 ^ 59
def prefixEnd_7736245 : Nat := 4983230072969 + 3 ^ 40 * 7736245 * 2
def baseEnd_7736245 : Nat := 3972412145942189639559163

theorem tailTrace_7736245 : CollatzResearch.WordTrace tailWord_7736245 prefixEnd_7736245 3972412145942189639559163 := by
  unfold tailWord_7736245
  simp only [CollatzResearch.WordTrace]
  refine ⟨282164035857913085301386189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188109357238608723534257459 282164035857913085301386189)
  ·
    refine ⟨105811513446717406988019821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282164035857913085301386189 105811513446717406988019821)
    ·
      refine ⟨39679317542519027620507433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105811513446717406988019821 39679317542519027620507433)
      ·
        refine ⟨29759488156889270715380575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39679317542519027620507433 29759488156889270715380575)
        ·
          refine ⟨44639232235333906073070863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29759488156889270715380575 44639232235333906073070863)
          ·
            refine ⟨66958848353000859109606295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44639232235333906073070863 66958848353000859109606295)
            ·
              refine ⟨100438272529501288664409443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66958848353000859109606295 100438272529501288664409443)
              ·
                refine ⟨150657408794251932996614165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100438272529501288664409443 150657408794251932996614165)
                ·
                  refine ⟨7062066037230559359216289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150657408794251932996614165 7062066037230559359216289)
                  ·
                    refine ⟨5296549527922919519412217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062066037230559359216289 5296549527922919519412217)
                    ·
                      refine ⟨3972412145942189639559163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296549527922919519412217 3972412145942189639559163)
                      ·
                        rfl

theorem cell23_7736245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_7736245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736245 prefixEnd_7736245 := by exact prefixLift 7736245
  have htrace : WordTrace (prefixWord ++ tailWord_7736245) baseStart_7736245 baseEnd_7736245 := by
    simpa [prefixWord, tailWord_7736245, baseEnd_7736245] using wordTrace_append hprefix tailTrace_7736245
  have hstable : (prefixWord ++ tailWord_7736245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736245).length < 2 ^ (prefixWord ++ tailWord_7736245).sum := by decide
  have hdescent : baseEnd_7736245 < baseStart_7736245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736291 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7736291 : Nat := 118140960795 + 7736291 * 2 ^ 59
def prefixEnd_7736291 : Nat := 4983230072969 + 3 ^ 40 * 7736291 * 2
def baseEnd_7736291 : Nat := 3972435766052296459583951

theorem tailTrace_7736291 : CollatzResearch.WordTrace tailWord_7736291 prefixEnd_7736291 3972435766052296459583951 := by
  unfold tailWord_7736291
  simp only [CollatzResearch.WordTrace]
  refine ⟨282165713615746435157560727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188110475743830956771707151 282165713615746435157560727)
  ·
    refine ⟨423248570423619652736341091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282165713615746435157560727 423248570423619652736341091)
    ·
      refine ⟨634872855635429479104511637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423248570423619652736341091 634872855635429479104511637)
      ·
        refine ⟨29759665107910756833023983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 634872855635429479104511637 29759665107910756833023983)
        ·
          refine ⟨44639497661866135249535975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29759665107910756833023983 44639497661866135249535975)
          ·
            refine ⟨66959246492799202874303963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44639497661866135249535975 66959246492799202874303963)
            ·
              refine ⟨100438869739198804311455945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66959246492799202874303963 100438869739198804311455945)
              ·
                refine ⟨75329152304399103233591959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100438869739198804311455945 75329152304399103233591959)
                ·
                  refine ⟨112993728456598654850387939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75329152304399103233591959 112993728456598654850387939)
                  ·
                    refine ⟨169490592684897982275581909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112993728456598654850387939 169490592684897982275581909)
                    ·
                      refine ⟨3972435766052296459583951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169490592684897982275581909 3972435766052296459583951)
                      ·
                        rfl

theorem cell23_7736291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7736291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736291 prefixEnd_7736291 := by exact prefixLift 7736291
  have htrace : WordTrace (prefixWord ++ tailWord_7736291) baseStart_7736291 baseEnd_7736291 := by
    simpa [prefixWord, tailWord_7736291, baseEnd_7736291] using wordTrace_append hprefix tailTrace_7736291
  have hstable : (prefixWord ++ tailWord_7736291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736291).length < 2 ^ (prefixWord ++ tailWord_7736291).sum := by decide
  have hdescent : baseEnd_7736291 < baseStart_7736291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736298 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_7736298 : Nat := 118140960795 + 7736298 * 2 ^ 59
def prefixEnd_7736298 : Nat := 4983230072969 + 3 ^ 40 * 7736298 * 2
def baseEnd_7736298 : Nat := 1324146453472292644065473

theorem tailTrace_7736298 : CollatzResearch.WordTrace tailWord_7736298 prefixEnd_7736298 1324146453472292644065473 := by
  unfold tailWord_7736298
  simp only [CollatzResearch.WordTrace]
  refine ⟨70541492231680268838266387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188110645951147383568710365 70541492231680268838266387)
  ·
    refine ⟨105812238347520403257399581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70541492231680268838266387 105812238347520403257399581)
    ·
      refine ⟨39679589380320151221524843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105812238347520403257399581 39679589380320151221524843)
      ·
        refine ⟨59519384070480226832287265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39679589380320151221524843 59519384070480226832287265)
        ·
          refine ⟨44639538052860170124215449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59519384070480226832287265 44639538052860170124215449)
          ·
            refine ⟨33479653539645127593161587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44639538052860170124215449 33479653539645127593161587)
            ·
              refine ⟨50219480309467691389742381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33479653539645127593161587 50219480309467691389742381)
              ·
                refine ⟨18832305116050384271153393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50219480309467691389742381 18832305116050384271153393)
                ·
                  refine ⟨14124228837037788203365045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18832305116050384271153393 14124228837037788203365045)
                  ·
                    refine ⟨1324146453472292644065473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14124228837037788203365045 1324146453472292644065473)
                    ·
                      rfl

theorem cell23_7736298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_7736298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736298 prefixEnd_7736298 := by exact prefixLift 7736298
  have htrace : WordTrace (prefixWord ++ tailWord_7736298) baseStart_7736298 baseEnd_7736298 := by
    simpa [prefixWord, tailWord_7736298, baseEnd_7736298] using wordTrace_append hprefix tailTrace_7736298
  have hstable : (prefixWord ++ tailWord_7736298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736298).length < 2 ^ (prefixWord ++ tailWord_7736298).sum := by decide
  have hdescent : baseEnd_7736298 < baseStart_7736298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736355 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3]
def baseStart_7736355 : Nat := 118140960795 + 7736355 * 2 ^ 59
def prefixEnd_7736355 : Nat := 4983230072969 + 3 ^ 40 * 7736355 * 2
def baseEnd_7736355 : Nat := 3972468628814184209183657

theorem tailTrace_7736355 : CollatzResearch.WordTrace tailWord_7736355 prefixEnd_7736355 3972468628814184209183657 := by
  unfold tailWord_7736355
  simp only [CollatzResearch.WordTrace]
  refine ⟨282168047887514574087890519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188112031925009716058593679 282168047887514574087890519)
  ·
    refine ⟨423252071831271861131835779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282168047887514574087890519 423252071831271861131835779)
    ·
      refine ⟨634878107746907791697753669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423252071831271861131835779 634878107746907791697753669)
      ·
        refine ⟨119039645202545210943328813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 634878107746907791697753669 119039645202545210943328813)
        ·
          refine ⟨44639866950954454103748305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119039645202545210943328813 44639866950954454103748305)
          ·
            refine ⟨33479900213215840577811229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44639866950954454103748305 33479900213215840577811229)
            ·
              refine ⟨12554962579955940216679211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33479900213215840577811229 12554962579955940216679211)
              ·
                refine ⟨18832443869933910325018817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12554962579955940216679211 18832443869933910325018817)
                ·
                  refine ⟨14124332902450432743764113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18832443869933910325018817 14124332902450432743764113)
                  ·
                    refine ⟨10593249676837824557823085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14124332902450432743764113 10593249676837824557823085)
                    ·
                      refine ⟨3972468628814184209183657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593249676837824557823085 3972468628814184209183657)
                      ·
                        rfl

theorem cell23_7736355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_7736355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736355 prefixEnd_7736355 := by exact prefixLift 7736355
  have htrace : WordTrace (prefixWord ++ tailWord_7736355) baseStart_7736355 baseEnd_7736355 := by
    simpa [prefixWord, tailWord_7736355, baseEnd_7736355] using wordTrace_append hprefix tailTrace_7736355
  have hstable : (prefixWord ++ tailWord_7736355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736355).length < 2 ^ (prefixWord ++ tailWord_7736355).sum := by decide
  have hdescent : baseEnd_7736355 < baseStart_7736355 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736402 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_7736402 : Nat := 118140960795 + 7736402 * 2 ^ 59
def prefixEnd_7736402 : Nat := 4983230072969 + 3 ^ 40 * 7736402 * 2
def baseEnd_7736402 : Nat := 3972492762404945525295941

theorem tailTrace_7736402 : CollatzResearch.WordTrace tailWord_7736402 prefixEnd_7736402 3972492762404945525295941 := by
  unfold tailWord_7736402
  simp only [CollatzResearch.WordTrace]
  refine ⟨70542440529586075278712865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188113174745562867409900973 70542440529586075278712865)
  ·
    refine ⟨52906830397189556459034649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70542440529586075278712865 52906830397189556459034649)
    ·
      refine ⟨39680122797892167344275987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52906830397189556459034649 39680122797892167344275987)
      ·
        refine ⟨59520184196838251016413981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39680122797892167344275987 59520184196838251016413981)
        ·
          refine ⟨22320069073814344131155243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59520184196838251016413981 22320069073814344131155243)
          ·
            refine ⟨33480103610721516196732865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22320069073814344131155243 33480103610721516196732865)
            ·
              refine ⟨25110077708041137147549649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33480103610721516196732865 25110077708041137147549649)
              ·
                refine ⟨18832558281030852860662237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25110077708041137147549649 18832558281030852860662237)
                ·
                  refine ⟨7062209355386569822748339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18832558281030852860662237 7062209355386569822748339)
                  ·
                    refine ⟨10593314033079854734122509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7062209355386569822748339 10593314033079854734122509)
                    ·
                      refine ⟨3972492762404945525295941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593314033079854734122509 3972492762404945525295941)
                      ·
                        rfl

theorem cell23_7736402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_7736402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736402 prefixEnd_7736402 := by exact prefixLift 7736402
  have htrace : WordTrace (prefixWord ++ tailWord_7736402) baseStart_7736402 baseEnd_7736402 := by
    simpa [prefixWord, tailWord_7736402, baseEnd_7736402] using wordTrace_append hprefix tailTrace_7736402
  have hstable : (prefixWord ++ tailWord_7736402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736402).length < 2 ^ (prefixWord ++ tailWord_7736402).sum := by decide
  have hdescent : baseEnd_7736402 < baseStart_7736402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736405 : List Nat := [1, 3, 2, 2, 1, 2, 4, 2, 1, 5]
def baseStart_7736405 : Nat := 118140960795 + 7736405 * 2 ^ 59
def prefixEnd_7736405 : Nat := 4983230072969 + 3 ^ 40 * 7736405 * 2
def baseEnd_7736405 : Nat := 1324164767615636337852809

theorem tailTrace_7736405 : CollatzResearch.WordTrace tailWord_7736405 prefixEnd_7736405 1324164767615636337852809 := by
  unfold tailWord_7736405
  simp only [CollatzResearch.WordTrace]
  refine ⟨282169871537333432627210669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188113247691555621751473779 282169871537333432627210669)
  ·
    refine ⟨105813701826500037235204001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282169871537333432627210669 105813701826500037235204001)
    ·
      refine ⟨79360276369875027926403001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105813701826500037235204001 79360276369875027926403001)
      ·
        refine ⟨59520207277406270944802251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79360276369875027926403001 59520207277406270944802251)
        ·
          refine ⟨89280310916109406417203377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59520207277406270944802251 89280310916109406417203377)
          ·
            refine ⟨66960233187082054812902533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89280310916109406417203377 66960233187082054812902533)
            ·
              refine ⟨12555043722577885277419225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66960233187082054812902533 12555043722577885277419225)
              ·
                refine ⟨9416282791933413958064419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12555043722577885277419225 9416282791933413958064419)
                ·
                  refine ⟨14124424187900120937096629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9416282791933413958064419 14124424187900120937096629)
                  ·
                    refine ⟨1324164767615636337852809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14124424187900120937096629 1324164767615636337852809)
                    ·
                      rfl

theorem cell23_7736405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_7736405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736405 prefixEnd_7736405 := by exact prefixLift 7736405
  have htrace : WordTrace (prefixWord ++ tailWord_7736405) baseStart_7736405 baseEnd_7736405 := by
    simpa [prefixWord, tailWord_7736405, baseEnd_7736405] using wordTrace_append hprefix tailTrace_7736405
  have hstable : (prefixWord ++ tailWord_7736405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736405).length < 2 ^ (prefixWord ++ tailWord_7736405).sum := by decide
  have hdescent : baseEnd_7736405 < baseStart_7736405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736412 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_7736412 : Nat := 118140960795 + 7736412 * 2 ^ 59
def prefixEnd_7736412 : Nat := 4983230072969 + 3 ^ 40 * 7736412 * 2
def baseEnd_7736412 : Nat := 3972497897211490486170895

theorem tailTrace_7736412 : CollatzResearch.WordTrace tailWord_7736412 prefixEnd_7736412 3972497897211490486170895 := by
  unfold tailWord_7736412
  simp only [CollatzResearch.WordTrace]
  refine ⟨141085063424154036411357745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188113417898872048548476993 141085063424154036411357745)
  ·
    refine ⟨105813797568115527308518309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141085063424154036411357745 105813797568115527308518309)
    ·
      refine ⟨19840087044021661370347183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105813797568115527308518309 19840087044021661370347183)
      ·
        refine ⟨29760130566032492055520775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19840087044021661370347183 29760130566032492055520775)
        ·
          refine ⟨44640195849048738083281163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29760130566032492055520775 44640195849048738083281163)
          ·
            refine ⟨66960293773573107124921745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44640195849048738083281163 66960293773573107124921745)
            ·
              refine ⟨50220220330179830343691309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66960293773573107124921745 50220220330179830343691309)
              ·
                refine ⟨18832582623817436378884241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50220220330179830343691309 18832582623817436378884241)
                ·
                  refine ⟨14124436967863077284163181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18832582623817436378884241 14124436967863077284163181)
                  ·
                    refine ⟨5296663862948653981561193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14124436967863077284163181 5296663862948653981561193)
                    ·
                      refine ⟨3972497897211490486170895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296663862948653981561193 3972497897211490486170895)
                      ·
                        rfl

theorem cell23_7736412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_7736412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736412 prefixEnd_7736412 := by exact prefixLift 7736412
  have htrace : WordTrace (prefixWord ++ tailWord_7736412) baseStart_7736412 baseEnd_7736412 := by
    simpa [prefixWord, tailWord_7736412, baseEnd_7736412] using wordTrace_append hprefix tailTrace_7736412
  have hstable : (prefixWord ++ tailWord_7736412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736412).length < 2 ^ (prefixWord ++ tailWord_7736412).sum := by decide
  have hdescent : baseEnd_7736412 < baseStart_7736412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736413 : List Nat := [1, 4, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7736413 : Nat := 118140960795 + 7736413 * 2 ^ 59
def prefixEnd_7736413 : Nat := 4983230072969 + 3 ^ 40 * 7736413 * 2
def baseEnd_7736413 : Nat := 1324166136897381660752797

theorem tailTrace_7736413 : CollatzResearch.WordTrace tailWord_7736413 prefixEnd_7736413 1324166136897381660752797 := by
  unfold tailWord_7736413
  simp only [CollatzResearch.WordTrace]
  refine ⟨282170163321304449993501893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188113442214202966662334595 282170163321304449993501893)
  ·
    refine ⟨52906905622744584373781605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282170163321304449993501893 52906905622744584373781605)
    ·
      refine ⟨9920044804264609570084051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52906905622744584373781605 9920044804264609570084051)
      ·
        refine ⟨14880067206396914355126077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920044804264609570084051 14880067206396914355126077)
        ·
          refine ⟨5580025202398842883172279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14880067206396914355126077 5580025202398842883172279)
          ·
            refine ⟨8370037803598264324758419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580025202398842883172279 8370037803598264324758419)
            ·
              refine ⟨12555056705397396487137629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370037803598264324758419 12555056705397396487137629)
              ·
                refine ⟨4708146264524023682676611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12555056705397396487137629 4708146264524023682676611)
                ·
                  refine ⟨7062219396786035524014917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708146264524023682676611 7062219396786035524014917)
                  ·
                    refine ⟨1324166136897381660752797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062219396786035524014917 1324166136897381660752797)
                    ·
                      rfl

theorem cell23_7736413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7736413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736413 prefixEnd_7736413 := by exact prefixLift 7736413
  have htrace : WordTrace (prefixWord ++ tailWord_7736413) baseStart_7736413 baseEnd_7736413 := by
    simpa [prefixWord, tailWord_7736413, baseEnd_7736413] using wordTrace_append hprefix tailTrace_7736413
  have hstable : (prefixWord ++ tailWord_7736413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736413).length < 2 ^ (prefixWord ++ tailWord_7736413).sum := by decide
  have hdescent : baseEnd_7736413 < baseStart_7736413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736425 : List Nat := [1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 4]
def baseStart_7736425 : Nat := 118140960795 + 7736425 * 2 ^ 59
def prefixEnd_7736425 : Nat := 4983230072969 + 3 ^ 40 * 7736425 * 2
def baseEnd_7736425 : Nat := 3972504572459998935308335

theorem tailTrace_7736425 : CollatzResearch.WordTrace tailWord_7736425 prefixEnd_7736425 3972504572459998935308335 := by
  unfold tailWord_7736425
  simp only [CollatzResearch.WordTrace]
  refine ⟨282170600997260976042938729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188113733998173984028625819 282170600997260976042938729)
  ·
    refine ⟨211627950747945732032204047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282170600997260976042938729 211627950747945732032204047)
    ·
      refine ⟨317441926121918598048306071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211627950747945732032204047 317441926121918598048306071)
      ·
        refine ⟨476162889182877897072459107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317441926121918598048306071 476162889182877897072459107)
        ·
          refine ⟨714244333774316845608688661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476162889182877897072459107 714244333774316845608688661)
          ·
            refine ⟨33480203145671102137907281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 714244333774316845608688661 33480203145671102137907281)
            ·
              refine ⟨25110152359253326603430461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33480203145671102137907281 25110152359253326603430461)
              ·
                refine ⟨9416307134719997476286423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25110152359253326603430461 9416307134719997476286423)
                ·
                  refine ⟨14124460702079996214429635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9416307134719997476286423 14124460702079996214429635)
                  ·
                    refine ⟨21186691053119994321644453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14124460702079996214429635 21186691053119994321644453)
                    ·
                      refine ⟨3972504572459998935308335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21186691053119994321644453 3972504572459998935308335)
                      ·
                        rfl

theorem cell23_7736425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 1, 4].length) (baseStart_7736425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736425 prefixEnd_7736425 := by exact prefixLift 7736425
  have htrace : WordTrace (prefixWord ++ tailWord_7736425) baseStart_7736425 baseEnd_7736425 := by
    simpa [prefixWord, tailWord_7736425, baseEnd_7736425] using wordTrace_append hprefix tailTrace_7736425
  have hstable : (prefixWord ++ tailWord_7736425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736425).length < 2 ^ (prefixWord ++ tailWord_7736425).sum := by decide
  have hdescent : baseEnd_7736425 < baseStart_7736425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736445 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_7736445 : Nat := 118140960795 + 7736445 * 2 ^ 59
def prefixEnd_7736445 : Nat := 4983230072969 + 3 ^ 40 * 7736445 * 2
def baseEnd_7736445 : Nat := 3972514842073088857058243

theorem tailTrace_7736445 : CollatzResearch.WordTrace tailWord_7736445 prefixEnd_7736445 3972514842073088857058243 := by
  unfold tailWord_7736445
  simp only [CollatzResearch.WordTrace]
  refine ⟨282171330457188519458666789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188114220304792346305777859 282171330457188519458666789)
  ·
    refine ⟨52907124460722847398500023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282171330457188519458666789 52907124460722847398500023)
    ·
      refine ⟨79360686691084271097750035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52907124460722847398500023 79360686691084271097750035)
      ·
        refine ⟨119041030036626406646625053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79360686691084271097750035 119041030036626406646625053)
        ·
          refine ⟨44640386263734902492484395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119041030036626406646625053 44640386263734902492484395)
          ·
            refine ⟨66960579395602353738726593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44640386263734902492484395 66960579395602353738726593)
            ·
              refine ⟨50220434546701765304044945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66960579395602353738726593 50220434546701765304044945)
              ·
                refine ⟨37665325910026323978033709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50220434546701765304044945 37665325910026323978033709)
                ·
                  refine ⟨14124497216259871491762641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37665325910026323978033709 14124497216259871491762641)
                  ·
                    refine ⟨10593372912194903618821981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14124497216259871491762641 10593372912194903618821981)
                    ·
                      refine ⟨3972514842073088857058243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593372912194903618821981 3972514842073088857058243)
                      ·
                        rfl

theorem cell23_7736445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_7736445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736445 prefixEnd_7736445 := by exact prefixLift 7736445
  have htrace : WordTrace (prefixWord ++ tailWord_7736445) baseStart_7736445 baseEnd_7736445 := by
    simpa [prefixWord, tailWord_7736445, baseEnd_7736445] using wordTrace_append hprefix tailTrace_7736445
  have hstable : (prefixWord ++ tailWord_7736445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736445).length < 2 ^ (prefixWord ++ tailWord_7736445).sum := by decide
  have hdescent : baseEnd_7736445 < baseStart_7736445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736452 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_7736452 : Nat := 118140960795 + 7736452 * 2 ^ 59
def prefixEnd_7736452 : Nat := 4983230072969 + 3 ^ 40 * 7736452 * 2
def baseEnd_7736452 : Nat := 1324172812145890109890237

theorem tailTrace_7736452 : CollatzResearch.WordTrace tailWord_7736452 prefixEnd_7736452 1324172812145890109890237 := by
  unfold tailWord_7736452
  simp only [CollatzResearch.WordTrace]
  refine ⟨141085792884081579827085805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188114390512108773102781073 141085792884081579827085805)
  ·
    refine ⟨52907172331530592435157177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141085792884081579827085805 52907172331530592435157177)
    ·
      refine ⟨39680379248647944326367883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52907172331530592435157177 39680379248647944326367883)
      ·
        refine ⟨59520568872971916489551825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39680379248647944326367883 59520568872971916489551825)
        ·
          refine ⟨44640426654728937367163869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59520568872971916489551825 44640426654728937367163869)
          ·
            refine ⟨16740159995523351512686451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44640426654728937367163869 16740159995523351512686451)
            ·
              refine ⟨25110239993285027269029677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16740159995523351512686451 25110239993285027269029677)
              ·
                refine ⟨9416339997481885225886129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25110239993285027269029677 9416339997481885225886129)
                ·
                  refine ⟨7062254998111413919414597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416339997481885225886129 7062254998111413919414597)
                  ·
                    refine ⟨1324172812145890109890237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062254998111413919414597 1324172812145890109890237)
                    ·
                      rfl

theorem cell23_7736452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_7736452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736452 prefixEnd_7736452 := by exact prefixLift 7736452
  have htrace : WordTrace (prefixWord ++ tailWord_7736452) baseStart_7736452 baseEnd_7736452 := by
    simpa [prefixWord, tailWord_7736452, baseEnd_7736452] using wordTrace_append hprefix tailTrace_7736452
  have hstable : (prefixWord ++ tailWord_7736452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736452).length < 2 ^ (prefixWord ++ tailWord_7736452).sum := by decide
  have hdescent : baseEnd_7736452 < baseStart_7736452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736462 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7736462 : Nat := 118140960795 + 7736462 * 2 ^ 59
def prefixEnd_7736462 : Nat := 4983230072969 + 3 ^ 40 * 7736462 * 2
def baseEnd_7736462 : Nat := 3972523571244215290545665

theorem tailTrace_7736462 : CollatzResearch.WordTrace tailWord_7736462 prefixEnd_7736462 3972523571244215290545665 := by
  unfold tailWord_7736462
  simp only [CollatzResearch.WordTrace]
  refine ⟨35271493812265866420254455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188114633665417954241357093 35271493812265866420254455)
  ·
    refine ⟨52907240718398799630381683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35271493812265866420254455 52907240718398799630381683)
    ·
      refine ⟨79360861077598199445572525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52907240718398799630381683 79360861077598199445572525)
      ·
        refine ⟨29760322904099324792089697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79360861077598199445572525 29760322904099324792089697)
        ·
          refine ⟨22320242178074493594067273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29760322904099324792089697 22320242178074493594067273)
          ·
            refine ⟨16740181633555870195550455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22320242178074493594067273 16740181633555870195550455)
            ·
              refine ⟨25110272450333805293325683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16740181633555870195550455 25110272450333805293325683)
              ·
                refine ⟨37665408675500707939988525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25110272450333805293325683 37665408675500707939988525)
                ·
                  refine ⟨14124528253312765477495697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37665408675500707939988525 14124528253312765477495697)
                  ·
                    refine ⟨10593396189984574108121773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14124528253312765477495697 10593396189984574108121773)
                    ·
                      refine ⟨3972523571244215290545665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593396189984574108121773 3972523571244215290545665)
                      ·
                        rfl

theorem cell23_7736462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7736462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736462 prefixEnd_7736462 := by exact prefixLift 7736462
  have htrace : WordTrace (prefixWord ++ tailWord_7736462) baseStart_7736462 baseEnd_7736462 := by
    simpa [prefixWord, tailWord_7736462, baseEnd_7736462] using wordTrace_append hprefix tailTrace_7736462
  have hstable : (prefixWord ++ tailWord_7736462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736462).length < 2 ^ (prefixWord ++ tailWord_7736462).sum := by decide
  have hdescent : baseEnd_7736462 < baseStart_7736462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736479 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7736479 : Nat := 118140960795 + 7736479 * 2 ^ 59
def prefixEnd_7736479 : Nat := 4983230072969 + 3 ^ 40 * 7736479 * 2
def baseEnd_7736479 : Nat := 3972532300415341724033087

theorem tailTrace_7736479 : CollatzResearch.WordTrace tailWord_7736479 prefixEnd_7736479 3972532300415341724033087 := by
  unfold tailWord_7736479
  simp only [CollatzResearch.WordTrace]
  refine ⟨282172570539065343265404491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188115047026043562176936327 282172570539065343265404491)
  ·
    refine ⟨423258855808598014898106737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282172570539065343265404491 423258855808598014898106737)
    ·
      refine ⟨317444141856448511173580053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423258855808598014898106737 317444141856448511173580053)
      ·
        refine ⟨14880194149521023961261565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317444141856448511173580053 14880194149521023961261565)
        ·
          refine ⟨5580072806070383985473087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14880194149521023961261565 5580072806070383985473087)
          ·
            refine ⟨8370109209105575978209631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580072806070383985473087 8370109209105575978209631)
            ·
              refine ⟨12555163813658363967314447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370109209105575978209631 12555163813658363967314447)
              ·
                refine ⟨18832745720487545950971671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555163813658363967314447 18832745720487545950971671)
                ·
                  refine ⟨28249118580731318926457507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18832745720487545950971671 28249118580731318926457507)
                  ·
                    refine ⟨42373677871096978389686261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28249118580731318926457507 42373677871096978389686261)
                    ·
                      refine ⟨3972532300415341724033087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42373677871096978389686261 3972532300415341724033087)
                      ·
                        rfl

theorem cell23_7736479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7736479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736479 prefixEnd_7736479 := by exact prefixLift 7736479
  have htrace : WordTrace (prefixWord ++ tailWord_7736479) baseStart_7736479 baseEnd_7736479 := by
    simpa [prefixWord, tailWord_7736479, baseEnd_7736479] using wordTrace_append hprefix tailTrace_7736479
  have hstable : (prefixWord ++ tailWord_7736479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736479).length < 2 ^ (prefixWord ++ tailWord_7736479).sum := by decide
  have hdescent : baseEnd_7736479 < baseStart_7736479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736493 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_7736493 : Nat := 118140960795 + 7736493 * 2 ^ 59
def prefixEnd_7736493 : Nat := 4983230072969 + 3 ^ 40 * 7736493 * 2
def baseEnd_7736493 : Nat := 3972539489144504669258023

theorem tailTrace_7736493 : CollatzResearch.WordTrace tailWord_7736493 prefixEnd_7736493 3972539489144504669258023 := by
  unfold tailWord_7736493
  simp only [CollatzResearch.WordTrace]
  refine ⟨282173081161014623656414133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188115387440676415770942755 282173081161014623656414133)
  ·
    refine ⟨26453726358845120967788825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 282173081161014623656414133 26453726358845120967788825)
    ·
      refine ⟨19840294769133840725841619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26453726358845120967788825 19840294769133840725841619)
      ·
        refine ⟨29760442153700761088762429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19840294769133840725841619 29760442153700761088762429)
        ·
          refine ⟨11160165807637785408285911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29760442153700761088762429 11160165807637785408285911)
          ·
            refine ⟨16740248711456678112428867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11160165807637785408285911 16740248711456678112428867)
            ·
              refine ⟨25110373067185017168643301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16740248711456678112428867 25110373067185017168643301)
              ·
                refine ⟨4708194950097190719120619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25110373067185017168643301 4708194950097190719120619)
                ·
                  refine ⟨7062292425145786078680929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708194950097190719120619 7062292425145786078680929)
                  ·
                    refine ⟨5296719318859339559010697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062292425145786078680929 5296719318859339559010697)
                    ·
                      refine ⟨3972539489144504669258023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296719318859339559010697 3972539489144504669258023)
                      ·
                        rfl

theorem cell23_7736493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_7736493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736493 prefixEnd_7736493 := by exact prefixLift 7736493
  have htrace : WordTrace (prefixWord ++ tailWord_7736493) baseStart_7736493 baseEnd_7736493 := by
    simpa [prefixWord, tailWord_7736493, baseEnd_7736493] using wordTrace_append hprefix tailTrace_7736493
  have hstable : (prefixWord ++ tailWord_7736493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736493).length < 2 ^ (prefixWord ++ tailWord_7736493).sum := by decide
  have hdescent : baseEnd_7736493 < baseStart_7736493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736538 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_7736538 : Nat := 118140960795 + 7736538 * 2 ^ 59
def prefixEnd_7736538 : Nat := 4983230072969 + 3 ^ 40 * 7736538 * 2
def baseEnd_7736538 : Nat := 441395843974884110355035

theorem tailTrace_7736538 : CollatzResearch.WordTrace tailWord_7736538 prefixEnd_7736538 441395843974884110355035 := by
  unfold tailWord_7736538
  simp only [CollatzResearch.WordTrace]
  refine ⟨70543680611462899085450567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188116481630567730894534845 70543680611462899085450567)
  ·
    refine ⟨105815520917194348628175851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70543680611462899085450567 105815520917194348628175851)
    ·
      refine ⟨158723281375791522942263777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105815520917194348628175851 158723281375791522942263777)
      ·
        refine ⟨119042461031843642206697833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158723281375791522942263777 119042461031843642206697833)
        ·
          refine ⟨89281845773882731655023375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119042461031843642206697833 89281845773882731655023375)
          ·
            refine ⟨133922768660824097482535063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89281845773882731655023375 133922768660824097482535063)
            ·
              refine ⟨200884152991236146223802595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133922768660824097482535063 200884152991236146223802595)
              ·
                refine ⟨301326229486854219335703893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200884152991236146223802595 301326229486854219335703893)
                ·
                  refine ⟨441395843974884110355035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 301326229486854219335703893 441395843974884110355035)
                  ·
                    rfl

theorem cell23_7736538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_7736538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736538 prefixEnd_7736538 := by exact prefixLift 7736538
  have htrace : WordTrace (prefixWord ++ tailWord_7736538) baseStart_7736538 baseEnd_7736538 := by
    simpa [prefixWord, tailWord_7736538, baseEnd_7736538] using wordTrace_append hprefix tailTrace_7736538
  have hstable : (prefixWord ++ tailWord_7736538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736538).length < 2 ^ (prefixWord ++ tailWord_7736538).sum := by decide
  have hdescent : baseEnd_7736538 < baseStart_7736538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736545 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_7736545 : Nat := 118140960795 + 7736545 * 2 ^ 59
def prefixEnd_7736545 : Nat := 4983230072969 + 3 ^ 40 * 7736545 * 2
def baseEnd_7736545 : Nat := 3972566190138538465807783

theorem tailTrace_7736545 : CollatzResearch.WordTrace tailWord_7736545 prefixEnd_7736545 3972566190138538465807783 := by
  unfold tailWord_7736545
  simp only [CollatzResearch.WordTrace]
  refine ⟨282174977756826236537307089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188116651837884157691538059 282174977756826236537307089)
  ·
    refine ⟨211631233317619677402980317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282174977756826236537307089 211631233317619677402980317)
    ·
      refine ⟨79361712494107379026117619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211631233317619677402980317 79361712494107379026117619)
      ·
        refine ⟨119042568741161068539176429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79361712494107379026117619 119042568741161068539176429)
        ·
          refine ⟨44640963277935400702191161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119042568741161068539176429 44640963277935400702191161)
          ·
            refine ⟨33480722458451550526643371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44640963277935400702191161 33480722458451550526643371)
            ·
              refine ⟨50221083687677325789965057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33480722458451550526643371 50221083687677325789965057)
              ·
                refine ⟨37665812765757994342473793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50221083687677325789965057 37665812765757994342473793)
                ·
                  refine ⟨28249359574318495756855345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37665812765757994342473793 28249359574318495756855345)
                  ·
                    refine ⟨21187019680738871817641509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28249359574318495756855345 21187019680738871817641509)
                    ·
                      refine ⟨3972566190138538465807783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21187019680738871817641509 3972566190138538465807783)
                      ·
                        rfl

theorem cell23_7736545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_7736545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736545 prefixEnd_7736545 := by exact prefixLift 7736545
  have htrace : WordTrace (prefixWord ++ tailWord_7736545) baseStart_7736545 baseEnd_7736545 := by
    simpa [prefixWord, tailWord_7736545, baseEnd_7736545] using wordTrace_append hprefix tailTrace_7736545
  have hstable : (prefixWord ++ tailWord_7736545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736545).length < 2 ^ (prefixWord ++ tailWord_7736545).sum := by decide
  have hdescent : baseEnd_7736545 < baseStart_7736545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736555 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 7]
def baseStart_7736555 : Nat := 118140960795 + 7736555 * 2 ^ 59
def prefixEnd_7736555 : Nat := 4983230072969 + 3 ^ 40 * 7736555 * 2
def baseEnd_7736555 : Nat := 441396813882787047409193

theorem tailTrace_7736555 : CollatzResearch.WordTrace tailWord_7736555 prefixEnd_7736555 441396813882787047409193 := by
  unfold tailWord_7736555
  simp only [CollatzResearch.WordTrace]
  refine ⟨282175342486790008245171119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188116894991193338830114079 282175342486790008245171119)
  ·
    refine ⟨423263013730185012367756679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282175342486790008245171119 423263013730185012367756679)
    ·
      refine ⟨634894520595277518551635019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423263013730185012367756679 634894520595277518551635019)
      ·
        refine ⟨952341780892916277827452529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634894520595277518551635019 952341780892916277827452529)
        ·
          refine ⟨714256335669687208370589397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952341780892916277827452529 714256335669687208370589397)
          ·
            refine ⟨16740382867258293946185689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 714256335669687208370589397 16740382867258293946185689)
            ·
              refine ⟨12555287150443720459639267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16740382867258293946185689 12555287150443720459639267)
              ·
                refine ⟨18832930725665580689458901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555287150443720459639267 18832930725665580689458901)
                ·
                  refine ⟨441396813882787047409193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18832930725665580689458901 441396813882787047409193)
                  ·
                    rfl

theorem cell23_7736555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 7].length) (baseStart_7736555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736555 prefixEnd_7736555 := by exact prefixLift 7736555
  have htrace : WordTrace (prefixWord ++ tailWord_7736555) baseStart_7736555 baseEnd_7736555 := by
    simpa [prefixWord, tailWord_7736555, baseEnd_7736555] using wordTrace_append hprefix tailTrace_7736555
  have hstable : (prefixWord ++ tailWord_7736555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736555).length < 2 ^ (prefixWord ++ tailWord_7736555).sum := by decide
  have hdescent : baseEnd_7736555 < baseStart_7736555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736585 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 2, 5]
def baseStart_7736585 : Nat := 118140960795 + 7736585 * 2 ^ 59
def prefixEnd_7736585 : Nat := 4983230072969 + 3 ^ 40 * 7736585 * 2
def baseEnd_7736585 : Nat := 1324195576454906103102533

theorem tailTrace_7736585 : CollatzResearch.WordTrace tailWord_7736585 prefixEnd_7736585 1324195576454906103102533 := by
  unfold tailWord_7736585
  simp only [CollatzResearch.WordTrace]
  refine ⟨282176436676681323368763209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188117624451120882245842139 282176436676681323368763209)
  ·
    refine ⟨211632327507510992526572407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282176436676681323368763209 211632327507510992526572407)
    ·
      refine ⟨317448491261266488789858611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211632327507510992526572407 317448491261266488789858611)
      ·
        refine ⟨476172736891899733184787917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317448491261266488789858611 476172736891899733184787917)
        ·
          refine ⟨178564776334462399944295469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476172736891899733184787917 178564776334462399944295469)
          ·
            refine ⟨66961791125423399979110801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178564776334462399944295469 66961791125423399979110801)
            ·
              refine ⟨50221343344067549984333101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66961791125423399979110801 50221343344067549984333101)
              ·
                refine ⟨18833003754025331244124913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50221343344067549984333101 18833003754025331244124913)
                ·
                  refine ⟨14124752815518998433093685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18833003754025331244124913 14124752815518998433093685)
                  ·
                    refine ⟨1324195576454906103102533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14124752815518998433093685 1324195576454906103102533)
                    ·
                      rfl

theorem cell23_7736585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 5].length) (baseStart_7736585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736585 prefixEnd_7736585 := by exact prefixLift 7736585
  have htrace : WordTrace (prefixWord ++ tailWord_7736585) baseStart_7736585 baseEnd_7736585 := by
    simpa [prefixWord, tailWord_7736585, baseEnd_7736585] using wordTrace_append hprefix tailTrace_7736585
  have hstable : (prefixWord ++ tailWord_7736585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736585).length < 2 ^ (prefixWord ++ tailWord_7736585).sum := by decide
  have hdescent : baseEnd_7736585 < baseStart_7736585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736602 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_7736602 : Nat := 118140960795 + 7736602 * 2 ^ 59
def prefixEnd_7736602 : Nat := 4983230072969 + 3 ^ 40 * 7736602 * 2
def baseEnd_7736602 : Nat := 1324198486178614914265007

theorem tailTrace_7736602 : CollatzResearch.WordTrace tailWord_7736602 prefixEnd_7736602 1324198486178614914265007 := by
  unfold tailWord_7736602
  simp only [CollatzResearch.WordTrace]
  refine ⟨70544264179404933818033015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188118037811746490181421373 70544264179404933818033015)
  ·
    refine ⟨105816396269107400727049523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70544264179404933818033015 105816396269107400727049523)
    ·
      refine ⟨158724594403661101090574285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105816396269107400727049523 158724594403661101090574285)
      ·
        refine ⟨59521722901372912908965357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158724594403661101090574285 59521722901372912908965357)
        ·
          refine ⟨22320646088014842340862009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59521722901372912908965357 22320646088014842340862009)
          ·
            refine ⟨16740484566011131755646507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22320646088014842340862009 16740484566011131755646507)
            ·
              refine ⟨25110726849016697633469761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16740484566011131755646507 25110726849016697633469761)
              ·
                refine ⟨18833045136762523225102321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25110726849016697633469761 18833045136762523225102321)
                ·
                  refine ⟨14124783852571892418826741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18833045136762523225102321 14124783852571892418826741)
                  ·
                    refine ⟨1324198486178614914265007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14124783852571892418826741 1324198486178614914265007)
                    ·
                      rfl

theorem cell23_7736602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_7736602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736602 prefixEnd_7736602 := by exact prefixLift 7736602
  have htrace : WordTrace (prefixWord ++ tailWord_7736602) baseStart_7736602 baseEnd_7736602 := by
    simpa [prefixWord, tailWord_7736602, baseEnd_7736602] using wordTrace_append hprefix tailTrace_7736602
  have hstable : (prefixWord ++ tailWord_7736602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736602).length < 2 ^ (prefixWord ++ tailWord_7736602).sum := by decide
  have hdescent : baseEnd_7736602 < baseStart_7736602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736606 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_7736606 : Nat := 118140960795 + 7736606 * 2 ^ 59
def prefixEnd_7736606 : Nat := 4983230072969 + 3 ^ 40 * 7736606 * 2
def baseEnd_7736606 : Nat := 441399723606495858571667

theorem tailTrace_7736606 : CollatzResearch.WordTrace tailWord_7736606 prefixEnd_7736606 441399723606495858571667 := by
  unfold tailWord_7736606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35272150326200655494409709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188118135073070162636851781 35272150326200655494409709)
  ·
    refine ⟨13227056372325245810403641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35272150326200655494409709 13227056372325245810403641)
    ·
      refine ⟨9920292279243934357802731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227056372325245810403641 9920292279243934357802731)
      ·
        refine ⟨14880438418865901536704097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920292279243934357802731 14880438418865901536704097)
        ·
          refine ⟨11160328814149426152528073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14880438418865901536704097 11160328814149426152528073)
          ·
            refine ⟨8370246610612069614396055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11160328814149426152528073 8370246610612069614396055)
            ·
              refine ⟨12555369915918104421594083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370246610612069614396055 12555369915918104421594083)
              ·
                refine ⟨18833054873877156632391125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555369915918104421594083 18833054873877156632391125)
                ·
                  refine ⟨441399723606495858571667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18833054873877156632391125 441399723606495858571667)
                  ·
                    rfl

theorem cell23_7736606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_7736606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736606 prefixEnd_7736606 := by exact prefixLift 7736606
  have htrace : WordTrace (prefixWord ++ tailWord_7736606) baseStart_7736606 baseEnd_7736606 := by
    simpa [prefixWord, tailWord_7736606, baseEnd_7736606] using wordTrace_append hprefix tailTrace_7736606
  have hstable : (prefixWord ++ tailWord_7736606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736606).length < 2 ^ (prefixWord ++ tailWord_7736606).sum := by decide
  have hdescent : baseEnd_7736606 < baseStart_7736606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736655 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_7736655 : Nat := 118140960795 + 7736655 * 2 ^ 59
def prefixEnd_7736655 : Nat := 4983230072969 + 3 ^ 40 * 7736655 * 2
def baseEnd_7736655 : Nat := 3972622673010533035432277

theorem tailTrace_7736655 : CollatzResearch.WordTrace tailWord_7736655 prefixEnd_7736655 3972622673010533035432277 := by
  unfold tailWord_7736655
  simp only [CollatzResearch.WordTrace]
  refine ⟨282178989786427725323811419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188119326524285150215874279 282178989786427725323811419)
  ·
    refine ⟨423268484679641587985717129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282178989786427725323811419 423268484679641587985717129)
    ·
      refine ⟨317451363509731190989287847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423268484679641587985717129 317451363509731190989287847)
      ·
        refine ⟨476177045264596786483931771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317451363509731190989287847 476177045264596786483931771)
        ·
          refine ⟨714265567896895179725897657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476177045264596786483931771 714265567896895179725897657)
          ·
            refine ⟨535699175922671384794423243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714265567896895179725897657 535699175922671384794423243)
            ·
              refine ⟨803548763884007077191634865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535699175922671384794423243 803548763884007077191634865)
              ·
                refine ⟨602661572913005307893726149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 803548763884007077191634865 602661572913005307893726149)
                ·
                  refine ⟨112999044921188495230073653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 602661572913005307893726149 112999044921188495230073653)
                  ·
                    refine ⟨10593660461361421427819405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112999044921188495230073653 10593660461361421427819405)
                    ·
                      refine ⟨3972622673010533035432277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593660461361421427819405 3972622673010533035432277)
                      ·
                        rfl

theorem cell23_7736655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_7736655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736655 prefixEnd_7736655 := by exact prefixLift 7736655
  have htrace : WordTrace (prefixWord ++ tailWord_7736655) baseStart_7736655 baseEnd_7736655 := by
    simpa [prefixWord, tailWord_7736655, baseEnd_7736655] using wordTrace_append hprefix tailTrace_7736655
  have hstable : (prefixWord ++ tailWord_7736655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736655).length < 2 ^ (prefixWord ++ tailWord_7736655).sum := by decide
  have hdescent : baseEnd_7736655 < baseStart_7736655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736666 : List Nat := [3, 1, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_7736666 : Nat := 118140960795 + 7736666 * 2 ^ 59
def prefixEnd_7736666 : Nat := 4983230072969 + 3 ^ 40 * 7736666 * 2
def baseEnd_7736666 : Nat := 1324209440432577497464909

theorem tailTrace_7736666 : CollatzResearch.WordTrace tailWord_7736666 prefixEnd_7736666 1324209440432577497464909 := by
  unfold tailWord_7736666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70544847747346968550615463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188119593992925249468307901 70544847747346968550615463)
  ·
    refine ⟨105817271621020452825923195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70544847747346968550615463 105817271621020452825923195)
    ·
      refine ⟨158725907431530679238884793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105817271621020452825923195 158725907431530679238884793)
      ·
        refine ⟨119044430573648009429163595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158725907431530679238884793 119044430573648009429163595)
        ·
          refine ⟨178566645860472014143745393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119044430573648009429163595 178566645860472014143745393)
          ·
            refine ⟨133924984395354010607809045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178566645860472014143745393 133924984395354010607809045)
            ·
              refine ⟨6277733643532219247241049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133924984395354010607809045 6277733643532219247241049)
              ·
                refine ⟨4708300232649164435430787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6277733643532219247241049 4708300232649164435430787)
                ·
                  refine ⟨7062450348973746653146181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708300232649164435430787 7062450348973746653146181)
                  ·
                    refine ⟨1324209440432577497464909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062450348973746653146181 1324209440432577497464909)
                    ·
                      rfl

theorem cell23_7736666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_7736666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736666 prefixEnd_7736666 := by exact prefixLift 7736666
  have htrace : WordTrace (prefixWord ++ tailWord_7736666) baseStart_7736666 baseEnd_7736666 := by
    simpa [prefixWord, tailWord_7736666, baseEnd_7736666] using wordTrace_append hprefix tailTrace_7736666
  have hstable : (prefixWord ++ tailWord_7736666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736666).length < 2 ^ (prefixWord ++ tailWord_7736666).sum := by decide
  have hdescent : baseEnd_7736666 < baseStart_7736666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736693 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_7736693 : Nat := 118140960795 + 7736693 * 2 ^ 59
def prefixEnd_7736693 : Nat := 4983230072969 + 3 ^ 40 * 7736693 * 2
def baseEnd_7736693 : Nat := 3972642185275403886757103

theorem tailTrace_7736693 : CollatzResearch.WordTrace tailWord_7736693 prefixEnd_7736693 3972642185275403886757103 := by
  unfold tailWord_7736693
  simp only [CollatzResearch.WordTrace]
  refine ⟨282180375760290057813694733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188120250506860038542463155 282180375760290057813694733)
  ·
    refine ⟨105817640910108771680135525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282180375760290057813694733 105817640910108771680135525)
    ·
      refine ⟨19840807670645394690025411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105817640910108771680135525 19840807670645394690025411)
      ·
        refine ⟨29761211505968092035038117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19840807670645394690025411 29761211505968092035038117)
        ·
          refine ⟨5580227157369017256569647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29761211505968092035038117 5580227157369017256569647)
          ·
            refine ⟨8370340736053525884854471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580227157369017256569647 8370340736053525884854471)
            ·
              refine ⟨12555511104080288827281707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370340736053525884854471 12555511104080288827281707)
              ·
                refine ⟨18833266656120433240922561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555511104080288827281707 18833266656120433240922561)
                ·
                  refine ⟨14124949992090324930691921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18833266656120433240922561 14124949992090324930691921)
                  ·
                    refine ⟨10593712494067743698018941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14124949992090324930691921 10593712494067743698018941)
                    ·
                      refine ⟨3972642185275403886757103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593712494067743698018941 3972642185275403886757103)
                      ·
                        rfl

theorem cell23_7736693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_7736693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736693 prefixEnd_7736693 := by exact prefixLift 7736693
  have htrace : WordTrace (prefixWord ++ tailWord_7736693) baseStart_7736693 baseEnd_7736693 := by
    simpa [prefixWord, tailWord_7736693, baseEnd_7736693] using wordTrace_append hprefix tailTrace_7736693
  have hstable : (prefixWord ++ tailWord_7736693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736693).length < 2 ^ (prefixWord ++ tailWord_7736693).sum := by decide
  have hdescent : baseEnd_7736693 < baseStart_7736693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736709 : List Nat := [1, 3, 1, 1, 3, 1, 6, 1, 1, 5]
def baseStart_7736709 : Nat := 118140960795 + 7736709 * 2 ^ 59
def prefixEnd_7736709 : Nat := 4983230072969 + 3 ^ 40 * 7736709 * 2
def baseEnd_7736709 : Nat := 1324216800321958608052343

theorem tailTrace_7736709 : CollatzResearch.WordTrace tailWord_7736709 prefixEnd_7736709 1324216800321958608052343 := by
  unfold tailWord_7736709
  simp only [CollatzResearch.WordTrace]
  refine ⟨282180959328232092546277181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188120639552154728364184787 282180959328232092546277181)
  ·
    refine ⟨105817859748087034704853943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282180959328232092546277181 105817859748087034704853943)
    ·
      refine ⟨158726789622130552057280915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105817859748087034704853943 158726789622130552057280915)
      ·
        refine ⟨238090184433195828085921373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158726789622130552057280915 238090184433195828085921373)
        ·
          refine ⟨89283819162448435532220515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238090184433195828085921373 89283819162448435532220515)
          ·
            refine ⟨133925728743672653298330773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89283819162448435532220515 133925728743672653298330773)
            ·
              refine ⟨6277768534859655623359255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133925728743672653298330773 6277768534859655623359255)
              ·
                refine ⟨9416652802289483435038883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277768534859655623359255 9416652802289483435038883)
                ·
                  refine ⟨14124979203434225152558325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9416652802289483435038883 14124979203434225152558325)
                  ·
                    refine ⟨1324216800321958608052343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14124979203434225152558325 1324216800321958608052343)
                    ·
                      rfl

theorem cell23_7736709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 6, 1, 1, 5].length) (baseStart_7736709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736709 prefixEnd_7736709 := by exact prefixLift 7736709
  have htrace : WordTrace (prefixWord ++ tailWord_7736709) baseStart_7736709 baseEnd_7736709 := by
    simpa [prefixWord, tailWord_7736709, baseEnd_7736709] using wordTrace_append hprefix tailTrace_7736709
  have hstable : (prefixWord ++ tailWord_7736709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736709).length < 2 ^ (prefixWord ++ tailWord_7736709).sum := by decide
  have hdescent : baseEnd_7736709 < baseStart_7736709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736755 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6]
def baseStart_7736755 : Nat := 118140960795 + 7736755 * 2 ^ 59
def prefixEnd_7736755 : Nat := 4983230072969 + 3 ^ 40 * 7736755 * 2
def baseEnd_7736755 : Nat := 3972674021075982644181817

theorem tailTrace_7736755 : CollatzResearch.WordTrace tailWord_7736755 prefixEnd_7736755 3972674021075982644181817 := by
  unfold tailWord_7736755
  simp only [CollatzResearch.WordTrace]
  refine ⟨282182637086065442402451719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188121758057376961601634479 282182637086065442402451719)
  ·
    refine ⟨423273955629098163603677579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282182637086065442402451719 423273955629098163603677579)
    ·
      refine ⟨634910933443647245405516369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423273955629098163603677579 634910933443647245405516369)
      ·
        refine ⟨476183200082735434054137277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 634910933443647245405516369 476183200082735434054137277)
        ·
          refine ⟨178568700031025787770301479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476183200082735434054137277 178568700031025787770301479)
          ·
            refine ⟨267853050046538681655452219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178568700031025787770301479 267853050046538681655452219)
            ·
              refine ⟨401779575069808022483178329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267853050046538681655452219 401779575069808022483178329)
              ·
                refine ⟨301334681302356016862383747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401779575069808022483178329 301334681302356016862383747)
                ·
                  refine ⟨452002021953534025293575621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301334681302356016862383747 452002021953534025293575621)
                  ·
                    refine ⟨84750379116287629742545429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 452002021953534025293575621 84750379116287629742545429)
                    ·
                      refine ⟨3972674021075982644181817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84750379116287629742545429 3972674021075982644181817)
                      ·
                        rfl

theorem cell23_7736755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_7736755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736755 prefixEnd_7736755 := by exact prefixLift 7736755
  have htrace : WordTrace (prefixWord ++ tailWord_7736755) baseStart_7736755 baseEnd_7736755 := by
    simpa [prefixWord, tailWord_7736755, baseEnd_7736755] using wordTrace_append hprefix tailTrace_7736755
  have hstable : (prefixWord ++ tailWord_7736755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736755).length < 2 ^ (prefixWord ++ tailWord_7736755).sum := by decide
  have hdescent : baseEnd_7736755 < baseStart_7736755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736779 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 3]
def baseStart_7736779 : Nat := 118140960795 + 7736779 * 2 ^ 59
def prefixEnd_7736779 : Nat := 4983230072969 + 3 ^ 40 * 7736779 * 2
def baseEnd_7736779 : Nat := 3972686344611690550281707

theorem tailTrace_7736779 : CollatzResearch.WordTrace tailWord_7736779 prefixEnd_7736779 3972686344611690550281707 := by
  unfold tailWord_7736779
  simp only [CollatzResearch.WordTrace]
  refine ⟨282183512437978494501325391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188122341625318996334216927 282183512437978494501325391)
  ·
    refine ⟨423275268656967741751988087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282183512437978494501325391 423275268656967741751988087)
    ·
      refine ⟨634912902985451612627982131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423275268656967741751988087 634912902985451612627982131)
      ·
        refine ⟨952369354478177418941973197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634912902985451612627982131 952369354478177418941973197)
        ·
          refine ⟨357138507929316532103239949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952369354478177418941973197 357138507929316532103239949)
          ·
            refine ⟨133926940473493699538714981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357138507929316532103239949 133926940473493699538714981)
            ·
              refine ⟨25111301338780068663509059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133926940473493699538714981 25111301338780068663509059)
              ·
                refine ⟨37666952008170102995263589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25111301338780068663509059 37666952008170102995263589)
                ·
                  refine ⟨7062553501531894311611923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37666952008170102995263589 7062553501531894311611923)
                  ·
                    refine ⟨10593830252297841467417885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7062553501531894311611923 10593830252297841467417885)
                    ·
                      refine ⟨3972686344611690550281707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593830252297841467417885 3972686344611690550281707)
                      ·
                        rfl

theorem cell23_7736779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 4, 1, 3].length) (baseStart_7736779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736779 prefixEnd_7736779 := by exact prefixLift 7736779
  have htrace : WordTrace (prefixWord ++ tailWord_7736779) baseStart_7736779 baseEnd_7736779 := by
    simpa [prefixWord, tailWord_7736779, baseEnd_7736779] using wordTrace_append hprefix tailTrace_7736779
  have hstable : (prefixWord ++ tailWord_7736779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736779).length < 2 ^ (prefixWord ++ tailWord_7736779).sum := by decide
  have hdescent : baseEnd_7736779 < baseStart_7736779 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736790 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_7736790 : Nat := 118140960795 + 7736790 * 2 ^ 59
def prefixEnd_7736790 : Nat := 4983230072969 + 3 ^ 40 * 7736790 * 2
def baseEnd_7736790 : Nat := 1324230664299630002414719

theorem tailTrace_7736790 : CollatzResearch.WordTrace tailWord_7736790 prefixEnd_7736790 1324230664299630002414719 := by
  unfold tailWord_7736790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17636494602558665211248489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188122609093959095586650549 17636494602558665211248489)
  ·
    refine ⟨13227370951918998908436367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17636494602558665211248489 13227370951918998908436367)
    ·
      refine ⟨19841056427878498362654551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13227370951918998908436367 19841056427878498362654551)
      ·
        refine ⟨29761584641817747543981827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19841056427878498362654551 29761584641817747543981827)
        ·
          refine ⟨44642376962726621315972741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29761584641817747543981827 44642376962726621315972741)
          ·
            refine ⟨8370445680511241496744889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44642376962726621315972741 8370445680511241496744889)
            ·
              refine ⟨6277834260383431122558667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8370445680511241496744889 6277834260383431122558667)
              ·
                refine ⟨9416751390575146683838001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6277834260383431122558667 9416751390575146683838001)
                ·
                  refine ⟨7062563542931360012878501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416751390575146683838001 7062563542931360012878501)
                  ·
                    refine ⟨1324230664299630002414719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7062563542931360012878501 1324230664299630002414719)
                    ·
                      rfl

theorem cell23_7736790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_7736790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736790 prefixEnd_7736790 := by exact prefixLift 7736790
  have htrace : WordTrace (prefixWord ++ tailWord_7736790) baseStart_7736790 baseEnd_7736790 := by
    simpa [prefixWord, tailWord_7736790, baseEnd_7736790] using wordTrace_append hprefix tailTrace_7736790
  have hstable : (prefixWord ++ tailWord_7736790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736790).length < 2 ^ (prefixWord ++ tailWord_7736790).sum := by decide
  have hdescent : baseEnd_7736790 < baseStart_7736790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736839 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7736839 : Nat := 118140960795 + 7736839 * 2 ^ 59
def prefixEnd_7736839 : Nat := 4983230072969 + 3 ^ 40 * 7736839 * 2
def baseEnd_7736839 : Nat := 3972717153450960315531431

theorem tailTrace_7736839 : CollatzResearch.WordTrace tailWord_7736839 prefixEnd_7736839 3972717153450960315531431 := by
  unfold tailWord_7736839
  simp only [CollatzResearch.WordTrace]
  refine ⟨282185700817761124748509571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188123800545174083165673047 282185700817761124748509571)
  ·
    refine ⟨423278551226641687122764357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282185700817761124748509571 423278551226641687122764357)
    ·
      refine ⟨79364728354995316335518317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423278551226641687122764357 79364728354995316335518317)
      ·
        refine ⟨29761773133123243625819369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79364728354995316335518317 29761773133123243625819369)
        ·
          refine ⟨22321329849842432719364527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29761773133123243625819369 22321329849842432719364527)
          ·
            refine ⟨33481994774763649079046791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22321329849842432719364527 33481994774763649079046791)
            ·
              refine ⟨50222992162145473618570187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33481994774763649079046791 50222992162145473618570187)
              ·
                refine ⟨75334488243218210427855281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50222992162145473618570187 75334488243218210427855281)
                ·
                  refine ⟨56500866182413657820891461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75334488243218210427855281 56500866182413657820891461)
                  ·
                    refine ⟨10593912409202560841417149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56500866182413657820891461 10593912409202560841417149)
                    ·
                      refine ⟨3972717153450960315531431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10593912409202560841417149 3972717153450960315531431)
                      ·
                        rfl

theorem cell23_7736839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7736839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736839 prefixEnd_7736839 := by exact prefixLift 7736839
  have htrace : WordTrace (prefixWord ++ tailWord_7736839) baseStart_7736839 baseEnd_7736839 := by
    simpa [prefixWord, tailWord_7736839, baseEnd_7736839] using wordTrace_append hprefix tailTrace_7736839
  have hstable : (prefixWord ++ tailWord_7736839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736839).length < 2 ^ (prefixWord ++ tailWord_7736839).sum := by decide
  have hdescent : baseEnd_7736839 < baseStart_7736839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736853 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_7736853 : Nat := 118140960795 + 7736853 * 2 ^ 59
def prefixEnd_7736853 : Nat := 4983230072969 + 3 ^ 40 * 7736853 * 2
def baseEnd_7736853 : Nat := 3972724342180123260756367

theorem tailTrace_7736853 : CollatzResearch.WordTrace tailWord_7736853 prefixEnd_7736853 3972724342180123260756367 := by
  unfold tailWord_7736853
  simp only [CollatzResearch.WordTrace]
  refine ⟨282186211439710405139519213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188124140959806936759679475 282186211439710405139519213)
  ·
    refine ⟨105819829289891401927319705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282186211439710405139519213 105819829289891401927319705)
    ·
      refine ⟨79364871967418551445489779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105819829289891401927319705 79364871967418551445489779)
      ·
        refine ⟨119047307951127827168234669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79364871967418551445489779 119047307951127827168234669)
        ·
          refine ⟨44642740481672935188088001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119047307951127827168234669 44642740481672935188088001)
          ·
            refine ⟨33482055361254701391066001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44642740481672935188088001 33482055361254701391066001)
            ·
              refine ⟨25111541520941026043299501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33482055361254701391066001 25111541520941026043299501)
              ·
                refine ⟨9416828070352884766237313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25111541520941026043299501 9416828070352884766237313)
                ·
                  refine ⟨7062621052764663574677985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9416828070352884766237313 7062621052764663574677985)
                  ·
                    refine ⟨5296965789573497681008489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062621052764663574677985 5296965789573497681008489)
                    ·
                      refine ⟨3972724342180123260756367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5296965789573497681008489 3972724342180123260756367)
                      ·
                        rfl

theorem cell23_7736853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_7736853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736853 prefixEnd_7736853 := by exact prefixLift 7736853
  have htrace : WordTrace (prefixWord ++ tailWord_7736853) baseStart_7736853 baseEnd_7736853 := by
    simpa [prefixWord, tailWord_7736853, baseEnd_7736853] using wordTrace_append hprefix tailTrace_7736853
  have hstable : (prefixWord ++ tailWord_7736853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736853).length < 2 ^ (prefixWord ++ tailWord_7736853).sum := by decide
  have hdescent : baseEnd_7736853 < baseStart_7736853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736929 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 3]
def baseStart_7736929 : Nat := 118140960795 + 7736929 * 2 ^ 59
def prefixEnd_7736929 : Nat := 4983230072969 + 3 ^ 40 * 7736929 * 2
def baseEnd_7736929 : Nat := 3972763366709864963406017

theorem tailTrace_7736929 : CollatzResearch.WordTrace tailWord_7736929 prefixEnd_7736929 3972763366709864963406017 := by
  unfold tailWord_7736929
  simp only [CollatzResearch.WordTrace]
  refine ⟨282188983387435070119285841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188125988924956713412857227 282188983387435070119285841)
  ·
    refine ⟨211641737540576302589464381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282188983387435070119285841 211641737540576302589464381)
    ·
      refine ⟨79365651577716113471049143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211641737540576302589464381 79365651577716113471049143)
      ·
        refine ⟨119048477366574170206573715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79365651577716113471049143 119048477366574170206573715)
        ·
          refine ⟨178572716049861255309860573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119048477366574170206573715 178572716049861255309860573)
          ·
            refine ⟨66964768518697970741197715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178572716049861255309860573 66964768518697970741197715)
            ·
              refine ⟨100447152778046956111796573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66964768518697970741197715 100447152778046956111796573)
              ·
                refine ⟨37667682291767608541923715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100447152778046956111796573 37667682291767608541923715)
                ·
                  refine ⟨56501523437651412812885573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37667682291767608541923715 56501523437651412812885573)
                  ·
                    refine ⟨10594035644559639902416045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56501523437651412812885573 10594035644559639902416045)
                    ·
                      refine ⟨3972763366709864963406017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594035644559639902416045 3972763366709864963406017)
                      ·
                        rfl

theorem cell23_7736929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_7736929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736929 prefixEnd_7736929 := by exact prefixLift 7736929
  have htrace : WordTrace (prefixWord ++ tailWord_7736929) baseStart_7736929 baseEnd_7736929 := by
    simpa [prefixWord, tailWord_7736929, baseEnd_7736929] using wordTrace_append hprefix tailTrace_7736929
  have hstable : (prefixWord ++ tailWord_7736929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736929).length < 2 ^ (prefixWord ++ tailWord_7736929).sum := by decide
  have hdescent : baseEnd_7736929 < baseStart_7736929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736946 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_7736946 : Nat := 118140960795 + 7736946 * 2 ^ 59
def prefixEnd_7736946 : Nat := 4983230072969 + 3 ^ 40 * 7736946 * 2
def baseEnd_7736946 : Nat := 3972772095880991396893439

theorem tailTrace_7736946 : CollatzResearch.WordTrace tailWord_7736946 prefixEnd_7736946 3972772095880991396893439 := by
  unfold tailWord_7736946
  simp only [CollatzResearch.WordTrace]
  refine ⟨70547400857093370505663673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188126402285582321348436461 70547400857093370505663673)
  ·
    refine ⟨52910550642820027879247755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70547400857093370505663673 52910550642820027879247755)
    ·
      refine ⟨79365825964230041818871633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52910550642820027879247755 79365825964230041818871633)
      ·
        refine ⟨59524369473172531364153725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79365825964230041818871633 59524369473172531364153725)
        ·
          refine ⟨22321638552439699261557647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59524369473172531364153725 22321638552439699261557647)
          ·
            refine ⟨33482457828659548892336471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22321638552439699261557647 33482457828659548892336471)
            ·
              refine ⟨50223686742989323338504707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33482457828659548892336471 50223686742989323338504707)
              ·
                refine ⟨75335530114483985007757061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50223686742989323338504707 75335530114483985007757061)
                ·
                  refine ⟨14125411896465747188954449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75335530114483985007757061 14125411896465747188954449)
                  ·
                    refine ⟨10594058922349310391715837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14125411896465747188954449 10594058922349310391715837)
                    ·
                      refine ⟨3972772095880991396893439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594058922349310391715837 3972772095880991396893439)
                      ·
                        rfl

theorem cell23_7736946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_7736946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736946 prefixEnd_7736946 := by exact prefixLift 7736946
  have htrace : WordTrace (prefixWord ++ tailWord_7736946) baseStart_7736946 baseEnd_7736946 := by
    simpa [prefixWord, tailWord_7736946, baseEnd_7736946] using wordTrace_append hprefix tailTrace_7736946
  have hstable : (prefixWord ++ tailWord_7736946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736946).length < 2 ^ (prefixWord ++ tailWord_7736946).sum := by decide
  have hdescent : baseEnd_7736946 < baseStart_7736946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736976 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3]
def baseStart_7736976 : Nat := 118140960795 + 7736976 * 2 ^ 59
def prefixEnd_7736976 : Nat := 4983230072969 + 3 ^ 40 * 7736976 * 2
def baseEnd_7736976 : Nat := 3972787500300626279518301

theorem tailTrace_7736976 : CollatzResearch.WordTrace tailWord_7736976 prefixEnd_7736976 3972787500300626279518301 := by
  unfold tailWord_7736976
  simp only [CollatzResearch.WordTrace]
  refine ⟨141095348809132398573123391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188127131745509864764164521 141095348809132398573123391)
  ·
    refine ⟨211643023213698597859685087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141095348809132398573123391 211643023213698597859685087)
    ·
      refine ⟨317464534820547896789527631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211643023213698597859685087 317464534820547896789527631)
      ·
        refine ⟨476196802230821845184291447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317464534820547896789527631 476196802230821845184291447)
        ·
          refine ⟨714295203346232767776437171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476196802230821845184291447 714295203346232767776437171)
          ·
            refine ⟨1071442805019349151664655757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714295203346232767776437171 1071442805019349151664655757)
            ·
              refine ⟨401791051882255931874245909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071442805019349151664655757 401791051882255931874245909)
              ·
                refine ⟨18833955556980746806605277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401791051882255931874245909 18833955556980746806605277)
                ·
                  refine ⟨7062733333867780052476979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18833955556980746806605277 7062733333867780052476979)
                  ·
                    refine ⟨10594100000801670078715469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7062733333867780052476979 10594100000801670078715469)
                    ·
                      refine ⟨3972787500300626279518301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594100000801670078715469 3972787500300626279518301)
                      ·
                        rfl

theorem cell23_7736976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_7736976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736976 prefixEnd_7736976 := by exact prefixLift 7736976
  have htrace : WordTrace (prefixWord ++ tailWord_7736976) baseStart_7736976 baseEnd_7736976 := by
    simpa [prefixWord, tailWord_7736976, baseEnd_7736976] using wordTrace_append hprefix tailTrace_7736976
  have hstable : (prefixWord ++ tailWord_7736976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736976).length < 2 ^ (prefixWord ++ tailWord_7736976).sum := by decide
  have hdescent : baseEnd_7736976 < baseStart_7736976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7736980 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7736980 : Nat := 118140960795 + 7736980 * 2 ^ 59
def prefixEnd_7736980 : Nat := 4983230072969 + 3 ^ 40 * 7736980 * 2
def baseEnd_7736980 : Nat := 3972789554223244263868283

theorem tailTrace_7736980 : CollatzResearch.WordTrace tailWord_7736980 prefixEnd_7736980 3972789554223244263868283 := by
  unfold tailWord_7736980
  simp only [CollatzResearch.WordTrace]
  refine ⟨141095421755125152914696197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188127229006833537219594929 141095421755125152914696197)
  ·
    refine ⟨26455391579085966171505537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141095421755125152914696197 26455391579085966171505537)
    ·
      refine ⟨19841543684314474628629153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26455391579085966171505537 19841543684314474628629153)
      ·
        refine ⟨14881157763235855971471865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19841543684314474628629153 14881157763235855971471865)
        ·
          refine ⟨11160868322426891978603899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881157763235855971471865 11160868322426891978603899)
          ·
            refine ⟨16741302483640337967905849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11160868322426891978603899 16741302483640337967905849)
            ·
              refine ⟨12555976862730253475929387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16741302483640337967905849 12555976862730253475929387)
              ·
                refine ⟨18833965294095380213894081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12555976862730253475929387 18833965294095380213894081)
                ·
                  refine ⟨14125473970571535160420561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18833965294095380213894081 14125473970571535160420561)
                  ·
                    refine ⟨10594105477928651370315421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14125473970571535160420561 10594105477928651370315421)
                    ·
                      refine ⟨3972789554223244263868283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594105477928651370315421 3972789554223244263868283)
                      ·
                        rfl

theorem cell23_7736980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7736980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7736980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7736980 prefixEnd_7736980 := by exact prefixLift 7736980
  have htrace : WordTrace (prefixWord ++ tailWord_7736980) baseStart_7736980 baseEnd_7736980 := by
    simpa [prefixWord, tailWord_7736980, baseEnd_7736980] using wordTrace_append hprefix tailTrace_7736980
  have hstable : (prefixWord ++ tailWord_7736980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7736980).length < 2 ^ (prefixWord ++ tailWord_7736980).sum := by decide
  have hdescent : baseEnd_7736980 < baseStart_7736980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7736980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737019 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5]
def baseStart_7737019 : Nat := 118140960795 + 7737019 * 2 ^ 59
def prefixEnd_7737019 : Nat := 4983230072969 + 3 ^ 40 * 7737019 * 2
def baseEnd_7737019 : Nat := 3972809579968769611280603

theorem tailTrace_7737019 : CollatzResearch.WordTrace tailWord_7737019 prefixEnd_7737019 3972809579968769611280603 := by
  unfold tailWord_7737019
  simp only [CollatzResearch.WordTrace]
  refine ⟨282192265957109015490062111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188128177304739343660041407 282192265957109015490062111)
  ·
    refine ⟨423288398935663523235093167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282192265957109015490062111 423288398935663523235093167)
    ·
      refine ⟨634932598403495284852639751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423288398935663523235093167 634932598403495284852639751)
      ·
        refine ⟨952398897605242927278959627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634932598403495284852639751 952398897605242927278959627)
        ·
          refine ⟨1428598346407864390918439441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952398897605242927278959627 1428598346407864390918439441)
          ·
            refine ⟨1071448759805898293188829581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428598346407864390918439441 1071448759805898293188829581)
            ·
              refine ⟨401793284927211859945811093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071448759805898293188829581 401793284927211859945811093)
              ·
                refine ⟨18834060230963055934959895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 401793284927211859945811093 18834060230963055934959895)
                ·
                  refine ⟨28251090346444583902439843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18834060230963055934959895 28251090346444583902439843)
                  ·
                    refine ⟨42376635519666875853659765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28251090346444583902439843 42376635519666875853659765)
                    ·
                      refine ⟨3972809579968769611280603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42376635519666875853659765 3972809579968769611280603)
                      ·
                        rfl

theorem cell23_7737019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 5].length) (baseStart_7737019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737019 prefixEnd_7737019 := by exact prefixLift 7737019
  have htrace : WordTrace (prefixWord ++ tailWord_7737019) baseStart_7737019 baseEnd_7737019 := by
    simpa [prefixWord, tailWord_7737019, baseEnd_7737019] using wordTrace_append hprefix tailTrace_7737019
  have hstable : (prefixWord ++ tailWord_7737019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737019).length < 2 ^ (prefixWord ++ tailWord_7737019).sum := by decide
  have hdescent : baseEnd_7737019 < baseStart_7737019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737029 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 4]
def baseStart_7737029 : Nat := 118140960795 + 7737029 * 2 ^ 59
def prefixEnd_7737029 : Nat := 4983230072969 + 3 ^ 40 * 7737029 * 2
def baseEnd_7737029 : Nat := 3972814714775314572155557

theorem tailTrace_7737029 : CollatzResearch.WordTrace tailWord_7737029 prefixEnd_7737029 3972814714775314572155557 := by
  unfold tailWord_7737029
  simp only [CollatzResearch.WordTrace]
  refine ⟨282192630687072787197926141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188128420458048524798617427 282192630687072787197926141)
  ·
    refine ⟨105822236507652295199222303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282192630687072787197926141 105822236507652295199222303)
    ·
      refine ⟨158733354761478442798833455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105822236507652295199222303 158733354761478442798833455)
      ·
        refine ⟨238100032142217664198250183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158733354761478442798833455 238100032142217664198250183)
        ·
          refine ⟨357150048213326496297375275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238100032142217664198250183 357150048213326496297375275)
          ·
            refine ⟨535725072319989744446062913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357150048213326496297375275 535725072319989744446062913)
            ·
              refine ⟨401793804239992308334547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535725072319989744446062913 401793804239992308334547185)
              ·
                refine ⟨301345353179994231250910389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401793804239992308334547185 301345353179994231250910389)
                ·
                  refine ⟨28251126860624459179772849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301345353179994231250910389 28251126860624459179772849)
                  ·
                    refine ⟨21188345145468344384829637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28251126860624459179772849 21188345145468344384829637)
                    ·
                      refine ⟨3972814714775314572155557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21188345145468344384829637 3972814714775314572155557)
                      ·
                        rfl

theorem cell23_7737029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_7737029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737029 prefixEnd_7737029 := by exact prefixLift 7737029
  have htrace : WordTrace (prefixWord ++ tailWord_7737029) baseStart_7737029 baseEnd_7737029 := by
    simpa [prefixWord, tailWord_7737029, baseEnd_7737029] using wordTrace_append hprefix tailTrace_7737029
  have hstable : (prefixWord ++ tailWord_7737029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737029).length < 2 ^ (prefixWord ++ tailWord_7737029).sum := by decide
  have hdescent : baseEnd_7737029 < baseStart_7737029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737030 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_7737030 : Nat := 118140960795 + 7737030 * 2 ^ 59
def prefixEnd_7737030 : Nat := 4983230072969 + 3 ^ 40 * 7737030 * 2
def baseEnd_7737030 : Nat := 1324271742751989689414351

theorem tailTrace_7737030 : CollatzResearch.WordTrace tailWord_7737030 prefixEnd_7737030 1324271742751989689414351 := by
  unfold tailWord_7737030
  simp only [CollatzResearch.WordTrace]
  refine ⟨8818520848752161386522267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 188128444773379442912475029 8818520848752161386522267)
  ·
    refine ⟨13227781273128242079783401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8818520848752161386522267 13227781273128242079783401)
    ·
      refine ⟨9920835954846181559837551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227781273128242079783401 9920835954846181559837551)
      ·
        refine ⟨14881253932269272339756327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920835954846181559837551 14881253932269272339756327)
        ·
          refine ⟨22321880898403908509634491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14881253932269272339756327 22321880898403908509634491)
          ·
            refine ⟨33482821347605862764451737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22321880898403908509634491 33482821347605862764451737)
            ·
              refine ⟨25112116010704397073338803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33482821347605862764451737 25112116010704397073338803)
              ·
                refine ⟨37668174016056595610008205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25112116010704397073338803 37668174016056595610008205)
                ·
                  refine ⟨14125565256021223353753077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37668174016056595610008205 14125565256021223353753077)
                  ·
                    refine ⟨1324271742751989689414351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14125565256021223353753077 1324271742751989689414351)
                    ·
                      rfl

theorem cell23_7737030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_7737030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737030 prefixEnd_7737030 := by exact prefixLift 7737030
  have htrace : WordTrace (prefixWord ++ tailWord_7737030) baseStart_7737030 baseEnd_7737030 := by
    simpa [prefixWord, tailWord_7737030, baseEnd_7737030] using wordTrace_append hprefix tailTrace_7737030
  have hstable : (prefixWord ++ tailWord_7737030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737030).length < 2 ^ (prefixWord ++ tailWord_7737030).sum := by decide
  have hdescent : baseEnd_7737030 < baseStart_7737030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737037 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_7737037 : Nat := 118140960795 + 7737037 * 2 ^ 59
def prefixEnd_7737037 : Nat := 4983230072969 + 3 ^ 40 * 7737037 * 2
def baseEnd_7737037 : Nat := 3972818822620550540855521

theorem tailTrace_7737037 : CollatzResearch.WordTrace tailWord_7737037 prefixEnd_7737037 3972818822620550540855521 := by
  unfold tailWord_7737037
  simp only [CollatzResearch.WordTrace]
  refine ⟨282192922471043804564217365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188128614980695869709478243 282192922471043804564217365)
  ·
    refine ⟨13227793240830178338947689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282192922471043804564217365 13227793240830178338947689)
    ·
      refine ⟨9920844930622633754210767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227793240830178338947689 9920844930622633754210767)
      ·
        refine ⟨14881267395933950631316151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9920844930622633754210767 14881267395933950631316151)
        ·
          refine ⟨22321901093900925946974227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14881267395933950631316151 22321901093900925946974227)
          ·
            refine ⟨33482851640851388920461341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22321901093900925946974227 33482851640851388920461341)
            ·
              refine ⟨12556069365319270845173003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33482851640851388920461341 12556069365319270845173003)
              ·
                refine ⟨18834104047978906267759505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556069365319270845173003 18834104047978906267759505)
                ·
                  refine ⟨14125578035984179700819629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18834104047978906267759505 14125578035984179700819629)
                  ·
                    refine ⟨5297091763494067387807361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14125578035984179700819629 5297091763494067387807361)
                    ·
                      refine ⟨3972818822620550540855521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297091763494067387807361 3972818822620550540855521)
                      ·
                        rfl

theorem cell23_7737037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_7737037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737037 prefixEnd_7737037 := by exact prefixLift 7737037
  have htrace : WordTrace (prefixWord ++ tailWord_7737037) baseStart_7737037 baseEnd_7737037 := by
    simpa [prefixWord, tailWord_7737037, baseEnd_7737037] using wordTrace_append hprefix tailTrace_7737037
  have hstable : (prefixWord ++ tailWord_7737037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737037).length < 2 ^ (prefixWord ++ tailWord_7737037).sum := by decide
  have hdescent : baseEnd_7737037 < baseStart_7737037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737050 : List Nat := [3, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4]
def baseStart_7737050 : Nat := 118140960795 + 7737050 * 2 ^ 59
def prefixEnd_7737050 : Nat := 4983230072969 + 3 ^ 40 * 7737050 * 2
def baseEnd_7737050 : Nat := 3972825497869058989992961

theorem tailTrace_7737050 : CollatzResearch.WordTrace tailWord_7737050 prefixEnd_7737050 3972825497869058989992961 := by
  unfold tailWord_7737050
  simp only [CollatzResearch.WordTrace]
  refine ⟨70548349154999176946110151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188128931079997805189627069 70548349154999176946110151)
  ·
    refine ⟨105822523732498765419165227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70548349154999176946110151 105822523732498765419165227)
    ·
      refine ⟨158733785598748148128747841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105822523732498765419165227 158733785598748148128747841)
      ·
        refine ⟨119050339199061111096560881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158733785598748148128747841 119050339199061111096560881)
        ·
          refine ⟨89287754399295833322420661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119050339199061111096560881 89287754399295833322420661)
          ·
            refine ⟨8370726974933984373976937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89287754399295833322420661 8370726974933984373976937)
            ·
              refine ⟨6278045231200488280482703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8370726974933984373976937 6278045231200488280482703)
              ·
                refine ⟨9417067846800732420724055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278045231200488280482703 9417067846800732420724055)
                ·
                  refine ⟨14125601770201098631086083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9417067846800732420724055 14125601770201098631086083)
                  ·
                    refine ⟨21188402655301647946629125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14125601770201098631086083 21188402655301647946629125)
                    ·
                      refine ⟨3972825497869058989992961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21188402655301647946629125 3972825497869058989992961)
                      ·
                        rfl

theorem cell23_7737050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_7737050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737050 prefixEnd_7737050 := by exact prefixLift 7737050
  have htrace : WordTrace (prefixWord ++ tailWord_7737050) baseStart_7737050 baseEnd_7737050 := by
    simpa [prefixWord, tailWord_7737050, baseEnd_7737050] using wordTrace_append hprefix tailTrace_7737050
  have hstable : (prefixWord ++ tailWord_7737050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737050).length < 2 ^ (prefixWord ++ tailWord_7737050).sum := by decide
  have hdescent : baseEnd_7737050 < baseStart_7737050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737066 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_7737066 : Nat := 118140960795 + 7737066 * 2 ^ 59
def prefixEnd_7737066 : Nat := 4983230072969 + 3 ^ 40 * 7737066 * 2
def baseEnd_7737066 : Nat := 3972833713559530927392887

theorem tailTrace_7737066 : CollatzResearch.WordTrace tailWord_7737066 prefixEnd_7737066 3972833713559530927392887 := by
  unfold tailWord_7737066
  simp only [CollatzResearch.WordTrace]
  refine ⟨70548495046984685629255763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188129320125292495011348701 70548495046984685629255763)
  ·
    refine ⟨105822742570477028443883645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70548495046984685629255763 105822742570477028443883645)
    ·
      refine ⟨39683528463928885666456367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105822742570477028443883645 39683528463928885666456367)
      ·
        refine ⟨59525292695893328499684551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39683528463928885666456367 59525292695893328499684551)
        ·
          refine ⟨89287939043839992749526827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59525292695893328499684551 89287939043839992749526827)
          ·
            refine ⟨133931908565759989124290241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89287939043839992749526827 133931908565759989124290241)
            ·
              refine ⟨100448931424319991843217681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133931908565759989124290241 100448931424319991843217681)
              ·
                refine ⟨75336698568239993882413261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100448931424319991843217681 75336698568239993882413261)
                ·
                  refine ⟨28251261963089997705904973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75336698568239993882413261 28251261963089997705904973)
                  ·
                    refine ⟨10594223236158749139714365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28251261963089997705904973 10594223236158749139714365)
                    ·
                      refine ⟨3972833713559530927392887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594223236158749139714365 3972833713559530927392887)
                      ·
                        rfl

theorem cell23_7737066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_7737066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737066 prefixEnd_7737066 := by exact prefixLift 7737066
  have htrace : WordTrace (prefixWord ++ tailWord_7737066) baseStart_7737066 baseEnd_7737066 := by
    simpa [prefixWord, tailWord_7737066, baseEnd_7737066] using wordTrace_append hprefix tailTrace_7737066
  have hstable : (prefixWord ++ tailWord_7737066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737066).length < 2 ^ (prefixWord ++ tailWord_7737066).sum := by decide
  have hdescent : baseEnd_7737066 < baseStart_7737066 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737099 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 8]
def baseStart_7737099 : Nat := 118140960795 + 7737099 * 2 ^ 59
def prefixEnd_7737099 : Nat := 4983230072969 + 3 ^ 40 * 7737099 * 2
def baseEnd_7737099 : Nat := 1324283552807043099426745

theorem tailTrace_7737099 : CollatzResearch.WordTrace tailWord_7737099 prefixEnd_7737099 1324283552807043099426745 := by
  unfold tailWord_7737099
  simp only [CollatzResearch.WordTrace]
  refine ⟨282195183796819189152974351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188130122531212792768649567 282195183796819189152974351)
  ·
    refine ⟨423292775695228783729461527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282195183796819189152974351 423292775695228783729461527)
    ·
      refine ⟨634939163542843175594192291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423292775695228783729461527 634939163542843175594192291)
      ·
        refine ⟨952408745314264763391288437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634939163542843175594192291 952408745314264763391288437)
        ·
          refine ⟨89288319873212321567933291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 952408745314264763391288437 89288319873212321567933291)
          ·
            refine ⟨133932479809818482351899937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89288319873212321567933291 133932479809818482351899937)
            ·
              refine ⟨100449359857363861763924953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133932479809818482351899937 100449359857363861763924953)
              ·
                refine ⟨75337019893022896322943715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100449359857363861763924953 75337019893022896322943715)
                ·
                  refine ⟨113005529839534344484415573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75337019893022896322943715 113005529839534344484415573)
                  ·
                    refine ⟨1324283552807043099426745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113005529839534344484415573 1324283552807043099426745)
                    ·
                      rfl

theorem cell23_7737099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 8].length) (baseStart_7737099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737099 prefixEnd_7737099 := by exact prefixLift 7737099
  have htrace : WordTrace (prefixWord ++ tailWord_7737099) baseStart_7737099 baseEnd_7737099 := by
    simpa [prefixWord, tailWord_7737099, baseEnd_7737099] using wordTrace_append hprefix tailTrace_7737099
  have hstable : (prefixWord ++ tailWord_7737099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737099).length < 2 ^ (prefixWord ++ tailWord_7737099).sum := by decide
  have hdescent : baseEnd_7737099 < baseStart_7737099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737118 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7737118 : Nat := 118140960795 + 7737118 * 2 ^ 59
def prefixEnd_7737118 : Nat := 4983230072969 + 3 ^ 40 * 7737118 * 2
def baseEnd_7737118 : Nat := 3972860414553564723942649

theorem tailTrace_7737118 : CollatzResearch.WordTrace tailWord_7737118 prefixEnd_7737118 3972860414553564723942649 := by
  unfold tailWord_7737118
  simp only [CollatzResearch.WordTrace]
  refine ⟨35274484597968794424739501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188130584522500236931944005 35274484597968794424739501)
  ·
    refine ⟨13227931724238297909277313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35274484597968794424739501 13227931724238297909277313)
    ·
      refine ⟨9920948793178723431957985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13227931724238297909277313 9920948793178723431957985)
      ·
        refine ⟨7440711594884042573968489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9920948793178723431957985 7440711594884042573968489)
        ·
          refine ⟨5580533696163031930476367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7440711594884042573968489 5580533696163031930476367)
          ·
            refine ⟨8370800544244547895714551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5580533696163031930476367 8370800544244547895714551)
            ·
              refine ⟨12556200816366821843571827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8370800544244547895714551 12556200816366821843571827)
              ·
                refine ⟨18834301224550232765357741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556200816366821843571827 18834301224550232765357741)
                ·
                  refine ⟨7062862959206337287009153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18834301224550232765357741 7062862959206337287009153)
                  ·
                    refine ⟨5297147219404752965256865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7062862959206337287009153 5297147219404752965256865)
                    ·
                      refine ⟨3972860414553564723942649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297147219404752965256865 3972860414553564723942649)
                      ·
                        rfl

theorem cell23_7737118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7737118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737118 prefixEnd_7737118 := by exact prefixLift 7737118
  have htrace : WordTrace (prefixWord ++ tailWord_7737118) baseStart_7737118 baseEnd_7737118 := by
    simpa [prefixWord, tailWord_7737118, baseEnd_7737118] using wordTrace_append hprefix tailTrace_7737118
  have hstable : (prefixWord ++ tailWord_7737118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737118).length < 2 ^ (prefixWord ++ tailWord_7737118).sum := by decide
  have hdescent : baseEnd_7737118 < baseStart_7737118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737183 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 2, 5, 2]
def baseStart_7737183 : Nat := 118140960795 + 7737183 * 2 ^ 59
def prefixEnd_7737183 : Nat := 4983230072969 + 3 ^ 40 * 7737183 * 2
def baseEnd_7737183 : Nat := 3972893790796106969629849

theorem tailTrace_7737183 : CollatzResearch.WordTrace tailWord_7737183 prefixEnd_7737183 3972893790796106969629849 := by
  unfold tailWord_7737183
  simp only [CollatzResearch.WordTrace]
  refine ⟨282198247528514871499032203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188132165019009914332688135 282198247528514871499032203)
  ·
    refine ⟨423297371292772307248548305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282198247528514871499032203 423297371292772307248548305)
    ·
      refine ⟨317473028469579230436411229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423297371292772307248548305 317473028469579230436411229)
      ·
        refine ⟨119052385676092211413654211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317473028469579230436411229 119052385676092211413654211)
        ·
          refine ⟨178578578514138317120481317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119052385676092211413654211 178578578514138317120481317)
          ·
            refine ⟨33483483471400934460090247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178578578514138317120481317 33483483471400934460090247)
            ·
              refine ⟨50225225207101401690135371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33483483471400934460090247 50225225207101401690135371)
              ·
                refine ⟨75337837810652102535203057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50225225207101401690135371 75337837810652102535203057)
                ·
                  refine ⟨56503378357989076901402293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75337837810652102535203057 56503378357989076901402293)
                  ·
                    refine ⟨5297191721061475959506465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56503378357989076901402293 5297191721061475959506465)
                    ·
                      refine ⟨3972893790796106969629849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297191721061475959506465 3972893790796106969629849)
                      ·
                        rfl

theorem cell23_7737183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_7737183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737183 prefixEnd_7737183 := by exact prefixLift 7737183
  have htrace : WordTrace (prefixWord ++ tailWord_7737183) baseStart_7737183 baseEnd_7737183 := by
    simpa [prefixWord, tailWord_7737183, baseEnd_7737183] using wordTrace_append hprefix tailTrace_7737183
  have hstable : (prefixWord ++ tailWord_7737183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737183).length < 2 ^ (prefixWord ++ tailWord_7737183).sum := by decide
  have hdescent : baseEnd_7737183 < baseStart_7737183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737213 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_7737213 : Nat := 118140960795 + 7737213 * 2 ^ 59
def prefixEnd_7737213 : Nat := 4983230072969 + 3 ^ 40 * 7737213 * 2
def baseEnd_7737213 : Nat := 3972909195215741852254711

theorem tailTrace_7737213 : CollatzResearch.WordTrace tailWord_7737213 prefixEnd_7737213 3972909195215741852254711 := by
  unfold tailWord_7737213
  simp only [CollatzResearch.WordTrace]
  refine ⟨282199341718406186622624293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188132894478937457748416195 282199341718406186622624293)
  ·
    refine ⟨52912376572201159991742055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282199341718406186622624293 52912376572201159991742055)
    ·
      refine ⟨79368564858301739987613083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52912376572201159991742055 79368564858301739987613083)
      ·
        refine ⟨119052847287452609981419625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79368564858301739987613083 119052847287452609981419625)
        ·
          refine ⟨89289635465589457486064719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119052847287452609981419625 89289635465589457486064719)
          ·
            refine ⟨133934453198384186229097079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89289635465589457486064719 133934453198384186229097079)
            ·
              refine ⟨200901679797576279343645619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133934453198384186229097079 200901679797576279343645619)
              ·
                refine ⟨301352519696364419015468429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200901679797576279343645619 301352519696364419015468429)
                ·
                  refine ⟨113007194886136657130800661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301352519696364419015468429 113007194886136657130800661)
                  ·
                    refine ⟨5297212260287655803006281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113007194886136657130800661 5297212260287655803006281)
                    ·
                      refine ⟨3972909195215741852254711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297212260287655803006281 3972909195215741852254711)
                      ·
                        rfl

theorem cell23_7737213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_7737213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737213 prefixEnd_7737213 := by exact prefixLift 7737213
  have htrace : WordTrace (prefixWord ++ tailWord_7737213) baseStart_7737213 baseEnd_7737213 := by
    simpa [prefixWord, tailWord_7737213, baseEnd_7737213] using wordTrace_append hprefix tailTrace_7737213
  have hstable : (prefixWord ++ tailWord_7737213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737213).length < 2 ^ (prefixWord ++ tailWord_7737213).sum := by decide
  have hdescent : baseEnd_7737213 < baseStart_7737213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737233 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 3]
def baseStart_7737233 : Nat := 118140960795 + 7737233 * 2 ^ 59
def prefixEnd_7737233 : Nat := 4983230072969 + 3 ^ 40 * 7737233 * 2
def baseEnd_7737233 : Nat := 3972919464828831774004619

theorem tailTrace_7737233 : CollatzResearch.WordTrace tailWord_7737233 prefixEnd_7737233 3972919464828831774004619 := by
  unfold tailWord_7737233
  simp only [CollatzResearch.WordTrace]
  refine ⟨282200071178333730038352353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188133380785555820025568235 282200071178333730038352353)
  ·
    refine ⟨211650053383750297528764265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282200071178333730038352353 211650053383750297528764265)
    ·
      refine ⟨158737540037812723146573199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211650053383750297528764265 158737540037812723146573199)
      ·
        refine ⟨238106310056719084719859799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158737540037812723146573199 238106310056719084719859799)
        ·
          refine ⟨357159465085078627079789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238106310056719084719859799 357159465085078627079789699)
          ·
            refine ⟨535739197627617940619684549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357159465085078627079789699 535739197627617940619684549)
            ·
              refine ⟨100451099555178363866190853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 535739197627617940619684549 100451099555178363866190853)
              ·
                refine ⟨18834581166595943224910785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100451099555178363866190853 18834581166595943224910785)
                ·
                  refine ⟨14125935874946957418683089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18834581166595943224910785 14125935874946957418683089)
                  ·
                    refine ⟨10594451906210218064012317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14125935874946957418683089 10594451906210218064012317)
                    ·
                      refine ⟨3972919464828831774004619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594451906210218064012317 3972919464828831774004619)
                      ·
                        rfl

theorem cell23_7737233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_7737233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737233 prefixEnd_7737233 := by exact prefixLift 7737233
  have htrace : WordTrace (prefixWord ++ tailWord_7737233) baseStart_7737233 baseEnd_7737233 := by
    simpa [prefixWord, tailWord_7737233, baseEnd_7737233] using wordTrace_append hprefix tailTrace_7737233
  have hstable : (prefixWord ++ tailWord_7737233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737233).length < 2 ^ (prefixWord ++ tailWord_7737233).sum := by decide
  have hdescent : baseEnd_7737233 < baseStart_7737233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737266 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_7737266 : Nat := 118140960795 + 7737266 * 2 ^ 59
def prefixEnd_7737266 : Nat := 4983230072969 + 3 ^ 40 * 7737266 * 2
def baseEnd_7737266 : Nat := 1324312136563476714963989

theorem tailTrace_7737266 : CollatzResearch.WordTrace tailWord_7737266 prefixEnd_7737266 1324312136563476714963989 := by
  unfold tailWord_7737266
  simp only [CollatzResearch.WordTrace]
  refine ⟨70550318696803544168575913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188134183191476117782869101 70550318696803544168575913)
  ·
    refine ⟨52912739022602658126431935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70550318696803544168575913 52912739022602658126431935)
    ·
      refine ⟨79369108533903987189647903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52912739022602658126431935 79369108533903987189647903)
      ·
        refine ⟨119053662800855980784471855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79369108533903987189647903 119053662800855980784471855)
        ·
          refine ⟨178580494201283971176707783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119053662800855980784471855 178580494201283971176707783)
          ·
            refine ⟨267870741301925956765061675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178580494201283971176707783 267870741301925956765061675)
            ·
              refine ⟨401806111952888935147592513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267870741301925956765061675 401806111952888935147592513)
              ·
                refine ⟨301354583964666701360694385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401806111952888935147592513 301354583964666701360694385)
                ·
                  refine ⟨226015937973500026020520789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301354583964666701360694385 226015937973500026020520789)
                  ·
                    refine ⟨1324312136563476714963989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 226015937973500026020520789 1324312136563476714963989)
                    ·
                      rfl

theorem cell23_7737266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_7737266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737266 prefixEnd_7737266 := by exact prefixLift 7737266
  have htrace : WordTrace (prefixWord ++ tailWord_7737266) baseStart_7737266 baseEnd_7737266 := by
    simpa [prefixWord, tailWord_7737266, baseEnd_7737266] using wordTrace_append hprefix tailTrace_7737266
  have hstable : (prefixWord ++ tailWord_7737266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737266).length < 2 ^ (prefixWord ++ tailWord_7737266).sum := by decide
  have hdescent : baseEnd_7737266 < baseStart_7737266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737290 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_7737290 : Nat := 118140960795 + 7737290 * 2 ^ 59
def prefixEnd_7737290 : Nat := 4983230072969 + 3 ^ 40 * 7737290 * 2
def baseEnd_7737290 : Nat := 3972948733226138050991857

theorem tailTrace_7737290 : CollatzResearch.WordTrace tailWord_7737290 prefixEnd_7737290 3972948733226138050991857 := by
  unfold tailWord_7737290
  simp only [CollatzResearch.WordTrace]
  refine ⟨70550537534781807193294331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188134766759418152515451549 70550537534781807193294331)
  ·
    refine ⟨105825806302172710789941497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70550537534781807193294331 105825806302172710789941497)
    ·
      refine ⟨79369354726629533092456123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105825806302172710789941497 79369354726629533092456123)
      ·
        refine ⟨119054032089944299638684185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79369354726629533092456123 119054032089944299638684185)
        ·
          refine ⟨89290524067458224729013139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119054032089944299638684185 89290524067458224729013139)
          ·
            refine ⟨133935786101187337093519709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89290524067458224729013139 133935786101187337093519709)
            ·
              refine ⟨50225919787945251410069891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133935786101187337093519709 50225919787945251410069891)
              ·
                refine ⟨75338879681917877115104837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50225919787945251410069891 75338879681917877115104837)
                ·
                  refine ⟨14126039940359601959082157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75338879681917877115104837 14126039940359601959082157)
                  ·
                    refine ⟨5297264977634850734655809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14126039940359601959082157 5297264977634850734655809)
                    ·
                      refine ⟨3972948733226138050991857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297264977634850734655809 3972948733226138050991857)
                      ·
                        rfl

theorem cell23_7737290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_7737290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737290 prefixEnd_7737290 := by exact prefixLift 7737290
  have htrace : WordTrace (prefixWord ++ tailWord_7737290) baseStart_7737290 baseEnd_7737290 := by
    simpa [prefixWord, tailWord_7737290, baseEnd_7737290] using wordTrace_append hprefix tailTrace_7737290
  have hstable : (prefixWord ++ tailWord_7737290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737290).length < 2 ^ (prefixWord ++ tailWord_7737290).sum := by decide
  have hdescent : baseEnd_7737290 < baseStart_7737290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737303 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_7737303 : Nat := 118140960795 + 7737303 * 2 ^ 59
def prefixEnd_7737303 : Nat := 4983230072969 + 3 ^ 40 * 7737303 * 2
def baseEnd_7737303 : Nat := 3972955408474646500129297

theorem tailTrace_7737303 : CollatzResearch.WordTrace tailWord_7737303 prefixEnd_7737303 3972955408474646500129297 := by
  unfold tailWord_7737303
  simp only [CollatzResearch.WordTrace]
  refine ⟨282202624288080131993400563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188135082858720087995600375 282202624288080131993400563)
  ·
    refine ⟨423303936432120197990100845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282202624288080131993400563 423303936432120197990100845)
    ·
      refine ⟨158738976162045074246287817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423303936432120197990100845 158738976162045074246287817)
      ·
        refine ⟨119054232121533805684715863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158738976162045074246287817 119054232121533805684715863)
        ·
          refine ⟨178581348182300708527073795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119054232121533805684715863 178581348182300708527073795)
          ·
            refine ⟨267872022273451062790610693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178581348182300708527073795 267872022273451062790610693)
            ·
              refine ⟨50226004176272074273239505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267872022273451062790610693 50226004176272074273239505)
              ·
                refine ⟨37669503132204055704929629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50226004176272074273239505 37669503132204055704929629)
                ·
                  refine ⟨14126063674576520889348611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37669503132204055704929629 14126063674576520889348611)
                  ·
                    refine ⟨21189095511864781334022917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14126063674576520889348611 21189095511864781334022917)
                    ·
                      refine ⟨3972955408474646500129297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21189095511864781334022917 3972955408474646500129297)
                      ·
                        rfl

theorem cell23_7737303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_7737303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737303 prefixEnd_7737303 := by exact prefixLift 7737303
  have htrace : WordTrace (prefixWord ++ tailWord_7737303) baseStart_7737303 baseEnd_7737303 := by
    simpa [prefixWord, tailWord_7737303, baseEnd_7737303] using wordTrace_append hprefix tailTrace_7737303
  have hstable : (prefixWord ++ tailWord_7737303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737303).length < 2 ^ (prefixWord ++ tailWord_7737303).sum := by decide
  have hdescent : baseEnd_7737303 < baseStart_7737303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737334 : List Nat := [5, 1, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_7737334 : Nat := 118140960795 + 7737334 * 2 ^ 59
def prefixEnd_7737334 : Nat := 4983230072969 + 3 ^ 40 * 7737334 * 2
def baseEnd_7737334 : Nat := 1324323775458311959613885

theorem tailTrace_7737334 : CollatzResearch.WordTrace tailWord_7737334 prefixEnd_7737334 1324323775458311959613885 := by
  unfold tailWord_7737334
  simp only [CollatzResearch.WordTrace]
  refine ⟨17637734684435489017986191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188135836633978549525186037 17637734684435489017986191)
  ·
    refine ⟨26456602026653233526979287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17637734684435489017986191 26456602026653233526979287)
    ·
      refine ⟨39684903039979850290468931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26456602026653233526979287 39684903039979850290468931)
      ·
        refine ⟨59527354559969775435703397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39684903039979850290468931 59527354559969775435703397)
        ·
          refine ⟨11161378979994332894194387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59527354559969775435703397 11161378979994332894194387)
          ·
            refine ⟨16742068469991499341291581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161378979994332894194387 16742068469991499341291581)
            ·
              refine ⟨6278275676246812252984343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16742068469991499341291581 6278275676246812252984343)
              ·
                refine ⟨9417413514370218379476515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278275676246812252984343 9417413514370218379476515)
                ·
                  refine ⟨14126120271555327569214773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9417413514370218379476515 14126120271555327569214773)
                  ·
                    refine ⟨1324323775458311959613885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14126120271555327569214773 1324323775458311959613885)
                    ·
                      rfl

theorem cell23_7737334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_7737334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737334 prefixEnd_7737334 := by exact prefixLift 7737334
  have htrace : WordTrace (prefixWord ++ tailWord_7737334) baseStart_7737334 baseEnd_7737334 := by
    simpa [prefixWord, tailWord_7737334, baseEnd_7737334] using wordTrace_append hprefix tailTrace_7737334
  have hstable : (prefixWord ++ tailWord_7737334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737334).length < 2 ^ (prefixWord ++ tailWord_7737334).sum := by decide
  have hdescent : baseEnd_7737334 < baseStart_7737334 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737337 : List Nat := [1, 2, 1, 3, 1, 5, 3, 1, 1, 1, 4]
def baseStart_7737337 : Nat := 118140960795 + 7737337 * 2 ^ 59
def prefixEnd_7737337 : Nat := 4983230072969 + 3 ^ 40 * 7737337 * 2
def baseEnd_7737337 : Nat := 3972972866816899367104141

theorem tailTrace_7737337 : CollatzResearch.WordTrace tailWord_7737337 prefixEnd_7737337 3972972866816899367104141 := by
  unfold tailWord_7737337
  simp only [CollatzResearch.WordTrace]
  refine ⟨282203864369956955800138265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188135909579971303866758843 282203864369956955800138265)
  ·
    refine ⟨211652898277467716850103699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282203864369956955800138265 211652898277467716850103699)
    ·
      refine ⟨317479347416201575275155549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211652898277467716850103699 317479347416201575275155549)
      ·
        refine ⟨119054755281075590728183331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317479347416201575275155549 119054755281075590728183331)
        ·
          refine ⟨178582132921613386092274997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119054755281075590728183331 178582132921613386092274997)
          ·
            refine ⟨16742074961401254946150781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178582132921613386092274997 16742074961401254946150781)
            ·
              refine ⟨6278278110525470604806543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16742074961401254946150781 6278278110525470604806543)
              ·
                refine ⟨9417417165788205907209815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278278110525470604806543 9417417165788205907209815)
                ·
                  refine ⟨14126125748682308860814723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9417417165788205907209815 14126125748682308860814723)
                  ·
                    refine ⟨21189188623023463291222085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14126125748682308860814723 21189188623023463291222085)
                    ·
                      refine ⟨3972972866816899367104141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21189188623023463291222085 3972972866816899367104141)
                      ·
                        rfl

theorem cell23_7737337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_7737337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737337 prefixEnd_7737337 := by exact prefixLift 7737337
  have htrace : WordTrace (prefixWord ++ tailWord_7737337) baseStart_7737337 baseEnd_7737337 := by
    simpa [prefixWord, tailWord_7737337, baseEnd_7737337] using wordTrace_append hprefix tailTrace_7737337
  have hstable : (prefixWord ++ tailWord_7737337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737337).length < 2 ^ (prefixWord ++ tailWord_7737337).sum := by decide
  have hdescent : baseEnd_7737337 < baseStart_7737337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737364 : List Nat := [2, 4, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_7737364 : Nat := 118140960795 + 7737364 * 2 ^ 59
def prefixEnd_7737364 : Nat := 4983230072969 + 3 ^ 40 * 7737364 * 2
def baseEnd_7737364 : Nat := 1324328910264856920488839

theorem tailTrace_7737364 : CollatzResearch.WordTrace tailWord_7737364 prefixEnd_7737364 1324328910264856920488839 := by
  unfold tailWord_7737364
  simp only [CollatzResearch.WordTrace]
  refine ⟨141102424570429569705685573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188136566093906092940914097 141102424570429569705685573)
  ·
    refine ⟨26456704606955544319816045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141102424570429569705685573 26456704606955544319816045)
    ·
      refine ⟨9921264227608329119931017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26456704606955544319816045 9921264227608329119931017)
      ·
        refine ⟨7440948170706246839948263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9921264227608329119931017 7440948170706246839948263)
        ·
          refine ⟨11161422256059370259922395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7440948170706246839948263 11161422256059370259922395)
          ·
            refine ⟨16742133384089055389883593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161422256059370259922395 16742133384089055389883593)
            ·
              refine ⟨12556600038066791542412695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16742133384089055389883593 12556600038066791542412695)
              ·
                refine ⟨18834900057100187313619043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556600038066791542412695 18834900057100187313619043)
                ·
                  refine ⟨28252350085650280970428565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18834900057100187313619043 28252350085650280970428565)
                  ·
                    refine ⟨1324328910264856920488839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28252350085650280970428565 1324328910264856920488839)
                    ·
                      rfl

theorem cell23_7737364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_7737364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737364 prefixEnd_7737364 := by exact prefixLift 7737364
  have htrace : WordTrace (prefixWord ++ tailWord_7737364) baseStart_7737364 baseEnd_7737364 := by
    simpa [prefixWord, tailWord_7737364, baseEnd_7737364] using wordTrace_append hprefix tailTrace_7737364
  have hstable : (prefixWord ++ tailWord_7737364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737364).length < 2 ^ (prefixWord ++ tailWord_7737364).sum := by decide
  have hdescent : baseEnd_7737364 < baseStart_7737364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737367 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7737367 : Nat := 118140960795 + 7737367 * 2 ^ 59
def prefixEnd_7737367 : Nat := 4983230072969 + 3 ^ 40 * 7737367 * 2
def baseEnd_7737367 : Nat := 3972988271236534249729003

theorem tailTrace_7737367 : CollatzResearch.WordTrace tailWord_7737367 prefixEnd_7737367 3972988271236534249729003 := by
  unfold tailWord_7737367
  simp only [CollatzResearch.WordTrace]
  refine ⟨282204958559848270923730355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188136639039898847282486903 282204958559848270923730355)
  ·
    refine ⟨423307437839772406385595533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282204958559848270923730355 423307437839772406385595533)
    ·
      refine ⟨158740289189914652394598325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423307437839772406385595533 158740289189914652394598325)
      ·
        refine ⟨14881902111554498661993593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158740289189914652394598325 14881902111554498661993593)
        ·
          refine ⟨11161426583665873996495195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14881902111554498661993593 11161426583665873996495195)
          ·
            refine ⟨16742139875498810994742793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161426583665873996495195 16742139875498810994742793)
            ·
              refine ⟨12556604906624108246057095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16742139875498810994742793 12556604906624108246057095)
              ·
                refine ⟨18834907359936162369085643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556604906624108246057095 18834907359936162369085643)
                ·
                  refine ⟨28252361039904243553628465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18834907359936162369085643 28252361039904243553628465)
                  ·
                    refine ⟨21189270779928182665221349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28252361039904243553628465 21189270779928182665221349)
                    ·
                      refine ⟨3972988271236534249729003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21189270779928182665221349 3972988271236534249729003)
                      ·
                        rfl

theorem cell23_7737367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7737367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737367 prefixEnd_7737367 := by exact prefixLift 7737367
  have htrace : WordTrace (prefixWord ++ tailWord_7737367) baseStart_7737367 baseEnd_7737367 := by
    simpa [prefixWord, tailWord_7737367, baseEnd_7737367] using wordTrace_append hprefix tailTrace_7737367
  have hstable : (prefixWord ++ tailWord_7737367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737367).length < 2 ^ (prefixWord ++ tailWord_7737367).sum := by decide
  have hdescent : baseEnd_7737367 < baseStart_7737367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737370 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_7737370 : Nat := 118140960795 + 7737370 * 2 ^ 59
def prefixEnd_7737370 : Nat := 4983230072969 + 3 ^ 40 * 7737370 * 2
def baseEnd_7737370 : Nat := 3972989811678497737991489

theorem tailTrace_7737370 : CollatzResearch.WordTrace tailWord_7737370 prefixEnd_7737370 3972989811678497737991489 := by
  unfold tailWord_7737370
  simp only [CollatzResearch.WordTrace]
  refine ⟨70551266994709350609022391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188136711985891601624059709 70551266994709350609022391)
  ·
    refine ⟨105826900492064025913533587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70551266994709350609022391 105826900492064025913533587)
    ·
      refine ⟨158740350738096038870300381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105826900492064025913533587 158740350738096038870300381)
      ·
        refine ⟨59527631526786014576362643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158740350738096038870300381 59527631526786014576362643)
        ·
          refine ⟨89291447290179021864543965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59527631526786014576362643 89291447290179021864543965)
          ·
            refine ⟨33484292733817133199203987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89291447290179021864543965 33484292733817133199203987)
            ·
              refine ⟨50226439100725699798805981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33484292733817133199203987 50226439100725699798805981)
              ·
                refine ⟨18834914662772137424552243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50226439100725699798805981 18834914662772137424552243)
                ·
                  refine ⟨28252371994158206136828365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18834914662772137424552243 28252371994158206136828365)
                  ·
                    refine ⟨10594639497809327301310637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28252371994158206136828365 10594639497809327301310637)
                    ·
                      refine ⟨3972989811678497737991489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594639497809327301310637 3972989811678497737991489)
                      ·
                        rfl

theorem cell23_7737370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_7737370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737370 prefixEnd_7737370 := by exact prefixLift 7737370
  have htrace : WordTrace (prefixWord ++ tailWord_7737370) baseStart_7737370 baseEnd_7737370 := by
    simpa [prefixWord, tailWord_7737370, baseEnd_7737370] using wordTrace_append hprefix tailTrace_7737370
  have hstable : (prefixWord ++ tailWord_7737370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737370).length < 2 ^ (prefixWord ++ tailWord_7737370).sum := by decide
  have hdescent : baseEnd_7737370 < baseStart_7737370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737413 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_7737413 : Nat := 118140960795 + 7737413 * 2 ^ 59
def prefixEnd_7737413 : Nat := 4983230072969 + 3 ^ 40 * 7737413 * 2
def baseEnd_7737413 : Nat := 3973011891346641069753791

theorem tailTrace_7737413 : CollatzResearch.WordTrace tailWord_7737413 prefixEnd_7737413 3973011891346641069753791 := by
  unfold tailWord_7737413
  simp only [CollatzResearch.WordTrace]
  refine ⟨282206636317681620779904893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188137757545121080519936595 282206636317681620779904893)
  ·
    refine ⟨105827488619130607792464335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282206636317681620779904893 105827488619130607792464335)
    ·
      refine ⟨158741232928695911688696503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105827488619130607792464335 158741232928695911688696503)
      ·
        refine ⟨238111849393043867533044755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158741232928695911688696503 238111849393043867533044755)
        ·
          refine ⟨357167774089565801299567133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238111849393043867533044755 357167774089565801299567133)
          ·
            refine ⟨133937915283587175487337675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357167774089565801299567133 133937915283587175487337675)
            ·
              refine ⟨200906872925380763231006513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133937915283587175487337675 200906872925380763231006513)
              ·
                refine ⟨150680154694035572423254885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200906872925380763231006513 150680154694035572423254885)
                ·
                  refine ⟨28252529005131669829360291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150680154694035572423254885 28252529005131669829360291)
                  ·
                    refine ⟨42378793507697504744040437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28252529005131669829360291 42378793507697504744040437)
                    ·
                      refine ⟨3973011891346641069753791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42378793507697504744040437 3973011891346641069753791)
                      ·
                        rfl

theorem cell23_7737413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_7737413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737413 prefixEnd_7737413 := by exact prefixLift 7737413
  have htrace : WordTrace (prefixWord ++ tailWord_7737413) baseStart_7737413 baseEnd_7737413 := by
    simpa [prefixWord, tailWord_7737413, baseEnd_7737413] using wordTrace_append hprefix tailTrace_7737413
  have hstable : (prefixWord ++ tailWord_7737413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737413).length < 2 ^ (prefixWord ++ tailWord_7737413).sum := by decide
  have hdescent : baseEnd_7737413 < baseStart_7737413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737421 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_7737421 : Nat := 118140960795 + 7737421 * 2 ^ 59
def prefixEnd_7737421 : Nat := 4983230072969 + 3 ^ 40 * 7737421 * 2
def baseEnd_7737421 : Nat := 3973015999191877038453755

theorem tailTrace_7737421 : CollatzResearch.WordTrace tailWord_7737421 prefixEnd_7737421 3973015999191877038453755 := by
  unfold tailWord_7737421
  simp only [CollatzResearch.WordTrace]
  refine ⟨282206928101652638146196117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188137952067768425430797411 282206928101652638146196117)
  ·
    refine ⟨13228449754764967413102943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282206928101652638146196117 13228449754764967413102943)
    ·
      refine ⟨19842674632147451119654415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13228449754764967413102943 19842674632147451119654415)
      ·
        refine ⟨29764011948221176679481623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19842674632147451119654415 29764011948221176679481623)
        ·
          refine ⟨44646017922331765019222435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29764011948221176679481623 44646017922331765019222435)
          ·
            refine ⟨66969026883497647528833653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44646017922331765019222435 66969026883497647528833653)
            ·
              refine ⟨6278346270327904455828155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66969026883497647528833653 6278346270327904455828155)
              ·
                refine ⟨9417519405491856683742233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278346270327904455828155 9417519405491856683742233)
                ·
                  refine ⟨7063139554118892512806675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9417519405491856683742233 7063139554118892512806675)
                  ·
                    refine ⟨10594709331178338769210013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7063139554118892512806675 10594709331178338769210013)
                    ·
                      refine ⟨3973015999191877038453755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594709331178338769210013 3973015999191877038453755)
                      ·
                        rfl

theorem cell23_7737421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_7737421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737421 prefixEnd_7737421 := by exact prefixLift 7737421
  have htrace : WordTrace (prefixWord ++ tailWord_7737421) baseStart_7737421 baseEnd_7737421 := by
    simpa [prefixWord, tailWord_7737421, baseEnd_7737421] using wordTrace_append hprefix tailTrace_7737421
  have hstable : (prefixWord ++ tailWord_7737421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737421).length < 2 ^ (prefixWord ++ tailWord_7737421).sum := by decide
  have hdescent : baseEnd_7737421 < baseStart_7737421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737433 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 7]
def baseStart_7737433 : Nat := 118140960795 + 7737433 * 2 ^ 59
def prefixEnd_7737433 : Nat := 4983230072969 + 3 ^ 40 * 7737433 * 2
def baseEnd_7737433 : Nat := 441446906773303443500411

theorem tailTrace_7737433 : CollatzResearch.WordTrace tailWord_7737433 prefixEnd_7737433 441446906773303443500411 := by
  unfold tailWord_7737433
  simp only [CollatzResearch.WordTrace]
  refine ⟨282207365777609164195632953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188138243851739442797088635 282207365777609164195632953)
  ·
    refine ⟨211655524333206873146724715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282207365777609164195632953 211655524333206873146724715)
    ·
      refine ⟨317483286499810309720087073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211655524333206873146724715 317483286499810309720087073)
      ·
        refine ⟨238112464874857732290065305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317483286499810309720087073 238112464874857732290065305)
        ·
          refine ⟨178584348656143299217548979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238112464874857732290065305 178584348656143299217548979)
          ·
            refine ⟨267876522984214948826323469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178584348656143299217548979 267876522984214948826323469)
            ·
              refine ⟨100453696119080605809871301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267876522984214948826323469 100453696119080605809871301)
              ·
                refine ⟨18835068022327613589350869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100453696119080605809871301 18835068022327613589350869)
                ·
                  refine ⟨441446906773303443500411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18835068022327613589350869 441446906773303443500411)
                  ·
                    rfl

theorem cell23_7737433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 7].length) (baseStart_7737433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737433 prefixEnd_7737433 := by exact prefixLift 7737433
  have htrace : WordTrace (prefixWord ++ tailWord_7737433) baseStart_7737433 baseEnd_7737433 := by
    simpa [prefixWord, tailWord_7737433, baseEnd_7737433] using wordTrace_append hprefix tailTrace_7737433
  have hstable : (prefixWord ++ tailWord_7737433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737433).length < 2 ^ (prefixWord ++ tailWord_7737433).sum := by decide
  have hdescent : baseEnd_7737433 < baseStart_7737433 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737490 : List Nat := [3, 2, 3, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7737490 : Nat := 118140960795 + 7737490 * 2 ^ 59
def prefixEnd_7737490 : Nat := 4983230072969 + 3 ^ 40 * 7737490 * 2
def baseEnd_7737490 : Nat := 3973051429357037268490937

theorem tailTrace_7737490 : CollatzResearch.WordTrace tailWord_7737490 prefixEnd_7737490 3973051429357037268490937 := by
  unfold tailWord_7737490
  simp only [CollatzResearch.WordTrace]
  refine ⟨70552361184600665732614481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188139629825601775286971949 70552361184600665732614481)
  ·
    refine ⟨52914270888450499299460861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70552361184600665732614481 52914270888450499299460861)
    ·
      refine ⟨19842851583168937237297823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52914270888450499299460861 19842851583168937237297823)
      ·
        refine ⟨29764277374753405855946735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19842851583168937237297823 29764277374753405855946735)
        ·
          refine ⟨44646416062130108783920103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29764277374753405855946735 44646416062130108783920103)
          ·
            refine ⟨66969624093195163175880155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44646416062130108783920103 66969624093195163175880155)
            ·
              refine ⟨100454436139792744763820233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66969624093195163175880155 100454436139792744763820233)
              ·
                refine ⟨75340827104844558572865175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100454436139792744763820233 75340827104844558572865175)
                ·
                  refine ⟨113011240657266837859297763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75340827104844558572865175 113011240657266837859297763)
                  ·
                    refine ⟨169516860985900256788946645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113011240657266837859297763 169516860985900256788946645)
                    ·
                      refine ⟨3973051429357037268490937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169516860985900256788946645 3973051429357037268490937)
                      ·
                        rfl

theorem cell23_7737490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7737490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737490 prefixEnd_7737490 := by exact prefixLift 7737490
  have htrace : WordTrace (prefixWord ++ tailWord_7737490) baseStart_7737490 baseEnd_7737490 := by
    simpa [prefixWord, tailWord_7737490, baseEnd_7737490] using wordTrace_append hprefix tailTrace_7737490
  have hstable : (prefixWord ++ tailWord_7737490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737490).length < 2 ^ (prefixWord ++ tailWord_7737490).sum := by decide
  have hdescent : baseEnd_7737490 < baseStart_7737490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737554 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_7737554 : Nat := 118140960795 + 7737554 * 2 ^ 59
def prefixEnd_7737554 : Nat := 4983230072969 + 3 ^ 40 * 7737554 * 2
def baseEnd_7737554 : Nat := 3973084292118925018090643

theorem tailTrace_7737554 : CollatzResearch.WordTrace tailWord_7737554 prefixEnd_7737554 3973084292118925018090643 := by
  unfold tailWord_7737554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70552944752542700465196929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188141186006780534573858477 70552944752542700465196929)
  ·
    refine ⟨52914708564407025348897697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70552944752542700465196929 52914708564407025348897697)
    ·
      refine ⟨39686031423305269011673273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52914708564407025348897697 39686031423305269011673273)
      ·
        refine ⟨29764523567478951758754955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39686031423305269011673273 29764523567478951758754955)
        ·
          refine ⟨44646785351218427638132433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29764523567478951758754955 44646785351218427638132433)
          ·
            refine ⟨33485089013413820728599325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44646785351218427638132433 33485089013413820728599325)
            ·
              refine ⟨12556908380030182773224747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33485089013413820728599325 12556908380030182773224747)
              ·
                refine ⟨18835362570045274159837121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12556908380030182773224747 18835362570045274159837121)
                ·
                  refine ⟨14126521927533955619877841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18835362570045274159837121 14126521927533955619877841)
                  ·
                    refine ⟨10594891445650466714908381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14126521927533955619877841 10594891445650466714908381)
                    ·
                      refine ⟨3973084292118925018090643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594891445650466714908381 3973084292118925018090643)
                      ·
                        rfl

theorem cell23_7737554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_7737554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737554 prefixEnd_7737554 := by exact prefixLift 7737554
  have htrace : WordTrace (prefixWord ++ tailWord_7737554) baseStart_7737554 baseEnd_7737554 := by
    simpa [prefixWord, tailWord_7737554, baseEnd_7737554] using wordTrace_append hprefix tailTrace_7737554
  have hstable : (prefixWord ++ tailWord_7737554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737554).length < 2 ^ (prefixWord ++ tailWord_7737554).sum := by decide
  have hdescent : baseEnd_7737554 < baseStart_7737554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737567 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 3]
def baseStart_7737567 : Nat := 118140960795 + 7737567 * 2 ^ 59
def prefixEnd_7737567 : Nat := 4983230072969 + 3 ^ 40 * 7737567 * 2
def baseEnd_7737567 : Nat := 3973090967367433467228083

theorem tailTrace_7737567 : CollatzResearch.WordTrace tailWord_7737567 prefixEnd_7737567 3973090967367433467228083 := by
  unfold tailWord_7737567
  simp only [CollatzResearch.WordTrace]
  refine ⟨282212253159123705081010955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188141502106082470054007303 282212253159123705081010955)
  ·
    refine ⟨423318379738685557621516433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282212253159123705081010955 423318379738685557621516433)
    ·
      refine ⟨317488784804014168216137325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423318379738685557621516433 317488784804014168216137325)
      ·
        refine ⟨119058294301505313081051497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317488784804014168216137325 119058294301505313081051497)
        ·
          refine ⟨89293720726128984810788623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119058294301505313081051497 89293720726128984810788623)
          ·
            refine ⟨133940581089193477216182935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89293720726128984810788623 133940581089193477216182935)
            ·
              refine ⟨200910871633790215824274403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133940581089193477216182935 200910871633790215824274403)
              ·
                refine ⟨301366307450685323736411605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200910871633790215824274403 301366307450685323736411605)
                ·
                  refine ⟨7063272830875437275072147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 301366307450685323736411605 7063272830875437275072147)
                  ·
                    refine ⟨10594909246313155912608221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7063272830875437275072147 10594909246313155912608221)
                    ·
                      refine ⟨3973090967367433467228083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10594909246313155912608221 3973090967367433467228083)
                      ·
                        rfl

theorem cell23_7737567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_7737567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737567 prefixEnd_7737567 := by exact prefixLift 7737567
  have htrace : WordTrace (prefixWord ++ tailWord_7737567) baseStart_7737567 baseEnd_7737567 := by
    simpa [prefixWord, tailWord_7737567, baseEnd_7737567] using wordTrace_append hprefix tailTrace_7737567
  have hstable : (prefixWord ++ tailWord_7737567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737567).length < 2 ^ (prefixWord ++ tailWord_7737567).sum := by decide
  have hdescent : baseEnd_7737567 < baseStart_7737567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737617 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 4, 4]
def baseStart_7737617 : Nat := 118140960795 + 7737617 * 2 ^ 59
def prefixEnd_7737617 : Nat := 4983230072969 + 3 ^ 40 * 7737617 * 2
def baseEnd_7737617 : Nat := 1324372213800052757200951

theorem tailTrace_7737617 : CollatzResearch.WordTrace tailWord_7737617 prefixEnd_7737617 1324372213800052757200951 := by
  unfold tailWord_7737617
  simp only [CollatzResearch.WordTrace]
  refine ⟨282214076808942563620331105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188142717872628375746887403 282214076808942563620331105)
  ·
    refine ⟨211660557606706922715248329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282214076808942563620331105 211660557606706922715248329)
    ·
      refine ⟨158745418205030192036436247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211660557606706922715248329 158745418205030192036436247)
      ·
        refine ⟨238118127307545288054654371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158745418205030192036436247 238118127307545288054654371)
        ·
          refine ⟨357177190961317932081981557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238118127307545288054654371 357177190961317932081981557)
          ·
            refine ⟨33485361652623556132685771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357177190961317932081981557 33485361652623556132685771)
            ·
              refine ⟨50228042478935334199028657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33485361652623556132685771 50228042478935334199028657)
              ·
                refine ⟨37671031859201500649271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50228042478935334199028657 37671031859201500649271493)
                ·
                  refine ⟨7063318473600281371738405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37671031859201500649271493 7063318473600281371738405)
                  ·
                    refine ⟨1324372213800052757200951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7063318473600281371738405 1324372213800052757200951)
                    ·
                      rfl

theorem cell23_7737617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 4].length) (baseStart_7737617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737617 prefixEnd_7737617 := by exact prefixLift 7737617
  have htrace : WordTrace (prefixWord ++ tailWord_7737617) baseStart_7737617 baseEnd_7737617 := by
    simpa [prefixWord, tailWord_7737617, baseEnd_7737617] using wordTrace_append hprefix tailTrace_7737617
  have hstable : (prefixWord ++ tailWord_7737617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737617).length < 2 ^ (prefixWord ++ tailWord_7737617).sum := by decide
  have hdescent : baseEnd_7737617 < baseStart_7737617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737634 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_7737634 : Nat := 118140960795 + 7737634 * 2 ^ 59
def prefixEnd_7737634 : Nat := 4983230072969 + 3 ^ 40 * 7737634 * 2
def baseEnd_7737634 : Nat := 1324375123523761568363425

theorem tailTrace_7737634 : CollatzResearch.WordTrace tailWord_7737634 prefixEnd_7737634 1324375123523761568363425 := by
  unfold tailWord_7737634
  simp only [CollatzResearch.WordTrace]
  refine ⟨70553674212470243880924989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188143131233253983682466637 70553674212470243880924989)
  ·
    refine ⟨26457627829676341455346871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70553674212470243880924989 26457627829676341455346871)
    ·
      refine ⟨39686441744514512183020307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26457627829676341455346871 39686441744514512183020307)
      ·
        refine ⟨59529662616771768274530461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39686441744514512183020307 59529662616771768274530461)
        ·
          refine ⟨22323623481289413102948923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59529662616771768274530461 22323623481289413102948923)
          ·
            refine ⟨33485435221934119654423385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22323623481289413102948923 33485435221934119654423385)
            ·
              refine ⟨25114076416450589740817539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33485435221934119654423385 25114076416450589740817539)
              ·
                refine ⟨37671114624675884611226309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25114076416450589740817539 37671114624675884611226309)
                ·
                  refine ⟨7063333992126728364604933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37671114624675884611226309 7063333992126728364604933)
                  ·
                    refine ⟨1324375123523761568363425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7063333992126728364604933 1324375123523761568363425)
                    ·
                      rfl

theorem cell23_7737634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_7737634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737634 prefixEnd_7737634 := by exact prefixLift 7737634
  have htrace : WordTrace (prefixWord ++ tailWord_7737634) baseStart_7737634 baseEnd_7737634 := by
    simpa [prefixWord, tailWord_7737634, baseEnd_7737634] using wordTrace_append hprefix tailTrace_7737634
  have hstable : (prefixWord ++ tailWord_7737634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737634).length < 2 ^ (prefixWord ++ tailWord_7737634).sum := by decide
  have hdescent : baseEnd_7737634 < baseStart_7737634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737692 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7737692 : Nat := 118140960795 + 7737692 * 2 ^ 59
def prefixEnd_7737692 : Nat := 4983230072969 + 3 ^ 40 * 7737692 * 2
def baseEnd_7737692 : Nat := 3973155152449245478165009

theorem tailTrace_7737692 : CollatzResearch.WordTrace tailWord_7737692 prefixEnd_7737692 3973155152449245478165009 := by
  unfold tailWord_7737692
  simp only [CollatzResearch.WordTrace]
  refine ⟨141108406141835425714655665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188144541522447234286207553 141108406141835425714655665)
  ·
    refine ⟨105831304606376569285991749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141108406141835425714655665 105831304606376569285991749)
    ·
      refine ⟨19843369613695606741123453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105831304606376569285991749 19843369613695606741123453)
      ·
        refine ⟨7441263605135852527921295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19843369613695606741123453 7441263605135852527921295)
        ·
          refine ⟨11161895407703778791881943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441263605135852527921295 11161895407703778791881943)
          ·
            refine ⟨16742843111555668187822915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11161895407703778791881943 16742843111555668187822915)
            ·
              refine ⟨25114264667333502281734373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16742843111555668187822915 25114264667333502281734373)
              ·
                refine ⟨4708924625125031677825195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25114264667333502281734373 4708924625125031677825195)
                ·
                  refine ⟨7063386937687547516737793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4708924625125031677825195 7063386937687547516737793)
                  ·
                    refine ⟨5297540203265660637553345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063386937687547516737793 5297540203265660637553345)
                    ·
                      refine ⟨3973155152449245478165009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297540203265660637553345 3973155152449245478165009)
                      ·
                        rfl

theorem cell23_7737692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7737692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737692 prefixEnd_7737692 := by exact prefixLift 7737692
  have htrace : WordTrace (prefixWord ++ tailWord_7737692) baseStart_7737692 baseEnd_7737692 := by
    simpa [prefixWord, tailWord_7737692, baseEnd_7737692] using wordTrace_append hprefix tailTrace_7737692
  have hstable : (prefixWord ++ tailWord_7737692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737692).length < 2 ^ (prefixWord ++ tailWord_7737692).sum := by decide
  have hdescent : baseEnd_7737692 < baseStart_7737692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737754 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_7737754 : Nat := 118140960795 + 7737754 * 2 ^ 59
def prefixEnd_7737754 : Nat := 4983230072969 + 3 ^ 40 * 7737754 * 2
def baseEnd_7737754 : Nat := 441465220916647137287747

theorem tailTrace_7737754 : CollatzResearch.WordTrace tailWord_7737754 prefixEnd_7737754 441465220916647137287747 := by
  unfold tailWord_7737754
  simp only [CollatzResearch.WordTrace]
  refine ⟨70554768402361559004517079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188146049072964157345378877 70554768402361559004517079)
  ·
    refine ⟨105832152603542338506775619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70554768402361559004517079 105832152603542338506775619)
    ·
      refine ⟨158748228905313507760163429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105832152603542338506775619 158748228905313507760163429)
      ·
        refine ⟨29765292919746282705030643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158748228905313507760163429 29765292919746282705030643)
        ·
          refine ⟨44647939379619424057545965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29765292919746282705030643 44647939379619424057545965)
          ·
            refine ⟨16742977267357284021579737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44647939379619424057545965 16742977267357284021579737)
            ·
              refine ⟨12557232950517963016184803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16742977267357284021579737 12557232950517963016184803)
              ·
                refine ⟨18835849425776944524277205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12557232950517963016184803 18835849425776944524277205)
                ·
                  refine ⟨441465220916647137287747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18835849425776944524277205 441465220916647137287747)
                  ·
                    rfl

theorem cell23_7737754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_7737754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737754 prefixEnd_7737754 := by exact prefixLift 7737754
  have htrace : WordTrace (prefixWord ++ tailWord_7737754) baseStart_7737754 baseEnd_7737754 := by
    simpa [prefixWord, tailWord_7737754, baseEnd_7737754] using wordTrace_append hprefix tailTrace_7737754
  have hstable : (prefixWord ++ tailWord_7737754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737754).length < 2 ^ (prefixWord ++ tailWord_7737754).sum := by decide
  have hdescent : baseEnd_7737754 < baseStart_7737754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737764 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_7737764 : Nat := 118140960795 + 7737764 * 2 ^ 59
def prefixEnd_7737764 : Nat := 4983230072969 + 3 ^ 40 * 7737764 * 2
def baseEnd_7737764 : Nat := 3973192123056369196464677

theorem tailTrace_7737764 : CollatzResearch.WordTrace tailWord_7737764 prefixEnd_7737764 3973192123056369196464677 := by
  unfold tailWord_7737764
  simp only [CollatzResearch.WordTrace]
  refine ⟨141109719169705003862966173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188146292226273338483954897 141109719169705003862966173)
  ·
    refine ⟨52916144688639376448612315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141109719169705003862966173 52916144688639376448612315)
    ·
      refine ⟨79374217032959064672918473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52916144688639376448612315 79374217032959064672918473)
      ·
        refine ⟨59530662774719298504688855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79374217032959064672918473 59530662774719298504688855)
        ·
          refine ⟨89295994162078947757033283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59530662774719298504688855 89295994162078947757033283)
          ·
            refine ⟨133943991243118421635549925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89295994162078947757033283 133943991243118421635549925)
            ·
              refine ⟨25114498358084704056665611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133943991243118421635549925 25114498358084704056665611)
              ·
                refine ⟨37671747537127056084998417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25114498358084704056665611 37671747537127056084998417)
                ·
                  refine ⟨28253810652845292063748813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37671747537127056084998417 28253810652845292063748813)
                  ·
                    refine ⟨10595178994816984523905805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28253810652845292063748813 10595178994816984523905805)
                    ·
                      refine ⟨3973192123056369196464677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10595178994816984523905805 3973192123056369196464677)
                      ·
                        rfl

theorem cell23_7737764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_7737764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737764 prefixEnd_7737764 := by exact prefixLift 7737764
  have htrace : WordTrace (prefixWord ++ tailWord_7737764) baseStart_7737764 baseEnd_7737764 := by
    simpa [prefixWord, tailWord_7737764, baseEnd_7737764] using wordTrace_append hprefix tailTrace_7737764
  have hstable : (prefixWord ++ tailWord_7737764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737764).length < 2 ^ (prefixWord ++ tailWord_7737764).sum := by decide
  have hdescent : baseEnd_7737764 < baseStart_7737764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737788 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 5]
def baseStart_7737788 : Nat := 118140960795 + 7737788 * 2 ^ 59
def prefixEnd_7737788 : Nat := 4983230072969 + 3 ^ 40 * 7737788 * 2
def baseEnd_7737788 : Nat := 441467160732453011396063

theorem tailTrace_7737788 : CollatzResearch.WordTrace tailWord_7737788 prefixEnd_7737788 441467160732453011396063 := by
  unfold tailWord_7737788
  simp only [CollatzResearch.WordTrace]
  refine ⟨141110156845661529912403009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188146875794215373216537345 141110156845661529912403009)
  ·
    refine ⟨105832617634246147434302257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141110156845661529912403009 105832617634246147434302257)
    ·
      refine ⟨79374463225684610575726693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105832617634246147434302257 79374463225684610575726693)
      ·
        refine ⟨14882711854815864482948755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79374463225684610575726693 14882711854815864482948755)
        ·
          refine ⟨22324067782223796724423133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14882711854815864482948755 22324067782223796724423133)
          ·
            refine ⟨8371525418333923771658675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22324067782223796724423133 8371525418333923771658675)
            ·
              refine ⟨12557288127500885657488013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371525418333923771658675 12557288127500885657488013)
              ·
                refine ⟨4708983047812832121558005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12557288127500885657488013 4708983047812832121558005)
                ·
                  refine ⟨441467160732453011396063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4708983047812832121558005 441467160732453011396063)
                  ·
                    rfl

theorem cell23_7737788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_7737788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737788 prefixEnd_7737788 := by exact prefixLift 7737788
  have htrace : WordTrace (prefixWord ++ tailWord_7737788) baseStart_7737788 baseEnd_7737788 := by
    simpa [prefixWord, tailWord_7737788, baseEnd_7737788] using wordTrace_append hprefix tailTrace_7737788
  have hstable : (prefixWord ++ tailWord_7737788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737788).length < 2 ^ (prefixWord ++ tailWord_7737788).sum := by decide
  have hdescent : baseEnd_7737788 < baseStart_7737788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737821 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_7737821 : Nat := 118140960795 + 7737821 * 2 ^ 59
def prefixEnd_7737821 : Nat := 4983230072969 + 3 ^ 40 * 7737821 * 2
def baseEnd_7737821 : Nat := 3973221391453675473451915

theorem tailTrace_7737821 : CollatzResearch.WordTrace tailWord_7737821 prefixEnd_7737821 3973221391453675473451915 := by
  unfold tailWord_7737821
  simp only [CollatzResearch.WordTrace]
  refine ⟨282221517300203506460757317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188147678200135670973838211 282221517300203506460757317)
  ·
    refine ⟨52916534493788157461391997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282221517300203506460757317 52916534493788157461391997)
    ·
      refine ⟨19843700435170559048021999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52916534493788157461391997 19843700435170559048021999)
      ·
        refine ⟨29765550652755838572032999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19843700435170559048021999 29765550652755838572032999)
        ·
          refine ⟨44648325979133757858049499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29765550652755838572032999 44648325979133757858049499)
          ·
            refine ⟨66972488968700636787074249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44648325979133757858049499 66972488968700636787074249)
            ·
              refine ⟨50229366726525477590305687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66972488968700636787074249 50229366726525477590305687)
              ·
                refine ⟨75344050089788216385458531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50229366726525477590305687 75344050089788216385458531)
                ·
                  refine ⟨113016075134682324578187797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75344050089788216385458531 113016075134682324578187797)
                  ·
                    refine ⟨5297628521938233964602553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113016075134682324578187797 5297628521938233964602553)
                    ·
                      refine ⟨3973221391453675473451915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297628521938233964602553 3973221391453675473451915)
                      ·
                        rfl

theorem cell23_7737821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_7737821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737821 prefixEnd_7737821 := by exact prefixLift 7737821
  have htrace : WordTrace (prefixWord ++ tailWord_7737821) baseStart_7737821 baseEnd_7737821 := by
    simpa [prefixWord, tailWord_7737821, baseEnd_7737821] using wordTrace_append hprefix tailTrace_7737821
  have hstable : (prefixWord ++ tailWord_7737821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737821).length < 2 ^ (prefixWord ++ tailWord_7737821).sum := by decide
  have hdescent : baseEnd_7737821 < baseStart_7737821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737824 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_7737824 : Nat := 118140960795 + 7737824 * 2 ^ 59
def prefixEnd_7737824 : Nat := 4983230072969 + 3 ^ 40 * 7737824 * 2
def baseEnd_7737824 : Nat := 3973222931895638961714401

theorem tailTrace_7737824 : CollatzResearch.WordTrace tailWord_7737824 prefixEnd_7737824 3973222931895638961714401 := by
  unfold tailWord_7737824
  simp only [CollatzResearch.WordTrace]
  refine ⟨141110813359596318986558263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188147751146128425315411017 141110813359596318986558263)
  ·
    refine ⟨211666220039394478479837395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141110813359596318986558263 211666220039394478479837395)
    ·
      refine ⟨317499330059091717719756093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211666220039394478479837395 317499330059091717719756093)
      ·
        refine ⟨119062248772159394144908535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317499330059091717719756093 119062248772159394144908535)
        ·
          refine ⟨178593373158239091217362803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119062248772159394144908535 178593373158239091217362803)
          ·
            refine ⟨267890059737358636826044205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178593373158239091217362803 267890059737358636826044205)
            ·
              refine ⟨100458772401509488809766577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267890059737358636826044205 100458772401509488809766577)
              ·
                refine ⟨75344079301132116607324933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100458772401509488809766577 75344079301132116607324933)
                ·
                  refine ⟨14127014868962271863873425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75344079301132116607324933 14127014868962271863873425)
                  ·
                    refine ⟨10595261151721703897905069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14127014868962271863873425 10595261151721703897905069)
                    ·
                      refine ⟨3973222931895638961714401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10595261151721703897905069 3973222931895638961714401)
                      ·
                        rfl

theorem cell23_7737824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_7737824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737824 prefixEnd_7737824 := by exact prefixLift 7737824
  have htrace : WordTrace (prefixWord ++ tailWord_7737824) baseStart_7737824 baseEnd_7737824 := by
    simpa [prefixWord, tailWord_7737824, baseEnd_7737824] using wordTrace_append hprefix tailTrace_7737824
  have hstable : (prefixWord ++ tailWord_7737824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737824).length < 2 ^ (prefixWord ++ tailWord_7737824).sum := by decide
  have hdescent : baseEnd_7737824 < baseStart_7737824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737841 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 3]
def baseStart_7737841 : Nat := 118140960795 + 7737841 * 2 ^ 59
def prefixEnd_7737841 : Nat := 4983230072969 + 3 ^ 40 * 7737841 * 2
def baseEnd_7737841 : Nat := 3973231661066765395201823

theorem tailTrace_7737841 : CollatzResearch.WordTrace tailWord_7737841 prefixEnd_7737841 3973231661066765395201823 := by
  unfold tailWord_7737841
  simp only [CollatzResearch.WordTrace]
  refine ⟨282222246760131049876485377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188148164506754033250990251 282222246760131049876485377)
  ·
    refine ⟨211666685070098287407364033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282222246760131049876485377 211666685070098287407364033)
    ·
      refine ⟨158750013802573715555523025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211666685070098287407364033 158750013802573715555523025)
      ·
        refine ⟨119062510351930286666642269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158750013802573715555523025 119062510351930286666642269)
        ·
          refine ⟨44648441381973857499990851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119062510351930286666642269 44648441381973857499990851)
          ·
            refine ⟨66972662072960786249986277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44648441381973857499990851 66972662072960786249986277)
            ·
              refine ⟨12557374138680147421872427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66972662072960786249986277 12557374138680147421872427)
              ·
                refine ⟨18836061208020221132808641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12557374138680147421872427 18836061208020221132808641)
                ·
                  refine ⟨14127045906015165849606481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18836061208020221132808641 14127045906015165849606481)
                  ·
                    refine ⟨10595284429511374387204861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14127045906015165849606481 10595284429511374387204861)
                    ·
                      refine ⟨3973231661066765395201823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10595284429511374387204861 3973231661066765395201823)
                      ·
                        rfl

theorem cell23_7737841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_7737841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737841 prefixEnd_7737841 := by exact prefixLift 7737841
  have htrace : WordTrace (prefixWord ++ tailWord_7737841) baseStart_7737841 baseEnd_7737841 := by
    simpa [prefixWord, tailWord_7737841, baseEnd_7737841] using wordTrace_append hprefix tailTrace_7737841
  have hstable : (prefixWord ++ tailWord_7737841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737841).length < 2 ^ (prefixWord ++ tailWord_7737841).sum := by decide
  have hdescent : baseEnd_7737841 < baseStart_7737841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737892 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7737892 : Nat := 118140960795 + 7737892 * 2 ^ 59
def prefixEnd_7737892 : Nat := 4983230072969 + 3 ^ 40 * 7737892 * 2
def baseEnd_7737892 : Nat := 3973257848580144695664089

theorem tailTrace_7737892 : CollatzResearch.WordTrace tailWord_7737892 prefixEnd_7737892 3973257848580144695664089 := by
  unfold tailWord_7737892
  simp only [CollatzResearch.WordTrace]
  refine ⟨141112053441473142793295965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188149404588630857057727953 141112053441473142793295965)
  ·
    refine ⟨52917020040552428547485987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141112053441473142793295965 52917020040552428547485987)
    ·
      refine ⟨79375530060828642821228981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52917020040552428547485987 79375530060828642821228981)
      ·
        refine ⟨7441455943202685264490217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79375530060828642821228981 7441455943202685264490217)
        ·
          refine ⟨5581091957402013948367663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441455943202685264490217 5581091957402013948367663)
          ·
            refine ⟨8371637936103020922551495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581091957402013948367663 8371637936103020922551495)
            ·
              refine ⟨12557456904154531383827243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8371637936103020922551495 12557456904154531383827243)
              ·
                refine ⟨18836185356231797075740865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12557456904154531383827243 18836185356231797075740865)
                ·
                  refine ⟨14127139017173847806805649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18836185356231797075740865 14127139017173847806805649)
                  ·
                    refine ⟨10595354262880385855104237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14127139017173847806805649 10595354262880385855104237)
                    ·
                      refine ⟨3973257848580144695664089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10595354262880385855104237 3973257848580144695664089)
                      ·
                        rfl

theorem cell23_7737892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7737892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737892 prefixEnd_7737892 := by exact prefixLift 7737892
  have htrace : WordTrace (prefixWord ++ tailWord_7737892) baseStart_7737892 baseEnd_7737892 := by
    simpa [prefixWord, tailWord_7737892, baseEnd_7737892] using wordTrace_append hprefix tailTrace_7737892
  have hstable : (prefixWord ++ tailWord_7737892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737892).length < 2 ^ (prefixWord ++ tailWord_7737892).sum := by decide
  have hdescent : baseEnd_7737892 < baseStart_7737892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737898 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_7737898 : Nat := 118140960795 + 7737898 * 2 ^ 59
def prefixEnd_7737898 : Nat := 4983230072969 + 3 ^ 40 * 7737898 * 2
def baseEnd_7737898 : Nat := 3973260929464071672189061

theorem tailTrace_7737898 : CollatzResearch.WordTrace tailWord_7737898 prefixEnd_7737898 3973260929464071672189061 := by
  unfold tailWord_7737898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70556081430231137152827587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188149550480616365740873565 70556081430231137152827587)
  ·
    refine ⟨105834122145346705729241381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70556081430231137152827587 105834122145346705729241381)
    ·
      refine ⟨19843897902252507324232759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105834122145346705729241381 19843897902252507324232759)
      ·
        refine ⟨29765846853378760986349139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19843897902252507324232759 29765846853378760986349139)
        ·
          refine ⟨44648770280068141479523709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29765846853378760986349139 44648770280068141479523709)
          ·
            refine ⟨16743288855025553054821391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44648770280068141479523709 16743288855025553054821391)
            ·
              refine ⟨25114933282538329582232087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16743288855025553054821391 25114933282538329582232087)
              ·
                refine ⟨37672399923807494373348131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25114933282538329582232087 37672399923807494373348131)
                ·
                  refine ⟨56508599885711241560022197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37672399923807494373348131 56508599885711241560022197)
                  ·
                    refine ⟨5297681239285428896252081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56508599885711241560022197 5297681239285428896252081)
                    ·
                      refine ⟨3973260929464071672189061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297681239285428896252081 3973260929464071672189061)
                      ·
                        rfl

theorem cell23_7737898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_7737898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737898 prefixEnd_7737898 := by exact prefixLift 7737898
  have htrace : WordTrace (prefixWord ++ tailWord_7737898) baseStart_7737898 baseEnd_7737898 := by
    simpa [prefixWord, tailWord_7737898, baseEnd_7737898] using wordTrace_append hprefix tailTrace_7737898
  have hstable : (prefixWord ++ tailWord_7737898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737898).length < 2 ^ (prefixWord ++ tailWord_7737898).sum := by decide
  have hdescent : baseEnd_7737898 < baseStart_7737898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737904 : List Nat := [2, 1, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_7737904 : Nat := 118140960795 + 7737904 * 2 ^ 59
def prefixEnd_7737904 : Nat := 4983230072969 + 3 ^ 40 * 7737904 * 2
def baseEnd_7737904 : Nat := 1324421336782666216238011

theorem tailTrace_7737904 : CollatzResearch.WordTrace tailWord_7737904 prefixEnd_7737904 1324421336782666216238011 := by
  unfold tailWord_7737904
  simp only [CollatzResearch.WordTrace]
  refine ⟨141112272279451405818014383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188149696372601874424019177 141112272279451405818014383)
  ·
    refine ⟨211668408419177108727021575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141112272279451405818014383 211668408419177108727021575)
    ·
      refine ⟨317502612628765663090532363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211668408419177108727021575 317502612628765663090532363)
      ·
        refine ⟨476253918943148494635798545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317502612628765663090532363 476253918943148494635798545)
        ·
          refine ⟨357190439207361370976848909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476253918943148494635798545 357190439207361370976848909)
          ·
            refine ⟨133946414702760514116318341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357190439207361370976848909 133946414702760514116318341)
            ·
              refine ⟨25114952756767596396809689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133946414702760514116318341 25114952756767596396809689)
              ·
                refine ⟨18836214567575697297607267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25114952756767596396809689 18836214567575697297607267)
                ·
                  refine ⟨28254321851363545946410901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18836214567575697297607267 28254321851363545946410901)
                  ·
                    refine ⟨1324421336782666216238011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28254321851363545946410901 1324421336782666216238011)
                    ·
                      rfl

theorem cell23_7737904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_7737904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737904 prefixEnd_7737904 := by exact prefixLift 7737904
  have htrace : WordTrace (prefixWord ++ tailWord_7737904) baseStart_7737904 baseEnd_7737904 := by
    simpa [prefixWord, tailWord_7737904, baseEnd_7737904] using wordTrace_append hprefix tailTrace_7737904
  have hstable : (prefixWord ++ tailWord_7737904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737904).length < 2 ^ (prefixWord ++ tailWord_7737904).sum := by decide
  have hdescent : baseEnd_7737904 < baseStart_7737904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737911 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_7737911 : Nat := 118140960795 + 7737911 * 2 ^ 59
def prefixEnd_7737911 : Nat := 4983230072969 + 3 ^ 40 * 7737911 * 2
def baseEnd_7737911 : Nat := 3973267604712580121326501

theorem tailTrace_7737911 : CollatzResearch.WordTrace tailWord_7737911 prefixEnd_7737911 3973267604712580121326501 := by
  unfold tailWord_7737911
  simp only [CollatzResearch.WordTrace]
  refine ⟨282224799869877451831533587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188149866579918301221022391 282224799869877451831533587)
  ·
    refine ⟨423337199804816177747300381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282224799869877451831533587 423337199804816177747300381)
    ·
      refine ⟨158751449926806066655237643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423337199804816177747300381 158751449926806066655237643)
      ·
        refine ⟨238127174890209099982856465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158751449926806066655237643 238127174890209099982856465)
        ·
          refine ⟨178595381167656824987142349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238127174890209099982856465 178595381167656824987142349)
          ·
            refine ⟨66973267937871309370178381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178595381167656824987142349 66973267937871309370178381)
            ·
              refine ⟨25114975476701741013816893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66973267937871309370178381 25114975476701741013816893)
              ·
                refine ⟨9418115803763152880181335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25114975476701741013816893 9418115803763152880181335)
                ·
                  refine ⟨14127173705644729320272003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418115803763152880181335 14127173705644729320272003)
                  ·
                    refine ⟨21190760558467093980408005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14127173705644729320272003 21190760558467093980408005)
                    ·
                      refine ⟨3973267604712580121326501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21190760558467093980408005 3973267604712580121326501)
                      ·
                        rfl

theorem cell23_7737911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_7737911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737911 prefixEnd_7737911 := by exact prefixLift 7737911
  have htrace : WordTrace (prefixWord ++ tailWord_7737911) baseStart_7737911 baseEnd_7737911 := by
    simpa [prefixWord, tailWord_7737911, baseEnd_7737911] using wordTrace_append hprefix tailTrace_7737911
  have hstable : (prefixWord ++ tailWord_7737911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737911).length < 2 ^ (prefixWord ++ tailWord_7737911).sum := by decide
  have hdescent : baseEnd_7737911 < baseStart_7737911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7737941 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_7737941 : Nat := 118140960795 + 7737941 * 2 ^ 59
def prefixEnd_7737941 : Nat := 4983230072969 + 3 ^ 40 * 7737941 * 2
def baseEnd_7737941 : Nat := 3973283009132215003951363

theorem tailTrace_7737941 : CollatzResearch.WordTrace tailWord_7737941 prefixEnd_7737941 3973283009132215003951363 := by
  unfold tailWord_7737941
  simp only [CollatzResearch.WordTrace]
  refine ⟨282225894059768766955125677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188150596039845844636750451 282225894059768766955125677)
  ·
    refine ⟨105834710272413287608172129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282225894059768766955125677 105834710272413287608172129)
    ·
      refine ⟨79376032704309965706129097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105834710272413287608172129 79376032704309965706129097)
      ·
        refine ⟨59532024528232474279596823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79376032704309965706129097 59532024528232474279596823)
        ·
          refine ⟨89298036792348711419395235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59532024528232474279596823 89298036792348711419395235)
          ·
            refine ⟨133947055188523067129092853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89298036792348711419395235 133947055188523067129092853)
            ·
              refine ⟨12557536423924037543352455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133947055188523067129092853 12557536423924037543352455)
              ·
                refine ⟨18836304635886056315028683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12557536423924037543352455 18836304635886056315028683)
                ·
                  refine ⟨28254456953829084472543025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18836304635886056315028683 28254456953829084472543025)
                  ·
                    refine ⟨21190842715371813354407269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28254456953829084472543025 21190842715371813354407269)
                    ·
                      refine ⟨3973283009132215003951363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21190842715371813354407269 3973283009132215003951363)
                      ·
                        rfl

theorem cell23_7737941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_7737941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7737941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7737941 prefixEnd_7737941 := by exact prefixLift 7737941
  have htrace : WordTrace (prefixWord ++ tailWord_7737941) baseStart_7737941 baseEnd_7737941 := by
    simpa [prefixWord, tailWord_7737941, baseEnd_7737941] using wordTrace_append hprefix tailTrace_7737941
  have hstable : (prefixWord ++ tailWord_7737941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7737941).length < 2 ^ (prefixWord ++ tailWord_7737941).sum := by decide
  have hdescent : baseEnd_7737941 < baseStart_7737941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7737941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738035 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 2, 2, 2]
def baseStart_7738035 : Nat := 118140960795 + 7738035 * 2 ^ 59
def prefixEnd_7738035 : Nat := 4983230072969 + 3 ^ 40 * 7738035 * 2
def baseEnd_7738035 : Nat := 3973331276313737636175931

theorem tailTrace_7738035 : CollatzResearch.WordTrace tailWord_7738035 prefixEnd_7738035 3973331276313737636175931 := by
  unfold tailWord_7738035
  simp only [CollatzResearch.WordTrace]
  refine ⟨282229322521428221009047559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188152881680952147339365039 282229322521428221009047559)
  ·
    refine ⟨423343983782142331513571339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282229322521428221009047559 423343983782142331513571339)
    ·
      refine ⟨635015975673213497270357009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423343983782142331513571339 635015975673213497270357009)
      ·
        refine ⟨476261981754910122952767757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635015975673213497270357009 476261981754910122952767757)
        ·
          refine ⟨178598243158091296107287909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476261981754910122952767757 178598243158091296107287909)
          ·
            refine ⟨33487170592142118020116483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178598243158091296107287909 33487170592142118020116483)
            ·
              refine ⟨50230755888213177030174725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33487170592142118020116483 50230755888213177030174725)
              ·
                refine ⟨9418266729039970693157761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50230755888213177030174725 9418266729039970693157761)
                ·
                  refine ⟨7063700046779978019868321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418266729039970693157761 7063700046779978019868321)
                  ·
                    refine ⟨5297775035084983514901241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063700046779978019868321 5297775035084983514901241)
                    ·
                      refine ⟨3973331276313737636175931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297775035084983514901241 3973331276313737636175931)
                      ·
                        rfl

theorem cell23_7738035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 2, 2].length) (baseStart_7738035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738035 prefixEnd_7738035 := by exact prefixLift 7738035
  have htrace : WordTrace (prefixWord ++ tailWord_7738035) baseStart_7738035 baseEnd_7738035 := by
    simpa [prefixWord, tailWord_7738035, baseEnd_7738035] using wordTrace_append hprefix tailTrace_7738035
  have hstable : (prefixWord ++ tailWord_7738035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738035).length < 2 ^ (prefixWord ++ tailWord_7738035).sum := by decide
  have hdescent : baseEnd_7738035 < baseStart_7738035 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738052 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_7738052 : Nat := 118140960795 + 7738052 * 2 ^ 59
def prefixEnd_7738052 : Nat := 4983230072969 + 3 ^ 40 * 7738052 * 2
def baseEnd_7738052 : Nat := 3973340005484864069663353

theorem tailTrace_7738052 : CollatzResearch.WordTrace tailWord_7738052 prefixEnd_7738052 3973340005484864069663353 := by
  unfold tailWord_7738052
  simp only [CollatzResearch.WordTrace]
  refine ⟨141114971281183316456208205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188153295041577755274944273 141114971281183316456208205)
  ·
    refine ⟨52918114230443743671078077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141114971281183316456208205 52918114230443743671078077)
    ·
      refine ⟨19844292836416403876654279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52918114230443743671078077 19844292836416403876654279)
      ·
        refine ⟨29766439254624605814981419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19844292836416403876654279 29766439254624605814981419)
        ·
          refine ⟨44649658881936908722472129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29766439254624605814981419 44649658881936908722472129)
          ·
            refine ⟨33487244161452681541854097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44649658881936908722472129 33487244161452681541854097)
            ·
              refine ⟨25115433121089511156390573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33487244161452681541854097 25115433121089511156390573)
              ·
                refine ⟨9418287420408566683646465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25115433121089511156390573 9418287420408566683646465)
                ·
                  refine ⟨7063715565306425012734849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418287420408566683646465 7063715565306425012734849)
                  ·
                    refine ⟨5297786673979818759551137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063715565306425012734849 5297786673979818759551137)
                    ·
                      refine ⟨3973340005484864069663353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297786673979818759551137 3973340005484864069663353)
                      ·
                        rfl

theorem cell23_7738052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_7738052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738052 prefixEnd_7738052 := by exact prefixLift 7738052
  have htrace : WordTrace (prefixWord ++ tailWord_7738052) baseStart_7738052 baseEnd_7738052 := by
    simpa [prefixWord, tailWord_7738052, baseEnd_7738052] using wordTrace_append hprefix tailTrace_7738052
  have hstable : (prefixWord ++ tailWord_7738052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738052).length < 2 ^ (prefixWord ++ tailWord_7738052).sum := by decide
  have hdescent : baseEnd_7738052 < baseStart_7738052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738071 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 7]
def baseStart_7738071 : Nat := 118140960795 + 7738071 * 2 ^ 59
def prefixEnd_7738071 : Nat := 4983230072969 + 3 ^ 40 * 7738071 * 2
def baseEnd_7738071 : Nat := 1324449920539099831775255

theorem tailTrace_7738071 : CollatzResearch.WordTrace tailWord_7738071 prefixEnd_7738071 1324449920539099831775255 := by
  unfold tailWord_7738071
  simp only [CollatzResearch.WordTrace]
  refine ⟨282230635549297799157358067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188153757032865199438238711 282230635549297799157358067)
  ·
    refine ⟨423345953323946698736037101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282230635549297799157358067 423345953323946698736037101)
    ·
      refine ⟨158754732496480012026013913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423345953323946698736037101 158754732496480012026013913)
      ·
        refine ⟨119066049372360009019510435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158754732496480012026013913 119066049372360009019510435)
        ·
          refine ⟨178599074058540013529265653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119066049372360009019510435 178599074058540013529265653)
          ·
            refine ⟨16743663192988126268368655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 178599074058540013529265653 16743663192988126268368655)
            ·
              refine ⟨25115494789482189402552983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16743663192988126268368655 25115494789482189402552983)
              ·
                refine ⟨37673242184223284103829475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25115494789482189402552983 37673242184223284103829475)
                ·
                  refine ⟨56509863276334926155744213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37673242184223284103829475 56509863276334926155744213)
                  ·
                    refine ⟨1324449920539099831775255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56509863276334926155744213 1324449920539099831775255)
                    ·
                      rfl

theorem cell23_7738071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_7738071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738071 prefixEnd_7738071 := by exact prefixLift 7738071
  have htrace : WordTrace (prefixWord ++ tailWord_7738071) baseStart_7738071 baseEnd_7738071 := by
    simpa [prefixWord, tailWord_7738071, baseEnd_7738071] using wordTrace_append hprefix tailTrace_7738071
  have hstable : (prefixWord ++ tailWord_7738071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738071).length < 2 ^ (prefixWord ++ tailWord_7738071).sum := by decide
  have hdescent : baseEnd_7738071 < baseStart_7738071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738091 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4]
def baseStart_7738091 : Nat := 118140960795 + 7738091 * 2 ^ 59
def prefixEnd_7738091 : Nat := 4983230072969 + 3 ^ 40 * 7738091 * 2
def baseEnd_7738091 : Nat := 3973360031230389417075673

theorem tailTrace_7738091 : CollatzResearch.WordTrace tailWord_7738091 prefixEnd_7738091 3973360031230389417075673 := by
  unfold tailWord_7738091
  simp only [CollatzResearch.WordTrace]
  refine ⟨282231365009225342573086127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188154243339483561715390751 282231365009225342573086127)
  ·
    refine ⟨423347047513838013859629191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282231365009225342573086127 423347047513838013859629191)
    ·
      refine ⟨635020571270757020789443787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423347047513838013859629191 635020571270757020789443787)
      ·
        refine ⟨952530856906135531184165681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635020571270757020789443787 952530856906135531184165681)
        ·
          refine ⟨714398142679601648388124261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952530856906135531184165681 714398142679601648388124261)
          ·
            refine ⟨133949651752425309072773299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 714398142679601648388124261 133949651752425309072773299)
            ·
              refine ⟨200924477628637963609159949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133949651752425309072773299 200924477628637963609159949)
              ·
                refine ⟨75346679110739236353434981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200924477628637963609159949 75346679110739236353434981)
                ·
                  refine ⟨14127502333263606816269059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75346679110739236353434981 14127502333263606816269059)
                  ·
                    refine ⟨21191253499895410224403589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14127502333263606816269059 21191253499895410224403589)
                    ·
                      refine ⟨3973360031230389417075673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21191253499895410224403589 3973360031230389417075673)
                      ·
                        rfl

theorem cell23_7738091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4].length) (baseStart_7738091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738091 prefixEnd_7738091 := by exact prefixLift 7738091
  have htrace : WordTrace (prefixWord ++ tailWord_7738091) baseStart_7738091 baseEnd_7738091 := by
    simpa [prefixWord, tailWord_7738091, baseEnd_7738091] using wordTrace_append hprefix tailTrace_7738091
  have hstable : (prefixWord ++ tailWord_7738091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738091).length < 2 ^ (prefixWord ++ tailWord_7738091).sum := by decide
  have hdescent : baseEnd_7738091 < baseStart_7738091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738165 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 6]
def baseStart_7738165 : Nat := 118140960795 + 7738165 * 2 ^ 59
def prefixEnd_7738165 : Nat := 4983230072969 + 3 ^ 40 * 7738165 * 2
def baseEnd_7738165 : Nat := 441488669866535791950037

theorem tailTrace_7738165 : CollatzResearch.WordTrace tailWord_7738165 prefixEnd_7738165 441488669866535791950037 := by
  unfold tailWord_7738165
  simp only [CollatzResearch.WordTrace]
  refine ⟨282234064010957253211279949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188156042673971502140853299 282234064010957253211279949)
  ·
    refine ⟨105837774004108969954229981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282234064010957253211279949 105837774004108969954229981)
    ·
      refine ⟨39689165251540863732836243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105837774004108969954229981 39689165251540863732836243)
      ·
        refine ⟨59533747877311295599254365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39689165251540863732836243 59533747877311295599254365)
        ·
          refine ⟨22325155453991735849720387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59533747877311295599254365 22325155453991735849720387)
          ·
            refine ⟨33487733180987603774580581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22325155453991735849720387 33487733180987603774580581)
            ·
              refine ⟨6278949971435175707733859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33487733180987603774580581 6278949971435175707733859)
              ·
                refine ⟨9418424957152763561600789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6278949971435175707733859 9418424957152763561600789)
                ·
                  refine ⟨441488669866535791950037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9418424957152763561600789 441488669866535791950037)
                  ·
                    rfl

theorem cell23_7738165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_7738165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738165 prefixEnd_7738165 := by exact prefixLift 7738165
  have htrace : WordTrace (prefixWord ++ tailWord_7738165) baseStart_7738165 baseEnd_7738165 := by
    simpa [prefixWord, tailWord_7738165, baseEnd_7738165] using wordTrace_append hprefix tailTrace_7738165
  have hstable : (prefixWord ++ tailWord_7738165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738165).length < 2 ^ (prefixWord ++ tailWord_7738165).sum := by decide
  have hdescent : baseEnd_7738165 < baseStart_7738165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738185 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 2, 3, 2]
def baseStart_7738185 : Nat := 118140960795 + 7738185 * 2 ^ 59
def prefixEnd_7738185 : Nat := 4983230072969 + 3 ^ 40 * 7738185 * 2
def baseEnd_7738185 : Nat := 3973408298411912049300241

theorem tailTrace_7738185 : CollatzResearch.WordTrace tailWord_7738185 prefixEnd_7738185 3973408298411912049300241 := by
  unfold tailWord_7738185
  simp only [CollatzResearch.WordTrace]
  refine ⟨282234793470884796627008009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188156528980589864418005339 282234793470884796627008009)
  ·
    refine ⟨211676095103163597470256007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282234793470884796627008009 211676095103163597470256007)
    ·
      refine ⟨317514142654745396205384011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211676095103163597470256007 317514142654745396205384011)
      ·
        refine ⟨476271213982118094308076017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317514142654745396205384011 476271213982118094308076017)
        ·
          refine ⟨357203410486588570731057013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476271213982118094308076017 357203410486588570731057013)
          ·
            refine ⟨33487819733117678506036595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357203410486588570731057013 33487819733117678506036595)
            ·
              refine ⟨50231729599676517759054893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33487819733117678506036595 50231729599676517759054893)
              ·
                refine ⟨18836898599878694159645585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50231729599676517759054893 18836898599878694159645585)
                ·
                  refine ⟨14127673949909020619734189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18836898599878694159645585 14127673949909020619734189)
                  ·
                    refine ⟨5297877731215882732400321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14127673949909020619734189 5297877731215882732400321)
                    ·
                      refine ⟨3973408298411912049300241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297877731215882732400321 3973408298411912049300241)
                      ·
                        rfl

theorem cell23_7738185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 3, 2].length) (baseStart_7738185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738185 prefixEnd_7738185 := by exact prefixLift 7738185
  have htrace : WordTrace (prefixWord ++ tailWord_7738185) baseStart_7738185 baseEnd_7738185 := by
    simpa [prefixWord, tailWord_7738185, baseEnd_7738185] using wordTrace_append hprefix tailTrace_7738185
  have hstable : (prefixWord ++ tailWord_7738185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738185).length < 2 ^ (prefixWord ++ tailWord_7738185).sum := by decide
  have hdescent : baseEnd_7738185 < baseStart_7738185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738225 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 2, 4]
def baseStart_7738225 : Nat := 118140960795 + 7738225 * 2 ^ 59
def prefixEnd_7738225 : Nat := 4983230072969 + 3 ^ 40 * 7738225 * 2
def baseEnd_7738225 : Nat := 1324476279212697297600019

theorem tailTrace_7738225 : CollatzResearch.WordTrace tailWord_7738225 prefixEnd_7738225 1324476279212697297600019 := by
  unfold tailWord_7738225
  simp only [CollatzResearch.WordTrace]
  refine ⟨282236252390739883458464129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188157501593826588972309419 282236252390739883458464129)
  ·
    refine ⟨211677189293054912593848097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282236252390739883458464129 211677189293054912593848097)
    ·
      refine ⟨158757891969791184445386073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211677189293054912593848097 158757891969791184445386073)
      ·
        refine ⟨119068418977343388334039555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158757891969791184445386073 119068418977343388334039555)
        ·
          refine ⟨178602628466015082501059333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119068418977343388334039555 178602628466015082501059333)
          ·
            refine ⟨33487992837377827968948625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178602628466015082501059333 33487992837377827968948625)
            ·
              refine ⟨25115994628033370976711469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33487992837377827968948625 25115994628033370976711469)
              ·
                refine ⟨9418497985512514116266801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25115994628033370976711469 9418497985512514116266801)
                ·
                  refine ⟨7063873489134385587200101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418497985512514116266801 7063873489134385587200101)
                  ·
                    refine ⟨1324476279212697297600019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7063873489134385587200101 1324476279212697297600019)
                    ·
                      rfl

theorem cell23_7738225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 4].length) (baseStart_7738225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738225 prefixEnd_7738225 := by exact prefixLift 7738225
  have htrace : WordTrace (prefixWord ++ tailWord_7738225) baseStart_7738225 baseEnd_7738225 := by
    simpa [prefixWord, tailWord_7738225, baseEnd_7738225] using wordTrace_append hprefix tailTrace_7738225
  have hstable : (prefixWord ++ tailWord_7738225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738225).length < 2 ^ (prefixWord ++ tailWord_7738225).sum := by decide
  have hdescent : baseEnd_7738225 < baseStart_7738225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738231 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_7738231 : Nat := 118140960795 + 7738231 * 2 ^ 59
def prefixEnd_7738231 : Nat := 4983230072969 + 3 ^ 40 * 7738231 * 2
def baseEnd_7738231 : Nat := 3973431918522018869325029

theorem tailTrace_7738231 : CollatzResearch.WordTrace tailWord_7738231 prefixEnd_7738231 3973431918522018869325029 := by
  unfold tailWord_7738231
  simp only [CollatzResearch.WordTrace]
  refine ⟨282236471228718146483182547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188157647485812097655455031 282236471228718146483182547)
  ·
    refine ⟨423354706843077219724773821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282236471228718146483182547 423354706843077219724773821)
    ·
      refine ⟨158758015066153957396790183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423354706843077219724773821 158758015066153957396790183)
      ·
        refine ⟨238137022599230936095185275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158758015066153957396790183 238137022599230936095185275)
        ·
          refine ⟨357205533898846404142777913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238137022599230936095185275 357205533898846404142777913)
          ·
            refine ⟨267904150424134803107083435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357205533898846404142777913 267904150424134803107083435)
            ·
              refine ⟨401856225636202204660625153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267904150424134803107083435 401856225636202204660625153)
              ·
                refine ⟨301392169227151653495468865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401856225636202204660625153 301392169227151653495468865)
                ·
                  refine ⟨226044126920363740121601649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301392169227151653495468865 226044126920363740121601649)
                  ·
                    refine ⟨169533095190272805091201237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226044126920363740121601649 169533095190272805091201237)
                    ·
                      refine ⟨3973431918522018869325029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169533095190272805091201237 3973431918522018869325029)
                      ·
                        rfl

theorem cell23_7738231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_7738231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738231 prefixEnd_7738231 := by exact prefixLift 7738231
  have htrace : WordTrace (prefixWord ++ tailWord_7738231) baseStart_7738231 baseEnd_7738231 := by
    simpa [prefixWord, tailWord_7738231, baseEnd_7738231] using wordTrace_append hprefix tailTrace_7738231
  have hstable : (prefixWord ++ tailWord_7738231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738231).length < 2 ^ (prefixWord ++ tailWord_7738231).sum := by decide
  have hdescent : baseEnd_7738231 < baseStart_7738231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738249 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 1, 2, 2]
def baseStart_7738249 : Nat := 118140960795 + 7738249 * 2 ^ 59
def prefixEnd_7738249 : Nat := 4983230072969 + 3 ^ 40 * 7738249 * 2
def baseEnd_7738249 : Nat := 3973441161173799798899947

theorem tailTrace_7738249 : CollatzResearch.WordTrace tailWord_7738249 prefixEnd_7738249 3973441161173799798899947 := by
  unfold tailWord_7738249
  simp only [CollatzResearch.WordTrace]
  refine ⟨282237127742652935557337801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188158085161768623704891867 282237127742652935557337801)
  ·
    refine ⟨211677845806989701668003351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282237127742652935557337801 211677845806989701668003351)
    ·
      refine ⟨317516768710484552502005027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211677845806989701668003351 317516768710484552502005027)
      ·
        refine ⟨476275153065726828753007541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317516768710484552502005027 476275153065726828753007541)
        ·
          refine ⟨44650795599911890195594457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 476275153065726828753007541 44650795599911890195594457)
          ·
            refine ⟨33488096699933917646695843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44650795599911890195594457 33488096699933917646695843)
            ·
              refine ⟨50232145049900876470043765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33488096699933917646695843 50232145049900876470043765)
              ·
                refine ⟨4709263598428207169066603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50232145049900876470043765 4709263598428207169066603)
                ·
                  refine ⟨7063895397642310753599905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709263598428207169066603 7063895397642310753599905)
                  ·
                    refine ⟨5297921548231733065199929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063895397642310753599905 5297921548231733065199929)
                    ·
                      refine ⟨3973441161173799798899947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297921548231733065199929 3973441161173799798899947)
                      ·
                        rfl

theorem cell23_7738249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 1, 2, 2].length) (baseStart_7738249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738249 prefixEnd_7738249 := by exact prefixLift 7738249
  have htrace : WordTrace (prefixWord ++ tailWord_7738249) baseStart_7738249 baseEnd_7738249 := by
    simpa [prefixWord, tailWord_7738249, baseEnd_7738249] using wordTrace_append hprefix tailTrace_7738249
  have hstable : (prefixWord ++ tailWord_7738249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738249).length < 2 ^ (prefixWord ++ tailWord_7738249).sum := by decide
  have hdescent : baseEnd_7738249 < baseStart_7738249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738252 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_7738252 : Nat := 118140960795 + 7738252 * 2 ^ 59
def prefixEnd_7738252 : Nat := 4983230072969 + 3 ^ 40 * 7738252 * 2
def baseEnd_7738252 : Nat := 3973442701615763287162433

theorem tailTrace_7738252 : CollatzResearch.WordTrace tailWord_7738252 prefixEnd_7738252 3973442701615763287162433 := by
  unfold tailWord_7738252
  simp only [CollatzResearch.WordTrace]
  refine ⟨141118618580821033534848505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188158158107761378046464673 141118618580821033534848505)
  ·
    refine ⟨105838963935615775151136379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141118618580821033534848505 105838963935615775151136379)
    ·
      refine ⟨158758445903423662726704569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105838963935615775151136379 158758445903423662726704569)
      ·
        refine ⟨119068834427567747045028427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158758445903423662726704569 119068834427567747045028427)
        ·
          refine ⟨178603251641351620567542641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119068834427567747045028427 178603251641351620567542641)
          ·
            refine ⟨133952438731013715425656981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178603251641351620567542641 133952438731013715425656981)
            ·
              refine ⟨6279020565516267910577671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133952438731013715425656981 6279020565516267910577671)
              ·
                refine ⟨9418530848274401865866507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279020565516267910577671 9418530848274401865866507)
                ·
                  refine ⟨14127796272411602798799761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418530848274401865866507 14127796272411602798799761)
                  ·
                    refine ⟨10595847204308702099099821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14127796272411602798799761 10595847204308702099099821)
                    ·
                      refine ⟨3973442701615763287162433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10595847204308702099099821 3973442701615763287162433)
                      ·
                        rfl

theorem cell23_7738252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_7738252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738252 prefixEnd_7738252 := by exact prefixLift 7738252
  have htrace : WordTrace (prefixWord ++ tailWord_7738252) baseStart_7738252 baseEnd_7738252 := by
    simpa [prefixWord, tailWord_7738252, baseEnd_7738252] using wordTrace_append hprefix tailTrace_7738252
  have hstable : (prefixWord ++ tailWord_7738252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738252).length < 2 ^ (prefixWord ++ tailWord_7738252).sum := by decide
  have hdescent : baseEnd_7738252 < baseStart_7738252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738275 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 5, 3, 2]
def baseStart_7738275 : Nat := 118140960795 + 7738275 * 2 ^ 59
def prefixEnd_7738275 : Nat := 4983230072969 + 3 ^ 40 * 7738275 * 2
def baseEnd_7738275 : Nat := 3973454511670816697174827

theorem tailTrace_7738275 : CollatzResearch.WordTrace tailWord_7738275 prefixEnd_7738275 3973454511670816697174827 := by
  unfold tailWord_7738275
  simp only [CollatzResearch.WordTrace]
  refine ⟨282238076040558741997784279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188158717360372494665189519 282238076040558741997784279)
  ·
    refine ⟨423357114060838112996676419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282238076040558741997784279 423357114060838112996676419)
    ·
      refine ⟨635035671091257169495014629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423357114060838112996676419 635035671091257169495014629)
      ·
        refine ⟨119069188329610719280315243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 635035671091257169495014629 119069188329610719280315243)
        ·
          refine ⟨178603782494416078920472865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119069188329610719280315243 178603782494416078920472865)
          ·
            refine ⟨133952836870812059190354649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178603782494416078920472865 133952836870812059190354649)
            ·
              refine ⟨100464627653109044392765987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133952836870812059190354649 100464627653109044392765987)
              ·
                refine ⟨150696941479663566589148981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100464627653109044392765987 150696941479663566589148981)
                ·
                  refine ⟨14127838263718459367732717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 150696941479663566589148981 14127838263718459367732717)
                  ·
                    refine ⟨5297939348894422262899769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14127838263718459367732717 5297939348894422262899769)
                    ·
                      refine ⟨3973454511670816697174827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297939348894422262899769 3973454511670816697174827)
                      ·
                        rfl

theorem cell23_7738275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_7738275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738275 prefixEnd_7738275 := by exact prefixLift 7738275
  have htrace : WordTrace (prefixWord ++ tailWord_7738275) baseStart_7738275 baseEnd_7738275 := by
    simpa [prefixWord, tailWord_7738275, baseEnd_7738275] using wordTrace_append hprefix tailTrace_7738275
  have hstable : (prefixWord ++ tailWord_7738275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738275).length < 2 ^ (prefixWord ++ tailWord_7738275).sum := by decide
  have hdescent : baseEnd_7738275 < baseStart_7738275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738279 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7738279 : Nat := 118140960795 + 7738279 * 2 ^ 59
def prefixEnd_7738279 : Nat := 4983230072969 + 3 ^ 40 * 7738279 * 2
def baseEnd_7738279 : Nat := 3973456565593434681524809

theorem tailTrace_7738279 : CollatzResearch.WordTrace tailWord_7738279 prefixEnd_7738279 3973456565593434681524809 := by
  unfold tailWord_7738279
  simp only [CollatzResearch.WordTrace]
  refine ⟨282238221932544250680929891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188158814621696167120619927 282238221932544250680929891)
  ·
    refine ⟨423357332898816376021394837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282238221932544250680929891 423357332898816376021394837)
    ·
      refine ⟨19844874979632017626002883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 423357332898816376021394837 19844874979632017626002883)
      ·
        refine ⟨29767312469448026439004325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19844874979632017626002883 29767312469448026439004325)
        ·
          refine ⟨5581371088021504957313311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29767312469448026439004325 5581371088021504957313311)
          ·
            refine ⟨8372056632032257435969967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581371088021504957313311 8372056632032257435969967)
            ·
              refine ⟨12558084948048386153954951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372056632032257435969967 12558084948048386153954951)
              ·
                refine ⟨18837127422072579230932427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12558084948048386153954951 18837127422072579230932427)
                ·
                  refine ⟨28255691133108868846398641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18837127422072579230932427 28255691133108868846398641)
                  ·
                    refine ⟨21191768349831651634798981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28255691133108868846398641 21191768349831651634798981)
                    ·
                      refine ⟨3973456565593434681524809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21191768349831651634798981 3973456565593434681524809)
                      ·
                        rfl

theorem cell23_7738279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7738279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738279 prefixEnd_7738279 := by exact prefixLift 7738279
  have htrace : WordTrace (prefixWord ++ tailWord_7738279) baseStart_7738279 baseEnd_7738279 := by
    simpa [prefixWord, tailWord_7738279, baseEnd_7738279] using wordTrace_append hprefix tailTrace_7738279
  have hstable : (prefixWord ++ tailWord_7738279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738279).length < 2 ^ (prefixWord ++ tailWord_7738279).sum := by decide
  have hdescent : baseEnd_7738279 < baseStart_7738279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738317 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_7738317 : Nat := 118140960795 + 7738317 * 2 ^ 59
def prefixEnd_7738317 : Nat := 4983230072969 + 3 ^ 40 * 7738317 * 2
def baseEnd_7738317 : Nat := 3973476077858305532849635

theorem tailTrace_7738317 : CollatzResearch.WordTrace tailWord_7738317 prefixEnd_7738317 3973476077858305532849635 := by
  unfold tailWord_7738317
  simp only [CollatzResearch.WordTrace]
  refine ⟨282239607906406583170813205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188159738604271055447208803 282239607906406583170813205)
  ·
    refine ⟨13229981620612808586131869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 282239607906406583170813205 13229981620612808586131869)
    ·
      refine ⟨4961243107729803219799451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13229981620612808586131869 4961243107729803219799451)
      ·
        refine ⟨7441864661594704829699177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961243107729803219799451 7441864661594704829699177)
        ·
          refine ⟨5581398496196028622274383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7441864661594704829699177 5581398496196028622274383)
          ·
            refine ⟨8372097744294042933411575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581398496196028622274383 8372097744294042933411575)
            ·
              refine ⟨12558146616441064400117363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372097744294042933411575 12558146616441064400117363)
              ·
                refine ⟨18837219924661596600176045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12558146616441064400117363 18837219924661596600176045)
                ·
                  refine ⟨7063957471748098725066017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18837219924661596600176045 7063957471748098725066017)
                  ·
                    refine ⟨5297968103811074043799513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063957471748098725066017 5297968103811074043799513)
                    ·
                      refine ⟨3973476077858305532849635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297968103811074043799513 3973476077858305532849635)
                      ·
                        rfl

theorem cell23_7738317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_7738317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738317 prefixEnd_7738317 := by exact prefixLift 7738317
  have htrace : WordTrace (prefixWord ++ tailWord_7738317) baseStart_7738317 baseEnd_7738317 := by
    simpa [prefixWord, tailWord_7738317, baseEnd_7738317] using wordTrace_append hprefix tailTrace_7738317
  have hstable : (prefixWord ++ tailWord_7738317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738317).length < 2 ^ (prefixWord ++ tailWord_7738317).sum := by decide
  have hdescent : baseEnd_7738317 < baseStart_7738317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738339 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7738339 : Nat := 118140960795 + 7738339 * 2 ^ 59
def prefixEnd_7738339 : Nat := 4983230072969 + 3 ^ 40 * 7738339 * 2
def baseEnd_7738339 : Nat := 3973487374432704446774533

theorem tailTrace_7738339 : CollatzResearch.WordTrace tailWord_7738339 prefixEnd_7738339 3973487374432704446774533 := by
  unfold tailWord_7738339
  simp only [CollatzResearch.WordTrace]
  refine ⟨282240410312326880928114071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188160273541551253952076047 282240410312326880928114071)
  ·
    refine ⟨423360615468490321392171107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282240410312326880928114071 423360615468490321392171107)
    ·
      refine ⟨635040923202735482088256661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423360615468490321392171107 635040923202735482088256661)
      ·
        refine ⟨29767543275128225722887031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 635040923202735482088256661 29767543275128225722887031)
        ·
          refine ⟨44651314912692338584330547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29767543275128225722887031 44651314912692338584330547)
          ·
            refine ⟨66976972369038507876495821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44651314912692338584330547 66976972369038507876495821)
            ·
              refine ⟨25116364638389440453685933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66976972369038507876495821 25116364638389440453685933)
              ·
                refine ⟨9418636739396040170132225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25116364638389440453685933 9418636739396040170132225)
                ·
                  refine ⟨7063977554547030127599169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9418636739396040170132225 7063977554547030127599169)
                  ·
                    refine ⟨5297983165910272595699377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7063977554547030127599169 5297983165910272595699377)
                    ·
                      refine ⟨3973487374432704446774533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5297983165910272595699377 3973487374432704446774533)
                      ·
                        rfl

theorem cell23_7738339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7738339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738339 prefixEnd_7738339 := by exact prefixLift 7738339
  have htrace : WordTrace (prefixWord ++ tailWord_7738339) baseStart_7738339 baseEnd_7738339 := by
    simpa [prefixWord, tailWord_7738339, baseEnd_7738339] using wordTrace_append hprefix tailTrace_7738339
  have hstable : (prefixWord ++ tailWord_7738339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738339).length < 2 ^ (prefixWord ++ tailWord_7738339).sum := by decide
  have hdescent : baseEnd_7738339 < baseStart_7738339 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738375 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 2, 5]
def baseStart_7738375 : Nat := 118140960795 + 7738375 * 2 ^ 59
def prefixEnd_7738375 : Nat := 4983230072969 + 3 ^ 40 * 7738375 * 2
def baseEnd_7738375 : Nat := 1324501953245422101974789

theorem tailTrace_7738375 : CollatzResearch.WordTrace tailWord_7738375 prefixEnd_7738375 1324501953245422101974789 := by
  unfold tailWord_7738375
  simp only [CollatzResearch.WordTrace]
  refine ⟨282241723340196459076424579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188161148893464306050949719 282241723340196459076424579)
  ·
    refine ⟨423362585010294688614636869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282241723340196459076424579 423362585010294688614636869)
    ·
      refine ⟨79380484689430254115244413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423362585010294688614636869 79380484689430254115244413)
      ·
        refine ⟨29767681758536345293216655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79380484689430254115244413 29767681758536345293216655)
        ·
          refine ⟨44651522637804517939824983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29767681758536345293216655 44651522637804517939824983)
          ·
            refine ⟨66977283956706776909737475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44651522637804517939824983 66977283956706776909737475)
            ·
              refine ⟨100465925935060165364606213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66977283956706776909737475 100465925935060165364606213)
              ·
                refine ⟨18837361112823781005863665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100465925935060165364606213 18837361112823781005863665)
                ·
                  refine ⟨14128020834617835754397749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18837361112823781005863665 14128020834617835754397749)
                  ·
                    refine ⟨1324501953245422101974789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14128020834617835754397749 1324501953245422101974789)
                    ·
                      rfl

theorem cell23_7738375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_7738375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738375 prefixEnd_7738375 := by exact prefixLift 7738375
  have htrace : WordTrace (prefixWord ++ tailWord_7738375) baseStart_7738375 baseEnd_7738375 := by
    simpa [prefixWord, tailWord_7738375, baseEnd_7738375] using wordTrace_append hprefix tailTrace_7738375
  have hstable : (prefixWord ++ tailWord_7738375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738375).length < 2 ^ (prefixWord ++ tailWord_7738375).sum := by decide
  have hdescent : baseEnd_7738375 < baseStart_7738375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738379 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 5]
def baseStart_7738379 : Nat := 118140960795 + 7738379 * 2 ^ 59
def prefixEnd_7738379 : Nat := 4983230072969 + 3 ^ 40 * 7738379 * 2
def baseEnd_7738379 : Nat := 441500879295431587808261

theorem tailTrace_7738379 : CollatzResearch.WordTrace tailWord_7738379 prefixEnd_7738379 441500879295431587808261 := by
  unfold tailWord_7738379
  simp only [CollatzResearch.WordTrace]
  refine ⟨282241869232181967759570191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188161246154787978506380127 282241869232181967759570191)
  ·
    refine ⟨423362803848272951639355287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282241869232181967759570191 423362803848272951639355287)
    ·
      refine ⟨635044205772409427459032931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423362803848272951639355287 635044205772409427459032931)
      ·
        refine ⟨952566308658614141188549397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635044205772409427459032931 952566308658614141188549397)
        ·
          refine ⟨44651545718372537868213253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 952566308658614141188549397 44651545718372537868213253)
          ·
            refine ⟨8372164822194850850289985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44651545718372537868213253 8372164822194850850289985)
            ·
              refine ⟨6279123616646138137717489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372164822194850850289985 6279123616646138137717489)
              ·
                refine ⟨4709342712484603603288117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279123616646138137717489 4709342712484603603288117)
                ·
                  refine ⟨441500879295431587808261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4709342712484603603288117 441500879295431587808261)
                  ·
                    rfl

theorem cell23_7738379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 5].length) (baseStart_7738379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738379 prefixEnd_7738379 := by exact prefixLift 7738379
  have htrace : WordTrace (prefixWord ++ tailWord_7738379) baseStart_7738379 baseEnd_7738379 := by
    simpa [prefixWord, tailWord_7738379, baseEnd_7738379] using wordTrace_append hprefix tailTrace_7738379
  have hstable : (prefixWord ++ tailWord_7738379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738379).length < 2 ^ (prefixWord ++ tailWord_7738379).sum := by decide
  have hdescent : baseEnd_7738379 < baseStart_7738379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738382 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7738382 : Nat := 118140960795 + 7738382 * 2 ^ 59
def prefixEnd_7738382 : Nat := 4983230072969 + 3 ^ 40 * 7738382 * 2
def baseEnd_7738382 : Nat := 3973509454100847778536835

theorem tailTrace_7738382 : CollatzResearch.WordTrace tailWord_7738382 prefixEnd_7738382 3973509454100847778536835 := by
  unfold tailWord_7738382
  simp only [CollatzResearch.WordTrace]
  refine ⟨35280247331396387408991175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188161319100780732847952933 35280247331396387408991175)
  ·
    refine ⟨52920370997094581113486763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35280247331396387408991175 52920370997094581113486763)
    ·
      refine ⟨79380556495641871670230145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52920370997094581113486763 79380556495641871670230145)
      ·
        refine ⟨59535417371731403752672609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79380556495641871670230145 59535417371731403752672609)
        ·
          refine ⟨44651563028798552814504457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59535417371731403752672609 44651563028798552814504457)
          ·
            refine ⟨33488672271598914610878343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44651563028798552814504457 33488672271598914610878343)
            ·
              refine ⟨50233008407398371916317515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33488672271598914610878343 50233008407398371916317515)
              ·
                refine ⟨75349512611097557874476273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50233008407398371916317515 75349512611097557874476273)
                ·
                  refine ⟨56512134458323168405857205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75349512611097557874476273 56512134458323168405857205)
                  ·
                    refine ⟨5298012605467797038049113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56512134458323168405857205 5298012605467797038049113)
                    ·
                      refine ⟨3973509454100847778536835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298012605467797038049113 3973509454100847778536835)
                      ·
                        rfl

theorem cell23_7738382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7738382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738382 prefixEnd_7738382 := by exact prefixLift 7738382
  have htrace : WordTrace (prefixWord ++ tailWord_7738382) baseStart_7738382 baseEnd_7738382 := by
    simpa [prefixWord, tailWord_7738382, baseEnd_7738382] using wordTrace_append hprefix tailTrace_7738382
  have hstable : (prefixWord ++ tailWord_7738382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738382).length < 2 ^ (prefixWord ++ tailWord_7738382).sum := by decide
  have hdescent : baseEnd_7738382 < baseStart_7738382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738386 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7738386 : Nat := 118140960795 + 7738386 * 2 ^ 59
def prefixEnd_7738386 : Nat := 4983230072969 + 3 ^ 40 * 7738386 * 2
def baseEnd_7738386 : Nat := 3973511508023465762886817

theorem tailTrace_7738386 : CollatzResearch.WordTrace tailWord_7738386 prefixEnd_7738386 3973511508023465762886817 := by
  unfold tailWord_7738386
  simp only [CollatzResearch.WordTrace]
  refine ⟨70560531135789151988768753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188161416362104405303383341 70560531135789151988768753)
  ·
    refine ⟨52920398351841863991576565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70560531135789151988768753 52920398351841863991576565)
    ·
      refine ⟨4961287345485174749210303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52920398351841863991576565 4961287345485174749210303)
      ·
        refine ⟨7441931018227762123815455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4961287345485174749210303 7441931018227762123815455)
        ·
          refine ⟨11162896527341643185723183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7441931018227762123815455 11162896527341643185723183)
          ·
            refine ⟨16744344791012464778584775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11162896527341643185723183 16744344791012464778584775)
            ·
              refine ⟨25116517186518697167877163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16744344791012464778584775 25116517186518697167877163)
              ·
                refine ⟨37674775779778045751815745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25116517186518697167877163 37674775779778045751815745)
                ·
                  refine ⟨28256081834833534313861809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37674775779778045751815745 28256081834833534313861809)
                  ·
                    refine ⟨21192061376125150735396357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28256081834833534313861809 21192061376125150735396357)
                    ·
                      refine ⟨3973511508023465762886817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21192061376125150735396357 3973511508023465762886817)
                      ·
                        rfl

theorem cell23_7738386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7738386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738386 prefixEnd_7738386 := by exact prefixLift 7738386
  have htrace : WordTrace (prefixWord ++ tailWord_7738386) baseStart_7738386 baseEnd_7738386 := by
    simpa [prefixWord, tailWord_7738386, baseEnd_7738386] using wordTrace_append hprefix tailTrace_7738386
  have hstable : (prefixWord ++ tailWord_7738386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738386).length < 2 ^ (prefixWord ++ tailWord_7738386).sum := by decide
  have hdescent : baseEnd_7738386 < baseStart_7738386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738425 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7738425 : Nat := 118140960795 + 7738425 * 2 ^ 59
def prefixEnd_7738425 : Nat := 4983230072969 + 3 ^ 40 * 7738425 * 2
def baseEnd_7738425 : Nat := 3973531533768991110299137

theorem tailTrace_7738425 : CollatzResearch.WordTrace tailWord_7738425 prefixEnd_7738425 3973531533768991110299137 := by
  unfold tailWord_7738425
  simp only [CollatzResearch.WordTrace]
  refine ⟨282243546990015317615744729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188162364660010211743829819 282243546990015317615744729)
  ·
    refine ⟨211682660242511488211808547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282243546990015317615744729 211682660242511488211808547)
    ·
      refine ⟨317523990363767232317712821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211682660242511488211808547 317523990363767232317712821)
      ·
        refine ⟨29767874096603178029785577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317523990363767232317712821 29767874096603178029785577)
        ·
          refine ⟨22325905572452383522339183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29767874096603178029785577 22325905572452383522339183)
          ·
            refine ⟨33488858358678575283508775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22325905572452383522339183 33488858358678575283508775)
            ·
              refine ⟨50233287538017862925263163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33488858358678575283508775 50233287538017862925263163)
              ·
                refine ⟨75349931307026794387894745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50233287538017862925263163 75349931307026794387894745)
                ·
                  refine ⟨56512448480270095790921059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75349931307026794387894745 56512448480270095790921059)
                  ·
                    refine ⟨84768672720405143686381589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56512448480270095790921059 84768672720405143686381589)
                    ·
                      refine ⟨3973531533768991110299137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84768672720405143686381589 3973531533768991110299137)
                      ·
                        rfl

theorem cell23_7738425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7738425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738425 prefixEnd_7738425 := by exact prefixLift 7738425
  have htrace : WordTrace (prefixWord ++ tailWord_7738425) baseStart_7738425 baseEnd_7738425 := by
    simpa [prefixWord, tailWord_7738425, baseEnd_7738425] using wordTrace_append hprefix tailTrace_7738425
  have hstable : (prefixWord ++ tailWord_7738425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738425).length < 2 ^ (prefixWord ++ tailWord_7738425).sum := by decide
  have hdescent : baseEnd_7738425 < baseStart_7738425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738439 : List Nat := [1, 1, 4, 1, 3, 2, 2, 4, 1, 4]
def baseStart_7738439 : Nat := 118140960795 + 7738439 * 2 ^ 59
def prefixEnd_7738439 : Nat := 4983230072969 + 3 ^ 40 * 7738439 * 2
def baseEnd_7738439 : Nat := 1324512907499384685174691

theorem tailTrace_7738439 : CollatzResearch.WordTrace tailWord_7738439 prefixEnd_7738439 1324512907499384685174691 := by
  unfold tailWord_7738439
  simp only [CollatzResearch.WordTrace]
  refine ⟨282244057611964598006754371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188162705074643065337836247 282244057611964598006754371)
  ·
    refine ⟨423366086417946897010131557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282244057611964598006754371 423366086417946897010131557)
    ·
      refine ⟨79381141203365043189399667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423366086417946897010131557 79381141203365043189399667)
      ·
        refine ⟨119071711805047564784099501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79381141203365043189399667 119071711805047564784099501)
        ·
          refine ⟨44651891926892836794037313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119071711805047564784099501 44651891926892836794037313)
          ·
            refine ⟨33488918945169627595527985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44651891926892836794037313 33488918945169627595527985)
            ·
              refine ⟨25116689208877220696645989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33488918945169627595527985 25116689208877220696645989)
              ·
                refine ⟨4709379226664478880621123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25116689208877220696645989 4709379226664478880621123)
                ·
                  refine ⟨7064068839996718320931685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709379226664478880621123 7064068839996718320931685)
                  ·
                    refine ⟨1324512907499384685174691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7064068839996718320931685 1324512907499384685174691)
                    ·
                      rfl

theorem cell23_7738439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_7738439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738439 prefixEnd_7738439 := by exact prefixLift 7738439
  have htrace : WordTrace (prefixWord ++ tailWord_7738439) baseStart_7738439 baseEnd_7738439 := by
    simpa [prefixWord, tailWord_7738439, baseEnd_7738439] using wordTrace_append hprefix tailTrace_7738439
  have hstable : (prefixWord ++ tailWord_7738439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738439).length < 2 ^ (prefixWord ++ tailWord_7738439).sum := by decide
  have hdescent : baseEnd_7738439 < baseStart_7738439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738465 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 3, 5]
def baseStart_7738465 : Nat := 118140960795 + 7738465 * 2 ^ 59
def prefixEnd_7738465 : Nat := 4983230072969 + 3 ^ 40 * 7738465 * 2
def baseEnd_7738465 : Nat := 1324517357665056984599651

theorem tailTrace_7738465 : CollatzResearch.WordTrace tailWord_7738465 prefixEnd_7738465 1324517357665056984599651 := by
  unfold tailWord_7738465
  simp only [CollatzResearch.WordTrace]
  refine ⟨282245005909870404447200849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188163337273246936298133899 282245005909870404447200849)
  ·
    refine ⟨211683754432402803335400637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282245005909870404447200849 211683754432402803335400637)
    ·
      refine ⟨79381407912151051250775239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211683754432402803335400637 79381407912151051250775239)
      ·
        refine ⟨119072111868226576876162859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79381407912151051250775239 119072111868226576876162859)
        ·
          refine ⟨178608167802339865314244289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119072111868226576876162859 178608167802339865314244289)
          ·
            refine ⟨133956125851754898985683217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178608167802339865314244289 133956125851754898985683217)
            ·
              refine ⟨100467094388816174239262413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133956125851754898985683217 100467094388816174239262413)
              ·
                refine ⟨37675160395806065339723405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100467094388816174239262413 37675160395806065339723405)
                ·
                  refine ⟨14128185148427274502396277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37675160395806065339723405 14128185148427274502396277)
                  ·
                    refine ⟨1324517357665056984599651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14128185148427274502396277 1324517357665056984599651)
                    ·
                      rfl

theorem cell23_7738465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_7738465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738465 prefixEnd_7738465 := by exact prefixLift 7738465
  have htrace : WordTrace (prefixWord ++ tailWord_7738465) baseStart_7738465 baseEnd_7738465 := by
    simpa [prefixWord, tailWord_7738465, baseEnd_7738465] using wordTrace_append hprefix tailTrace_7738465
  have hstable : (prefixWord ++ tailWord_7738465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738465).length < 2 ^ (prefixWord ++ tailWord_7738465).sum := by decide
  have hdescent : baseEnd_7738465 < baseStart_7738465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738482 : List Nat := [3, 2, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_7738482 : Nat := 118140960795 + 7738482 * 2 ^ 59
def prefixEnd_7738482 : Nat := 4983230072969 + 3 ^ 40 * 7738482 * 2
def baseEnd_7738482 : Nat := 1324520267388765795762125

theorem tailTrace_7738482 : CollatzResearch.WordTrace tailWord_7738482 prefixEnd_7738482 1324520267388765795762125 := by
  unfold tailWord_7738482
  simp only [CollatzResearch.WordTrace]
  refine ⟨70561406487702204087642425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188163750633872544233713133 70561406487702204087642425)
  ·
    refine ⟨52921054865776653065731819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70561406487702204087642425 52921054865776653065731819)
    ·
      refine ⟨79381582298664979598597729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52921054865776653065731819 79381582298664979598597729)
      ·
        refine ⟨59536186723998734698948297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79381582298664979598597729 59536186723998734698948297)
        ·
          refine ⟨44652140042999051024211223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59536186723998734698948297 44652140042999051024211223)
          ·
            refine ⟨66978210064498576536316835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44652140042999051024211223 66978210064498576536316835)
            ·
              refine ⟨100467315096747864804475253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66978210064498576536316835 100467315096747864804475253)
              ·
                refine ⟨9418810790320112325419555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100467315096747864804475253 9418810790320112325419555)
                ·
                  refine ⟨14128216185480168488129333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418810790320112325419555 14128216185480168488129333)
                  ·
                    refine ⟨1324520267388765795762125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14128216185480168488129333 1324520267388765795762125)
                    ·
                      rfl

theorem cell23_7738482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_7738482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738482 prefixEnd_7738482 := by exact prefixLift 7738482
  have htrace : WordTrace (prefixWord ++ tailWord_7738482) baseStart_7738482 baseEnd_7738482 := by
    simpa [prefixWord, tailWord_7738482, baseEnd_7738482] using wordTrace_append hprefix tailTrace_7738482
  have hstable : (prefixWord ++ tailWord_7738482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738482).length < 2 ^ (prefixWord ++ tailWord_7738482).sum := by decide
  have hdescent : baseEnd_7738482 < baseStart_7738482 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738515 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_7738515 : Nat := 118140960795 + 7738515 * 2 ^ 59
def prefixEnd_7738515 : Nat := 4983230072969 + 3 ^ 40 * 7738515 * 2
def baseEnd_7738515 : Nat := 3973577747027895758173723

theorem tailTrace_7738515 : CollatzResearch.WordTrace tailWord_7738515 prefixEnd_7738515 3973577747027895758173723 := by
  unfold tailWord_7738515
  simp only [CollatzResearch.WordTrace]
  refine ⟨282246829559689262986520999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188164553039792841991013999 282246829559689262986520999)
  ·
    refine ⟨423370244339533894479781499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282246829559689262986520999 423370244339533894479781499)
    ·
      refine ⟨635055366509300841719672249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423370244339533894479781499 635055366509300841719672249)
      ·
        refine ⟨476291524881975631289754187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635055366509300841719672249 476291524881975631289754187)
        ·
          refine ⟨714437287322963446934631281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476291524881975631289754187 714437287322963446934631281)
          ·
            refine ⟨535827965492222585200973461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714437287322963446934631281 535827965492222585200973461)
            ·
              refine ⟨25116935882447933681295631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535827965492222585200973461 25116935882447933681295631)
              ·
                refine ⟨37675403823671900521943447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25116935882447933681295631 37675403823671900521943447)
                ·
                  refine ⟨56513105735507850782915171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37675403823671900521943447 56513105735507850782915171)
                  ·
                    refine ⟨84769658603261776174372757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56513105735507850782915171 84769658603261776174372757)
                    ·
                      refine ⟨3973577747027895758173723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84769658603261776174372757 3973577747027895758173723)
                      ·
                        rfl

theorem cell23_7738515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_7738515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738515 prefixEnd_7738515 := by exact prefixLift 7738515
  have htrace : WordTrace (prefixWord ++ tailWord_7738515) baseStart_7738515 baseEnd_7738515 := by
    simpa [prefixWord, tailWord_7738515, baseEnd_7738515] using wordTrace_append hprefix tailTrace_7738515
  have hstable : (prefixWord ++ tailWord_7738515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738515).length < 2 ^ (prefixWord ++ tailWord_7738515).sum := by decide
  have hdescent : baseEnd_7738515 < baseStart_7738515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738519 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_7738519 : Nat := 118140960795 + 7738519 * 2 ^ 59
def prefixEnd_7738519 : Nat := 4983230072969 + 3 ^ 40 * 7738519 * 2
def baseEnd_7738519 : Nat := 3973579800950513742523705

theorem tailTrace_7738519 : CollatzResearch.WordTrace tailWord_7738519 prefixEnd_7738519 3973579800950513742523705 := by
  unfold tailWord_7738519
  simp only [CollatzResearch.WordTrace]
  refine ⟨282246975451674771669666611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188164650301116514446444407 282246975451674771669666611)
  ·
    refine ⟨423370463177512157504499917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282246975451674771669666611 423370463177512157504499917)
    ·
      refine ⟨158763923691567059064187469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423370463177512157504499917 158763923691567059064187469)
      ·
        refine ⟨59536471384337647149070301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158763923691567059064187469 59536471384337647149070301)
        ·
          refine ⟨22326176769126617680901363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59536471384337647149070301 22326176769126617680901363)
          ·
            refine ⟨33489265153689926521352045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22326176769126617680901363 33489265153689926521352045)
            ·
              refine ⟨12558474432633722445507017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33489265153689926521352045 12558474432633722445507017)
              ·
                refine ⟨9418855824475291834130263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12558474432633722445507017 9418855824475291834130263)
                ·
                  refine ⟨14128283736712937751195395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9418855824475291834130263 14128283736712937751195395)
                  ·
                    refine ⟨21192425605069406626793093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14128283736712937751195395 21192425605069406626793093)
                    ·
                      refine ⟨3973579800950513742523705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21192425605069406626793093 3973579800950513742523705)
                      ·
                        rfl

theorem cell23_7738519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_7738519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738519 prefixEnd_7738519 := by exact prefixLift 7738519
  have htrace : WordTrace (prefixWord ++ tailWord_7738519) baseStart_7738519 baseEnd_7738519 := by
    simpa [prefixWord, tailWord_7738519, baseEnd_7738519] using wordTrace_append hprefix tailTrace_7738519
  have hstable : (prefixWord ++ tailWord_7738519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738519).length < 2 ^ (prefixWord ++ tailWord_7738519).sum := by decide
  have hdescent : baseEnd_7738519 < baseStart_7738519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738525 : List Nat := [1, 4, 2, 1, 1, 2, 1, 11]
def baseStart_7738525 : Nat := 118140960795 + 7738525 * 2 ^ 59
def prefixEnd_7738525 : Nat := 4983230072969 + 3 ^ 40 * 7738525 * 2
def baseEnd_7738525 : Nat := 147169736364238545149951

theorem tailTrace_7738525 : CollatzResearch.WordTrace tailWord_7738525 prefixEnd_7738525 147169736364238545149951 := by
  unfold tailWord_7738525
  simp only [CollatzResearch.WordTrace]
  refine ⟨282247194289653034694385029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188164796193102023129590019 282247194289653034694385029)
  ·
    refine ⟨52921348929309944005197193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282247194289653034694385029 52921348929309944005197193)
    ·
      refine ⟨39691011696982458003897895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52921348929309944005197193 39691011696982458003897895)
      ·
        refine ⟨59536517545473687005846843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39691011696982458003897895 59536517545473687005846843)
        ·
          refine ⟨89304776318210530508770265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59536517545473687005846843 89304776318210530508770265)
          ·
            refine ⟨66978582238657897881577699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89304776318210530508770265 66978582238657897881577699)
            ·
              refine ⟨100467873357986846822366549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66978582238657897881577699 100467873357986846822366549)
              ·
                refine ⟨147169736364238545149951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 100467873357986846822366549 147169736364238545149951)
                ·
                  rfl

theorem cell23_7738525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 11].length) (baseStart_7738525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738525 prefixEnd_7738525 := by exact prefixLift 7738525
  have htrace : WordTrace (prefixWord ++ tailWord_7738525) baseStart_7738525 baseEnd_7738525 := by
    simpa [prefixWord, tailWord_7738525, baseEnd_7738525] using wordTrace_append hprefix tailTrace_7738525
  have hstable : (prefixWord ++ tailWord_7738525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738525).length < 2 ^ (prefixWord ++ tailWord_7738525).sum := by decide
  have hdescent : baseEnd_7738525 < baseStart_7738525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738532 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_7738532 : Nat := 118140960795 + 7738532 * 2 ^ 59
def prefixEnd_7738532 : Nat := 4983230072969 + 3 ^ 40 * 7738532 * 2
def baseEnd_7738532 : Nat := 3973586476199022191661145

theorem tailTrace_7738532 : CollatzResearch.WordTrace tailWord_7738532 prefixEnd_7738532 3973586476199022191661145 := by
  unfold tailWord_7738532
  simp only [CollatzResearch.WordTrace]
  refine ⟨141123724800313837444944925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188164966400418449926593233 141123724800313837444944925)
  ·
    refine ⟨52921396800117689041854347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141123724800313837444944925 52921396800117689041854347)
    ·
      refine ⟨79382095200176533562781521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52921396800117689041854347 79382095200176533562781521)
      ·
        refine ⟨59536571400132400172086141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79382095200176533562781521 59536571400132400172086141)
        ·
          refine ⟨22326214275049650064532303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59536571400132400172086141 22326214275049650064532303)
          ·
            refine ⟨33489321412574475096798455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22326214275049650064532303 33489321412574475096798455)
            ·
              refine ⟨50233982118861712645197683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33489321412574475096798455 50233982118861712645197683)
              ·
                refine ⟨75350973178292568967796525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50233982118861712645197683 75350973178292568967796525)
                ·
                  refine ⟨28256614941859713362923697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75350973178292568967796525 28256614941859713362923697)
                  ·
                    refine ⟨21192461206394785022192773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28256614941859713362923697 21192461206394785022192773)
                    ·
                      refine ⟨3973586476199022191661145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21192461206394785022192773 3973586476199022191661145)
                      ·
                        rfl

theorem cell23_7738532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_7738532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738532 prefixEnd_7738532 := by exact prefixLift 7738532
  have htrace : WordTrace (prefixWord ++ tailWord_7738532) baseStart_7738532 baseEnd_7738532 := by
    simpa [prefixWord, tailWord_7738532, baseEnd_7738532] using wordTrace_append hprefix tailTrace_7738532
  have hstable : (prefixWord ++ tailWord_7738532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738532).length < 2 ^ (prefixWord ++ tailWord_7738532).sum := by decide
  have hdescent : baseEnd_7738532 < baseStart_7738532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738553 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7738553 : Nat := 118140960795 + 7738553 * 2 ^ 59
def prefixEnd_7738553 : Nat := 4983230072969 + 3 ^ 40 * 7738553 * 2
def baseEnd_7738553 : Nat := 3973597259292766609498549

theorem tailTrace_7738553 : CollatzResearch.WordTrace tailWord_7738553 prefixEnd_7738553 3973597259292766609498549 := by
  unfold tailWord_7738553
  simp only [CollatzResearch.WordTrace]
  refine ⟨282248215533551595476404313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188165477022367730317602875 282248215533551595476404313)
  ·
    refine ⟨211686161650163696607303235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282248215533551595476404313 211686161650163696607303235)
    ·
      refine ⟨317529242475245544910954853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211686161650163696607303235 317529242475245544910954853)
      ·
        refine ⟨59536732964108539670804035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317529242475245544910954853 59536732964108539670804035)
        ·
          refine ⟨89305099446162809506206053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59536732964108539670804035 89305099446162809506206053)
          ·
            refine ⟨16744706146155526782413635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89305099446162809506206053 16744706146155526782413635)
            ·
              refine ⟨25117059219233290173620453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16744706146155526782413635 25117059219233290173620453)
              ·
                refine ⟨4709448603606241907553835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25117059219233290173620453 4709448603606241907553835)
                ·
                  refine ⟨7064172905409362861330753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709448603606241907553835 7064172905409362861330753)
                  ·
                    refine ⟨5298129679057022145998065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7064172905409362861330753 5298129679057022145998065)
                    ·
                      refine ⟨3973597259292766609498549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298129679057022145998065 3973597259292766609498549)
                      ·
                        rfl

theorem cell23_7738553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7738553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738553 prefixEnd_7738553 := by exact prefixLift 7738553
  have htrace : WordTrace (prefixWord ++ tailWord_7738553) baseStart_7738553 baseEnd_7738553 := by
    simpa [prefixWord, tailWord_7738553, baseEnd_7738553] using wordTrace_append hprefix tailTrace_7738553
  have hstable : (prefixWord ++ tailWord_7738553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738553).length < 2 ^ (prefixWord ++ tailWord_7738553).sum := by decide
  have hdescent : baseEnd_7738553 < baseStart_7738553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738565 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_7738565 : Nat := 118140960795 + 7738565 * 2 ^ 59
def prefixEnd_7738565 : Nat := 4983230072969 + 3 ^ 40 * 7738565 * 2
def baseEnd_7738565 : Nat := 3973603421060620562548493

theorem tailTrace_7738565 : CollatzResearch.WordTrace tailWord_7738565 prefixEnd_7738565 3973603421060620562548493 := by
  unfold tailWord_7738565
  simp only [CollatzResearch.WordTrace]
  refine ⟨282248653209508121525841149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188165768806338747683894099 282248653209508121525841149)
  ·
    refine ⟨105843244953565545572190431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282248653209508121525841149 105843244953565545572190431)
    ·
      refine ⟨158764867430348318358285647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105843244953565545572190431 158764867430348318358285647)
      ·
        refine ⟨238147301145522477537428471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158764867430348318358285647 238147301145522477537428471)
        ·
          refine ⟨357220951718283716306142707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238147301145522477537428471 357220951718283716306142707)
          ·
            refine ⟨535831427577425574459214061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357220951718283716306142707 535831427577425574459214061)
            ·
              refine ⟨200936785341534590422205273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535831427577425574459214061 200936785341534590422205273)
              ·
                refine ⟨150702589006150942816653955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200936785341534590422205273 150702589006150942816653955)
                ·
                  refine ⟨226053883509226414224980933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150702589006150942816653955 226053883509226414224980933)
                  ·
                    refine ⟨42385103157979952667183925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226053883509226414224980933 42385103157979952667183925)
                    ·
                      refine ⟨3973603421060620562548493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42385103157979952667183925 3973603421060620562548493)
                      ·
                        rfl

theorem cell23_7738565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_7738565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738565 prefixEnd_7738565 := by exact prefixLift 7738565
  have htrace : WordTrace (prefixWord ++ tailWord_7738565) baseStart_7738565 baseEnd_7738565 := by
    simpa [prefixWord, tailWord_7738565, baseEnd_7738565] using wordTrace_append hprefix tailTrace_7738565
  have hstable : (prefixWord ++ tailWord_7738565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738565).length < 2 ^ (prefixWord ++ tailWord_7738565).sum := by decide
  have hdescent : baseEnd_7738565 < baseStart_7738565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738585 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 8]
def baseStart_7738585 : Nat := 118140960795 + 7738585 * 2 ^ 59
def prefixEnd_7738585 : Nat := 4983230072969 + 3 ^ 40 * 7738585 * 2
def baseEnd_7738585 : Nat := 1324537896891236828099467

theorem tailTrace_7738585 : CollatzResearch.WordTrace tailWord_7738585 prefixEnd_7738585 1324537896891236828099467 := by
  unfold tailWord_7738585
  simp only [CollatzResearch.WordTrace]
  refine ⟨282249382669435664941569209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188166255112957109961046139 282249382669435664941569209)
  ·
    refine ⟨211687037002076748706176907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282249382669435664941569209 211687037002076748706176907)
    ·
      refine ⟨317530555503115123059265361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211687037002076748706176907 317530555503115123059265361)
      ·
        refine ⟨238147916627336342294449021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317530555503115123059265361 238147916627336342294449021)
        ·
          refine ⟨89305468735251128360418383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238147916627336342294449021 89305468735251128360418383)
          ·
            refine ⟨133958203102876692540627575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89305468735251128360418383 133958203102876692540627575)
            ·
              refine ⟨200937304654315038810941363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133958203102876692540627575 200937304654315038810941363)
              ·
                refine ⟨301405956981472558216412045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200937304654315038810941363 301405956981472558216412045)
                ·
                  refine ⟨113027233868052209331154517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301405956981472558216412045 113027233868052209331154517)
                  ·
                    refine ⟨1324537896891236828099467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113027233868052209331154517 1324537896891236828099467)
                    ·
                      rfl

theorem cell23_7738585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 8].length) (baseStart_7738585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738585 prefixEnd_7738585 := by exact prefixLift 7738585
  have htrace : WordTrace (prefixWord ++ tailWord_7738585) baseStart_7738585 baseEnd_7738585 := by
    simpa [prefixWord, tailWord_7738585, baseEnd_7738585] using wordTrace_append hprefix tailTrace_7738585
  have hstable : (prefixWord ++ tailWord_7738585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738585).length < 2 ^ (prefixWord ++ tailWord_7738585).sum := by decide
  have hdescent : baseEnd_7738585 < baseStart_7738585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738602 : List Nat := [3, 1, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_7738602 : Nat := 118140960795 + 7738602 * 2 ^ 59
def prefixEnd_7738602 : Nat := 4983230072969 + 3 ^ 40 * 7738602 * 2
def baseEnd_7738602 : Nat := 1324540806614945639261941

theorem tailTrace_7738602 : CollatzResearch.WordTrace tailWord_7738602 prefixEnd_7738602 1324540806614945639261941 := by
  unfold tailWord_7738602
  simp only [CollatzResearch.WordTrace]
  refine ⟨70562500677593519211234515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188166668473582717896625373 70562500677593519211234515)
  ·
    refine ⟨105843751016390278816851773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70562500677593519211234515 105843751016390278816851773)
    ·
      refine ⟨39691406631146354556319415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105843751016390278816851773 39691406631146354556319415)
      ·
        refine ⟨59537109946719531834479123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39691406631146354556319415 59537109946719531834479123)
        ·
          refine ⟨89305664920079297751718685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59537109946719531834479123 89305664920079297751718685)
          ·
            refine ⟨33489624345029736656894507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89305664920079297751718685 33489624345029736656894507)
            ·
              refine ⟨50234436517544604985341761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33489624345029736656894507 50234436517544604985341761)
              ·
                refine ⟨37675827388158453739006321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50234436517544604985341761 37675827388158453739006321)
                ·
                  refine ⟨28256870541118840304254741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37675827388158453739006321 28256870541118840304254741)
                  ·
                    refine ⟨1324540806614945639261941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28256870541118840304254741 1324540806614945639261941)
                    ·
                      rfl

theorem cell23_7738602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_7738602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738602 prefixEnd_7738602 := by exact prefixLift 7738602
  have htrace : WordTrace (prefixWord ++ tailWord_7738602) baseStart_7738602 baseEnd_7738602 := by
    simpa [prefixWord, tailWord_7738602, baseEnd_7738602] using wordTrace_append hprefix tailTrace_7738602
  have hstable : (prefixWord ++ tailWord_7738602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738602).length < 2 ^ (prefixWord ++ tailWord_7738602).sum := by decide
  have hdescent : baseEnd_7738602 < baseStart_7738602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738615 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 11]
def baseStart_7738615 : Nat := 118140960795 + 7738615 * 2 ^ 59
def prefixEnd_7738615 : Nat := 4983230072969 + 3 ^ 40 * 7738615 * 2
def baseEnd_7738615 : Nat := 441514343899260596324807

theorem tailTrace_7738615 : CollatzResearch.WordTrace tailWord_7738615 prefixEnd_7738615 441514343899260596324807 := by
  unfold tailWord_7738615
  simp only [CollatzResearch.WordTrace]
  refine ⟨282250476859326980065161299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188166984572884653376774199 282250476859326980065161299)
  ·
    refine ⟨423375715288990470097741949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282250476859326980065161299 423375715288990470097741949)
    ·
      refine ⟨158765893233371426286653231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423375715288990470097741949 158765893233371426286653231)
      ·
        refine ⟨238148839850057139429979847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158765893233371426286653231 238148839850057139429979847)
        ·
          refine ⟨357223259775085709144969771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238148839850057139429979847 357223259775085709144969771)
          ·
            refine ⟨535834889662628563717454657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357223259775085709144969771 535834889662628563717454657)
            ·
              refine ⟨401876167246971422788090993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535834889662628563717454657 401876167246971422788090993)
              ·
                refine ⟨301407125435228567091068245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401876167246971422788090993 301407125435228567091068245)
                ·
                  refine ⟨441514343899260596324807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 301407125435228567091068245 441514343899260596324807)
                  ·
                    rfl

theorem cell23_7738615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 11].length) (baseStart_7738615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738615 prefixEnd_7738615 := by exact prefixLift 7738615
  have htrace : WordTrace (prefixWord ++ tailWord_7738615) baseStart_7738615 baseEnd_7738615 := by
    simpa [prefixWord, tailWord_7738615, baseEnd_7738615] using wordTrace_append hprefix tailTrace_7738615
  have hstable : (prefixWord ++ tailWord_7738615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738615).length < 2 ^ (prefixWord ++ tailWord_7738615).sum := by decide
  have hdescent : baseEnd_7738615 < baseStart_7738615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738666 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_7738666 : Nat := 118140960795 + 7738666 * 2 ^ 59
def prefixEnd_7738666 : Nat := 4983230072969 + 3 ^ 40 * 7738666 * 2
def baseEnd_7738666 : Nat := 441517253622969407487281

theorem tailTrace_7738666 : CollatzResearch.WordTrace tailWord_7738666 prefixEnd_7738666 441517253622969407487281 := by
  unfold tailWord_7738666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70563084245535553943816963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188168224654761477183511901 70563084245535553943816963)
  ·
    refine ⟨105844626368303330915725445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70563084245535553943816963 105844626368303330915725445)
    ·
      refine ⟨19845867444056874546698521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105844626368303330915725445 19845867444056874546698521)
      ·
        refine ⟨14884400583042655910023891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19845867444056874546698521 14884400583042655910023891)
        ·
          refine ⟨22326600874563983865035837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14884400583042655910023891 22326600874563983865035837)
          ·
            refine ⟨8372475327961493949388439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22326600874563983865035837 8372475327961493949388439)
            ·
              refine ⟨12558712991942240924082659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372475327961493949388439 12558712991942240924082659)
              ·
                refine ⟨18838069487913361386123989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12558712991942240924082659 18838069487913361386123989)
                ·
                  refine ⟨441517253622969407487281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18838069487913361386123989 441517253622969407487281)
                  ·
                    rfl

theorem cell23_7738666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_7738666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738666 prefixEnd_7738666 := by exact prefixLift 7738666
  have htrace : WordTrace (prefixWord ++ tailWord_7738666) baseStart_7738666 baseEnd_7738666 := by
    simpa [prefixWord, tailWord_7738666, baseEnd_7738666] using wordTrace_append hprefix tailTrace_7738666
  have hstable : (prefixWord ++ tailWord_7738666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738666).length < 2 ^ (prefixWord ++ tailWord_7738666).sum := by decide
  have hdescent : baseEnd_7738666 < baseStart_7738666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738672 : List Nat := [2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_7738672 : Nat := 118140960795 + 7738672 * 2 ^ 59
def prefixEnd_7738672 : Nat := 4983230072969 + 3 ^ 40 * 7738672 * 2
def baseEnd_7738672 : Nat := 3973658363490651643910501

theorem tailTrace_7738672 : CollatzResearch.WordTrace tailWord_7738672 prefixEnd_7738672 3973658363490651643910501 := by
  unfold tailWord_7738672
  simp only [CollatzResearch.WordTrace]
  refine ⟨141126277910060239399993135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188168370546746985866657513 141126277910060239399993135)
  ·
    refine ⟨211689416865090359099989703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141126277910060239399993135 211689416865090359099989703)
    ·
      refine ⟨317534125297635538649984555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211689416865090359099989703 317534125297635538649984555)
      ·
        refine ⟨476301187946453307974976833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317534125297635538649984555 476301187946453307974976833)
        ·
          refine ⟨357225890959839980981232625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476301187946453307974976833 357225890959839980981232625)
          ·
            refine ⟨267919418219879985735924469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357225890959839980981232625 267919418219879985735924469)
            ·
              refine ⟨25117445458113748662742919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 267919418219879985735924469 25117445458113748662742919)
              ·
                refine ⟨37676168187170622994114379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25117445458113748662742919 37676168187170622994114379)
                ·
                  refine ⟨56514252280755934491171569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37676168187170622994114379 56514252280755934491171569)
                  ·
                    refine ⟨42385689210566950868378677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56514252280755934491171569 42385689210566950868378677)
                    ·
                      refine ⟨3973658363490651643910501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42385689210566950868378677 3973658363490651643910501)
                      ·
                        rfl

theorem cell23_7738672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_7738672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738672 prefixEnd_7738672 := by exact prefixLift 7738672
  have htrace : WordTrace (prefixWord ++ tailWord_7738672) baseStart_7738672 baseEnd_7738672 := by
    simpa [prefixWord, tailWord_7738672, baseEnd_7738672] using wordTrace_append hprefix tailTrace_7738672
  have hstable : (prefixWord ++ tailWord_7738672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738672).length < 2 ^ (prefixWord ++ tailWord_7738672).sum := by decide
  have hdescent : baseEnd_7738672 < baseStart_7738672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738712 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_7738712 : Nat := 118140960795 + 7738712 * 2 ^ 59
def prefixEnd_7738712 : Nat := 4983230072969 + 3 ^ 40 * 7738712 * 2
def baseEnd_7738712 : Nat := 3973678902716831487410317

theorem tailTrace_7738712 : CollatzResearch.WordTrace tailWord_7738712 prefixEnd_7738712 3973678902716831487410317 := by
  unfold tailWord_7738712
  simp only [CollatzResearch.WordTrace]
  refine ⟨141127007369987782815721195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188169343159983710420961593 141127007369987782815721195)
  ·
    refine ⟨211690511054981674223581793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141127007369987782815721195 211690511054981674223581793)
    ·
      refine ⟨158767883291236255667686345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211690511054981674223581793 158767883291236255667686345)
      ·
        refine ⟨119075912468427191750764759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158767883291236255667686345 119075912468427191750764759)
        ·
          refine ⟨178613868702640787626147139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119075912468427191750764759 178613868702640787626147139)
          ·
            refine ⟨267920803053961181439220709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178613868702640787626147139 267920803053961181439220709)
            ·
              refine ⟨50235150572617721519853883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267920803053961181439220709 50235150572617721519853883)
              ·
                refine ⟨75352725858926582279780825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50235150572617721519853883 75352725858926582279780825)
                ·
                  refine ⟨56514544394194936709835619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75352725858926582279780825 56514544394194936709835619)
                  ·
                    refine ⟨84771816591292405064753429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56514544394194936709835619 84771816591292405064753429)
                    ·
                      refine ⟨3973678902716831487410317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84771816591292405064753429 3973678902716831487410317)
                      ·
                        rfl

theorem cell23_7738712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_7738712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738712 prefixEnd_7738712 := by exact prefixLift 7738712
  have htrace : WordTrace (prefixWord ++ tailWord_7738712) baseStart_7738712 baseEnd_7738712 := by
    simpa [prefixWord, tailWord_7738712, baseEnd_7738712] using wordTrace_append hprefix tailTrace_7738712
  have hstable : (prefixWord ++ tailWord_7738712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738712).length < 2 ^ (prefixWord ++ tailWord_7738712).sum := by decide
  have hdescent : baseEnd_7738712 < baseStart_7738712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738769 : List Nat := [1, 2, 2, 1, 1, 1, 2, 7, 1, 5]
def baseStart_7738769 : Nat := 118140960795 + 7738769 * 2 ^ 59
def prefixEnd_7738769 : Nat := 4983230072969 + 3 ^ 40 * 7738769 * 2
def baseEnd_7738769 : Nat := 1324569390371379254799185

theorem tailTrace_7738769 : CollatzResearch.WordTrace tailWord_7738769 prefixEnd_7738769 1324569390371379254799185 := by
  unfold tailWord_7738769
  simp only [CollatzResearch.WordTrace]
  refine ⟨282256093700769064366267361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188170729133846042910844907 282256093700769064366267361)
  ·
    refine ⟨211692070275576798274700521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282256093700769064366267361 211692070275576798274700521)
    ·
      refine ⟨158769052706682598706025391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211692070275576798274700521 158769052706682598706025391)
      ·
        refine ⟨238153579060023898059038087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158769052706682598706025391 238153579060023898059038087)
        ·
          refine ⟨357230368590035847088557131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238153579060023898059038087 357230368590035847088557131)
          ·
            refine ⟨535845552885053770632835697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357230368590035847088557131 535845552885053770632835697)
            ·
              refine ⟨401884164663790327974626773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535845552885053770632835697 401884164663790327974626773)
              ·
                refine ⟨9419160109307585811905315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 401884164663790327974626773 9419160109307585811905315)
                ·
                  refine ⟨14128740163961378717857973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9419160109307585811905315 14128740163961378717857973)
                  ·
                    refine ⟨1324569390371379254799185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14128740163961378717857973 1324569390371379254799185)
                    ·
                      rfl

theorem cell23_7738769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 5].length) (baseStart_7738769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738769 prefixEnd_7738769 := by exact prefixLift 7738769
  have htrace : WordTrace (prefixWord ++ tailWord_7738769) baseStart_7738769 baseEnd_7738769 := by
    simpa [prefixWord, tailWord_7738769, baseEnd_7738769] using wordTrace_append hprefix tailTrace_7738769
  have hstable : (prefixWord ++ tailWord_7738769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738769).length < 2 ^ (prefixWord ++ tailWord_7738769).sum := by decide
  have hdescent : baseEnd_7738769 < baseStart_7738769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738783 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 3]
def baseStart_7738783 : Nat := 118140960795 + 7738783 * 2 ^ 59
def prefixEnd_7738783 : Nat := 4983230072969 + 3 ^ 40 * 7738783 * 2
def baseEnd_7738783 : Nat := 3973715359843300709622491

theorem tailTrace_7738783 : CollatzResearch.WordTrace tailWord_7738783 prefixEnd_7738783 3973715359843300709622491 := by
  unfold tailWord_7738783
  simp only [CollatzResearch.WordTrace]
  refine ⟨282256604322718344757277003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188171069548478896504851335 282256604322718344757277003)
  ·
    refine ⟨423384906484077517135915505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282256604322718344757277003 423384906484077517135915505)
    ·
      refine ⟨317538679863058137851936629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423384906484077517135915505 317538679863058137851936629)
      ·
        refine ⟨29769251237161700423619059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317538679863058137851936629 29769251237161700423619059)
        ·
          refine ⟨44653876855742550635428589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29769251237161700423619059 44653876855742550635428589)
          ·
            refine ⟨16745203820903456488285721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44653876855742550635428589 16745203820903456488285721)
            ·
              refine ⟨12558902865677592366214291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16745203820903456488285721 12558902865677592366214291)
              ·
                refine ⟨18838354298516388549321437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12558902865677592366214291 18838354298516388549321437)
                ·
                  refine ⟨7064382861943645705995539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18838354298516388549321437 7064382861943645705995539)
                  ·
                    refine ⟨10596574292915468558993309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7064382861943645705995539 10596574292915468558993309)
                    ·
                      refine ⟨3973715359843300709622491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10596574292915468558993309 3973715359843300709622491)
                      ·
                        rfl

theorem cell23_7738783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_7738783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738783 prefixEnd_7738783 := by exact prefixLift 7738783
  have htrace : WordTrace (prefixWord ++ tailWord_7738783) baseStart_7738783 baseEnd_7738783 := by
    simpa [prefixWord, tailWord_7738783, baseEnd_7738783] using wordTrace_append hprefix tailTrace_7738783
  have hstable : (prefixWord ++ tailWord_7738783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738783).length < 2 ^ (prefixWord ++ tailWord_7738783).sum := by decide
  have hdescent : baseEnd_7738783 < baseStart_7738783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738789 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_7738789 : Nat := 118140960795 + 7738789 * 2 ^ 59
def prefixEnd_7738789 : Nat := 4983230072969 + 3 ^ 40 * 7738789 * 2
def baseEnd_7738789 : Nat := 3973718440727227686147463

theorem tailTrace_7738789 : CollatzResearch.WordTrace tailWord_7738789 prefixEnd_7738789 3973718440727227686147463 := by
  unfold tailWord_7738789
  simp only [CollatzResearch.WordTrace]
  refine ⟨282256823160696607781995421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188171215440464405187996947 282256823160696607781995421)
  ·
    refine ⟨105846308685261227918248283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282256823160696607781995421 105846308685261227918248283)
    ·
      refine ⟨158769463027891841877372425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105846308685261227918248283 158769463027891841877372425)
      ·
        refine ⟨119077097270918881408029319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158769463027891841877372425 119077097270918881408029319)
        ·
          refine ⟨178615645906378322112043979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119077097270918881408029319 178615645906378322112043979)
          ·
            refine ⟨267923468859567483168065969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178615645906378322112043979 267923468859567483168065969)
            ·
              refine ⟨200942601644675612376049477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267923468859567483168065969 200942601644675612376049477)
              ·
                refine ⟨37676737808376677320509277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200942601644675612376049477 37676737808376677320509277)
                ·
                  refine ⟨14128776678141253995190979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37676737808376677320509277 14128776678141253995190979)
                  ·
                    refine ⟨21193165017211880992786469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14128776678141253995190979 21193165017211880992786469)
                    ·
                      refine ⟨3973718440727227686147463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21193165017211880992786469 3973718440727227686147463)
                      ·
                        rfl

theorem cell23_7738789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_7738789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738789 prefixEnd_7738789 := by exact prefixLift 7738789
  have htrace : WordTrace (prefixWord ++ tailWord_7738789) baseStart_7738789 baseEnd_7738789 := by
    simpa [prefixWord, tailWord_7738789, baseEnd_7738789] using wordTrace_append hprefix tailTrace_7738789
  have hstable : (prefixWord ++ tailWord_7738789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738789).length < 2 ^ (prefixWord ++ tailWord_7738789).sum := by decide
  have hdescent : baseEnd_7738789 < baseStart_7738789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738819 : List Nat := [1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4]
def baseStart_7738819 : Nat := 118140960795 + 7738819 * 2 ^ 59
def prefixEnd_7738819 : Nat := 4983230072969 + 3 ^ 40 * 7738819 * 2
def baseEnd_7738819 : Nat := 3973733845146862568772325

theorem tailTrace_7738819 : CollatzResearch.WordTrace tailWord_7738819 prefixEnd_7738819 3973733845146862568772325 := by
  unfold tailWord_7738819
  simp only [CollatzResearch.WordTrace]
  refine ⟨282257917350587922905587511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188171944900391948603725007 282257917350587922905587511)
  ·
    refine ⟨423386876025881884358381267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282257917350587922905587511 423386876025881884358381267)
    ·
      refine ⟨635080314038822826537571901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423386876025881884358381267 635080314038822826537571901)
      ·
        refine ⟨238155117764558559951589463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635080314038822826537571901 238155117764558559951589463)
        ·
          refine ⟨357232676646837839927384195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238155117764558559951589463 357232676646837839927384195)
          ·
            refine ⟨535849014970256759891076293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357232676646837839927384195 535849014970256759891076293)
            ·
              refine ⟨100471690306923142479576805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 535849014970256759891076293 100471690306923142479576805)
              ·
                refine ⟨18838441932548089214920651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100471690306923142479576805 18838441932548089214920651)
                ·
                  refine ⟨28257662898822133822380977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18838441932548089214920651 28257662898822133822380977)
                  ·
                    refine ⟨21193247174116600366785733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28257662898822133822380977 21193247174116600366785733)
                    ·
                      refine ⟨3973733845146862568772325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21193247174116600366785733 3973733845146862568772325)
                      ·
                        rfl

theorem cell23_7738819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_7738819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738819 prefixEnd_7738819 := by exact prefixLift 7738819
  have htrace : WordTrace (prefixWord ++ tailWord_7738819) baseStart_7738819 baseEnd_7738819 := by
    simpa [prefixWord, tailWord_7738819, baseEnd_7738819] using wordTrace_append hprefix tailTrace_7738819
  have hstable : (prefixWord ++ tailWord_7738819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738819).length < 2 ^ (prefixWord ++ tailWord_7738819).sum := by decide
  have hdescent : baseEnd_7738819 < baseStart_7738819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738826 : List Nat := [3, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_7738826 : Nat := 118140960795 + 7738826 * 2 ^ 59
def prefixEnd_7738826 : Nat := 4983230072969 + 3 ^ 40 * 7738826 * 2
def baseEnd_7738826 : Nat := 3973737439511444041384793

theorem tailTrace_7738826 : CollatzResearch.WordTrace tailWord_7738826 prefixEnd_7738826 3973737439511444041384793 := by
  unfold tailWord_7738826
  simp only [CollatzResearch.WordTrace]
  refine ⟨70564543165390640775273083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188172115107708375400728221 70564543165390640775273083)
  ·
    refine ⟨105846814748085961162909625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70564543165390640775273083 105846814748085961162909625)
    ·
      refine ⟨79385111061064470872182219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105846814748085961162909625 79385111061064470872182219)
      ·
        refine ⟨119077666591596706308273329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79385111061064470872182219 119077666591596706308273329)
        ·
          refine ⟨89308249943697529731204997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119077666591596706308273329 89308249943697529731204997)
          ·
            refine ⟨16745296864443286824600937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89308249943697529731204997 16745296864443286824600937)
            ·
              refine ⟨12558972648332465118450703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16745296864443286824600937 12558972648332465118450703)
              ·
                refine ⟨18838458972498697677676055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12558972648332465118450703 18838458972498697677676055)
                ·
                  refine ⟨28257688458748046516514083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18838458972498697677676055 28257688458748046516514083)
                  ·
                    refine ⟨42386532688122069774771125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28257688458748046516514083 42386532688122069774771125)
                    ·
                      refine ⟨3973737439511444041384793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42386532688122069774771125 3973737439511444041384793)
                      ·
                        rfl

theorem cell23_7738826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_7738826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738826 prefixEnd_7738826 := by exact prefixLift 7738826
  have htrace : WordTrace (prefixWord ++ tailWord_7738826) baseStart_7738826 baseEnd_7738826 := by
    simpa [prefixWord, tailWord_7738826, baseEnd_7738826] using wordTrace_append hprefix tailTrace_7738826
  have hstable : (prefixWord ++ tailWord_7738826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738826).length < 2 ^ (prefixWord ++ tailWord_7738826).sum := by decide
  have hdescent : baseEnd_7738826 < baseStart_7738826 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738840 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 1, 2, 2]
def baseStart_7738840 : Nat := 118140960795 + 7738840 * 2 ^ 59
def prefixEnd_7738840 : Nat := 4983230072969 + 3 ^ 40 * 7738840 * 2
def baseEnd_7738840 : Nat := 3973744628240606986609729

theorem tailTrace_7738840 : CollatzResearch.WordTrace tailWord_7738840 prefixEnd_7738840 3973744628240606986609729 := by
  unfold tailWord_7738840
  simp only [CollatzResearch.WordTrace]
  refine ⟨141129341641755921746050987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188172455522341228994734649 141129341641755921746050987)
  ·
    refine ⟨211694012462633882619076481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141129341641755921746050987 211694012462633882619076481)
    ·
      refine ⟨158770509346975411964307361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211694012462633882619076481 158770509346975411964307361)
      ·
        refine ⟨119077882010231558973230521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158770509346975411964307361 119077882010231558973230521)
        ·
          refine ⟨89308411507673669229922891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119077882010231558973230521 89308411507673669229922891)
          ·
            refine ⟨133962617261510503844884337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89308411507673669229922891 133962617261510503844884337)
            ·
              refine ⟨100471962946132877883663253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133962617261510503844884337 100471962946132877883663253)
              ·
                refine ⟨4709623263099978650796715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100471962946132877883663253 4709623263099978650796715)
                ·
                  refine ⟨7064434894649967976195073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709623263099978650796715 7064434894649967976195073)
                  ·
                    refine ⟨5298326170987475982146305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7064434894649967976195073 5298326170987475982146305)
                    ·
                      refine ⟨3973744628240606986609729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298326170987475982146305 3973744628240606986609729)
                      ·
                        rfl

theorem cell23_7738840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_7738840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738840 prefixEnd_7738840 := by exact prefixLift 7738840
  have htrace : WordTrace (prefixWord ++ tailWord_7738840) baseStart_7738840 baseEnd_7738840 := by
    simpa [prefixWord, tailWord_7738840, baseEnd_7738840] using wordTrace_append hprefix tailTrace_7738840
  have hstable : (prefixWord ++ tailWord_7738840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738840).length < 2 ^ (prefixWord ++ tailWord_7738840).sum := by decide
  have hdescent : baseEnd_7738840 < baseStart_7738840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738856 : List Nat := [2, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7738856 : Nat := 118140960795 + 7738856 * 2 ^ 59
def prefixEnd_7738856 : Nat := 4983230072969 + 3 ^ 40 * 7738856 * 2
def baseEnd_7738856 : Nat := 3973752843931078924009655

theorem tailTrace_7738856 : CollatzResearch.WordTrace tailWord_7738856 prefixEnd_7738856 3973752843931078924009655 := by
  unfold tailWord_7738856
  simp only [CollatzResearch.WordTrace]
  refine ⟨141129633425726939112342211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188172844567635918816456281 141129633425726939112342211)
  ·
    refine ⟨211694450138590408668513317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141129633425726939112342211 211694450138590408668513317)
    ·
      refine ⟨39692709400985701625346247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211694450138590408668513317 39692709400985701625346247)
      ·
        refine ⟨59539064101478552438019371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39692709400985701625346247 59539064101478552438019371)
        ·
          refine ⟨89308596152217828657029057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59539064101478552438019371 89308596152217828657029057)
          ·
            refine ⟨66981447114163371492771793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89308596152217828657029057 66981447114163371492771793)
            ·
              refine ⟨50236085335622528619578845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66981447114163371492771793 50236085335622528619578845)
              ·
                refine ⟨18838532000858448232342067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50236085335622528619578845 18838532000858448232342067)
                ·
                  refine ⟨28257798001287672348513101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18838532000858448232342067 28257798001287672348513101)
                  ·
                    refine ⟨10596674250482877130692413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28257798001287672348513101 10596674250482877130692413)
                    ·
                      refine ⟨3973752843931078924009655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10596674250482877130692413 3973752843931078924009655)
                      ·
                        rfl

theorem cell23_7738856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7738856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738856 prefixEnd_7738856 := by exact prefixLift 7738856
  have htrace : WordTrace (prefixWord ++ tailWord_7738856) baseStart_7738856 baseEnd_7738856 := by
    simpa [prefixWord, tailWord_7738856, baseEnd_7738856] using wordTrace_append hprefix tailTrace_7738856
  have hstable : (prefixWord ++ tailWord_7738856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738856).length < 2 ^ (prefixWord ++ tailWord_7738856).sum := by decide
  have hdescent : baseEnd_7738856 < baseStart_7738856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738889 : List Nat := [1, 2, 1, 1, 3, 1, 4, 2, 2, 6]
def baseStart_7738889 : Nat := 118140960795 + 7738889 * 2 ^ 59
def prefixEnd_7738889 : Nat := 4983230072969 + 3 ^ 40 * 7738889 * 2
def baseEnd_7738889 : Nat := 1324589929597559098299001

theorem tailTrace_7738889 : CollatzResearch.WordTrace tailWord_7738889 prefixEnd_7738889 1324589929597559098299001 := by
  unfold tailWord_7738889
  simp only [CollatzResearch.WordTrace]
  refine ⟨282260470460334324860635721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188173646973556216573757147 282260470460334324860635721)
  ·
    refine ⟨211695352845250743645476791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282260470460334324860635721 211695352845250743645476791)
    ·
      refine ⟨317543029267876115468215187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211695352845250743645476791 317543029267876115468215187)
      ·
        refine ⟨476314543901814173202322781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317543029267876115468215187 476314543901814173202322781)
        ·
          refine ⟨178617953963180314950871043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476314543901814173202322781 178617953963180314950871043)
          ·
            refine ⟨267926930944770472426306565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178617953963180314950871043 267926930944770472426306565)
            ·
              refine ⟨50236299552144463579932481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267926930944770472426306565 50236299552144463579932481)
              ·
                refine ⟨37677224664108347684949361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50236299552144463579932481 37677224664108347684949361)
                ·
                  refine ⟨28257918498081260763712021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37677224664108347684949361 28257918498081260763712021)
                  ·
                    refine ⟨1324589929597559098299001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28257918498081260763712021 1324589929597559098299001)
                    ·
                      rfl

theorem cell23_7738889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 6].length) (baseStart_7738889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738889 prefixEnd_7738889 := by exact prefixLift 7738889
  have htrace : WordTrace (prefixWord ++ tailWord_7738889) baseStart_7738889 baseEnd_7738889 := by
    simpa [prefixWord, tailWord_7738889, baseEnd_7738889] using wordTrace_append hprefix tailTrace_7738889
  have hstable : (prefixWord ++ tailWord_7738889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738889).length < 2 ^ (prefixWord ++ tailWord_7738889).sum := by decide
  have hdescent : baseEnd_7738889 < baseStart_7738889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738890 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_7738890 : Nat := 118140960795 + 7738890 * 2 ^ 59
def prefixEnd_7738890 : Nat := 4983230072969 + 3 ^ 40 * 7738890 * 2
def baseEnd_7738890 : Nat := 3973770302273331790984499

theorem tailTrace_7738890 : CollatzResearch.WordTrace tailWord_7738890 prefixEnd_7738890 3973770302273331790984499 := by
  unfold tailWord_7738890
  simp only [CollatzResearch.WordTrace]
  refine ⟨70565126733332675507855531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188173671288887134687614749 70565126733332675507855531)
  ·
    refine ⟨105847690099999013261783297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70565126733332675507855531 105847690099999013261783297)
    ·
      refine ⟨79385767574999259946337473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105847690099999013261783297 79385767574999259946337473)
      ·
        refine ⟨59539325681249444959753105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79385767574999259946337473 59539325681249444959753105)
        ·
          refine ⟨44654494260937083719814829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59539325681249444959753105 44654494260937083719814829)
          ·
            refine ⟨16745435347851406394930561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44654494260937083719814829 16745435347851406394930561)
            ·
              refine ⟨12559076510888554796197921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16745435347851406394930561 12559076510888554796197921)
              ·
                refine ⟨9419307383166416097148441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12559076510888554796197921 9419307383166416097148441)
                ·
                  refine ⟨7064480537374812072861331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9419307383166416097148441 7064480537374812072861331)
                  ·
                    refine ⟨10596720806062218109291997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7064480537374812072861331 10596720806062218109291997)
                    ·
                      refine ⟨3973770302273331790984499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10596720806062218109291997 3973770302273331790984499)
                      ·
                        rfl

theorem cell23_7738890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_7738890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738890 prefixEnd_7738890 := by exact prefixLift 7738890
  have htrace : WordTrace (prefixWord ++ tailWord_7738890) baseStart_7738890 baseEnd_7738890 := by
    simpa [prefixWord, tailWord_7738890, baseEnd_7738890] using wordTrace_append hprefix tailTrace_7738890
  have hstable : (prefixWord ++ tailWord_7738890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738890).length < 2 ^ (prefixWord ++ tailWord_7738890).sum := by decide
  have hdescent : baseEnd_7738890 < baseStart_7738890 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738891 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 1, 2, 2]
def baseStart_7738891 : Nat := 118140960795 + 7738891 * 2 ^ 59
def prefixEnd_7738891 : Nat := 4983230072969 + 3 ^ 40 * 7738891 * 2
def baseEnd_7738891 : Nat := 3973770815753986287071995

theorem tailTrace_7738891 : CollatzResearch.WordTrace tailWord_7738891 prefixEnd_7738891 3973770815753986287071995 := by
  unfold tailWord_7738891
  simp only [CollatzResearch.WordTrace]
  refine ⟨282260543406327079202208527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188173695604218052801472351 282260543406327079202208527)
  ·
    refine ⟨423390815109490618803312791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282260543406327079202208527 423390815109490618803312791)
    ·
      refine ⟨635086222664235928204969187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423390815109490618803312791 635086222664235928204969187)
      ·
        refine ⟨952629333996353892307453781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635086222664235928204969187 952629333996353892307453781)
        ·
          refine ⟨5581812503884886087738987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 952629333996353892307453781 5581812503884886087738987)
          ·
            refine ⟨8372718755827329131608481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5581812503884886087738987 8372718755827329131608481)
            ·
              refine ⟨6279539066870496848706361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8372718755827329131608481 6279539066870496848706361)
              ·
                refine ⟨4709654300152872636529771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6279539066870496848706361 4709654300152872636529771)
                ·
                  refine ⟨7064481450229308954794657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4709654300152872636529771 7064481450229308954794657)
                  ·
                    refine ⟨5298361087671981716095993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7064481450229308954794657 5298361087671981716095993)
                    ·
                      refine ⟨3973770815753986287071995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298361087671981716095993 3973770815753986287071995)
                      ·
                        rfl

theorem cell23_7738891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 1, 2, 2].length) (baseStart_7738891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738891 prefixEnd_7738891 := by exact prefixLift 7738891
  have htrace : WordTrace (prefixWord ++ tailWord_7738891) baseStart_7738891 baseEnd_7738891 := by
    simpa [prefixWord, tailWord_7738891, baseEnd_7738891] using wordTrace_append hprefix tailTrace_7738891
  have hstable : (prefixWord ++ tailWord_7738891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738891).length < 2 ^ (prefixWord ++ tailWord_7738891).sum := by decide
  have hdescent : baseEnd_7738891 < baseStart_7738891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738913 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 1, 4, 2]
def baseStart_7738913 : Nat := 118140960795 + 7738913 * 2 ^ 59
def prefixEnd_7738913 : Nat := 4983230072969 + 3 ^ 40 * 7738913 * 2
def baseEnd_7738913 : Nat := 3973782112328385200996893

theorem tailTrace_7738913 : CollatzResearch.WordTrace tailWord_7738913 prefixEnd_7738913 3973782112328385200996893 := by
  unfold tailWord_7738913
  simp only [CollatzResearch.WordTrace]
  refine ⟨282261345812247376959509393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188174230541498251306339595 282261345812247376959509393)
  ·
    refine ⟨211696009359185532719632045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282261345812247376959509393 211696009359185532719632045)
    ·
      refine ⟨79386003509694574769862017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211696009359185532719632045 79386003509694574769862017)
      ·
        refine ⟨59539502632270931077396513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79386003509694574769862017 59539502632270931077396513)
        ·
          refine ⟨44654626974203198308047385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59539502632270931077396513 44654626974203198308047385)
          ·
            refine ⟨33490970230652398731035539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44654626974203198308047385 33490970230652398731035539)
            ·
              refine ⟨50236455345978598096553309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33490970230652398731035539 50236455345978598096553309)
              ·
                refine ⟨18838670754741974286207491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50236455345978598096553309 18838670754741974286207491)
                ·
                  refine ⟨28258006132112961429311237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18838670754741974286207491 28258006132112961429311237)
                  ·
                    refine ⟨5298376149771180267995857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28258006132112961429311237 5298376149771180267995857)
                    ·
                      refine ⟨3973782112328385200996893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298376149771180267995857 3973782112328385200996893)
                      ·
                        rfl

theorem cell23_7738913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_7738913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738913 prefixEnd_7738913 := by exact prefixLift 7738913
  have htrace : WordTrace (prefixWord ++ tailWord_7738913) baseStart_7738913 baseEnd_7738913 := by
    simpa [prefixWord, tailWord_7738913, baseEnd_7738913] using wordTrace_append hprefix tailTrace_7738913
  have hstable : (prefixWord ++ tailWord_7738913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738913).length < 2 ^ (prefixWord ++ tailWord_7738913).sum := by decide
  have hdescent : baseEnd_7738913 < baseStart_7738913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738929 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 7]
def baseStart_7738929 : Nat := 118140960795 + 7738929 * 2 ^ 59
def prefixEnd_7738929 : Nat := 4983230072969 + 3 ^ 40 * 7738929 * 2
def baseEnd_7738929 : Nat := 3973790328018857138396819

theorem tailTrace_7738929 : CollatzResearch.WordTrace tailWord_7738929 prefixEnd_7738929 3973790328018857138396819 := by
  unfold tailWord_7738929
  simp only [CollatzResearch.WordTrace]
  refine ⟨282261929380189411692091841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188174619586792941128061227 282261929380189411692091841)
  ·
    refine ⟨211696447035142058769068881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282261929380189411692091841 211696447035142058769068881)
    ·
      refine ⟨158772335276356544076801661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211696447035142058769068881 158772335276356544076801661)
      ·
        refine ⟨59539625728633704028800623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158772335276356544076801661 59539625728633704028800623)
        ·
          refine ⟨89309438592950556043200935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59539625728633704028800623 89309438592950556043200935)
          ·
            refine ⟨133964157889425834064801403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89309438592950556043200935 133964157889425834064801403)
            ·
              refine ⟨200946236834138751097202105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133964157889425834064801403 200946236834138751097202105)
              ·
                refine ⟨150709677625604063322901579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200946236834138751097202105 150709677625604063322901579)
                ·
                  refine ⟨226064516438406094984352369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150709677625604063322901579 226064516438406094984352369)
                  ·
                    refine ⟨169548387328804571238264277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 226064516438406094984352369 169548387328804571238264277)
                    ·
                      refine ⟨3973790328018857138396819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169548387328804571238264277 3973790328018857138396819)
                      ·
                        rfl

theorem cell23_7738929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_7738929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738929 prefixEnd_7738929 := by exact prefixLift 7738929
  have htrace : WordTrace (prefixWord ++ tailWord_7738929) baseStart_7738929 baseEnd_7738929 := by
    simpa [prefixWord, tailWord_7738929, baseEnd_7738929] using wordTrace_append hprefix tailTrace_7738929
  have hstable : (prefixWord ++ tailWord_7738929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738929).length < 2 ^ (prefixWord ++ tailWord_7738929).sum := by decide
  have hdescent : baseEnd_7738929 < baseStart_7738929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7738959 : List Nat := [1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_7738959 : Nat := 118140960795 + 7738959 * 2 ^ 59
def prefixEnd_7738959 : Nat := 4983230072969 + 3 ^ 40 * 7738959 * 2
def baseEnd_7738959 : Nat := 3973805732438492021021681

theorem tailTrace_7738959 : CollatzResearch.WordTrace tailWord_7738959 prefixEnd_7738959 3973805732438492021021681 := by
  unfold tailWord_7738959
  simp only [CollatzResearch.WordTrace]
  refine ⟨282263023570080726815683931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188175349046720484543789287 282263023570080726815683931)
  ·
    refine ⟨423394535355121090223525897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282263023570080726815683931 423394535355121090223525897)
    ·
      refine ⟨317545901516340817667644423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423394535355121090223525897 317545901516340817667644423)
      ·
        refine ⟨476318852274511226501466635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317545901516340817667644423 476318852274511226501466635)
        ·
          refine ⟨714478278411766839752199953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476318852274511226501466635 714478278411766839752199953)
          ·
            refine ⟨535858708808825129814149965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714478278411766839752199953 535858708808825129814149965)
            ·
              refine ⟨200947015803309423680306237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 535858708808825129814149965 200947015803309423680306237)
              ·
                refine ⟨75355130926241033880114839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200947015803309423680306237 75355130926241033880114839)
                ·
                  refine ⟨113032696389361550820172259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75355130926241033880114839 113032696389361550820172259)
                  ·
                    refine ⟨169549044584042326230258389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113032696389361550820172259 169549044584042326230258389)
                    ·
                      refine ⟨3973805732438492021021681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169549044584042326230258389 3973805732438492021021681)
                      ·
                        rfl

theorem cell23_7738959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_7738959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7738959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7738959 prefixEnd_7738959 := by exact prefixLift 7738959
  have htrace : WordTrace (prefixWord ++ tailWord_7738959) baseStart_7738959 baseEnd_7738959 := by
    simpa [prefixWord, tailWord_7738959, baseEnd_7738959] using wordTrace_append hprefix tailTrace_7738959
  have hstable : (prefixWord ++ tailWord_7738959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7738959).length < 2 ^ (prefixWord ++ tailWord_7738959).sum := by decide
  have hdescent : baseEnd_7738959 < baseStart_7738959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7738959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739040 : List Nat := [2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_7739040 : Nat := 118140960795 + 7739040 * 2 ^ 59
def prefixEnd_7739040 : Nat := 4983230072969 + 3 ^ 40 * 7739040 * 2
def baseEnd_7739040 : Nat := 3973847324371506204108809

theorem tailTrace_7739040 : CollatzResearch.WordTrace tailWord_7739040 prefixEnd_7739040 3973847324371506204108809 := by
  unfold tailWord_7739040
  simp only [CollatzResearch.WordTrace]
  refine ⟨141132988941393638824691287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188177318588524851766255049 141132988941393638824691287)
  ·
    refine ⟨211699483412090458237036931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141132988941393638824691287 211699483412090458237036931)
    ·
      refine ⟨317549225118135687355555397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211699483412090458237036931 317549225118135687355555397)
      ·
        refine ⟨59540479709650441379166637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317549225118135687355555397 59540479709650441379166637)
        ·
          refine ⟨22327679891118915517187489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59540479709650441379166637 22327679891118915517187489)
          ·
            refine ⟨16745759918339186637890617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22327679891118915517187489 16745759918339186637890617)
            ·
              refine ⟨12559319938754389978417963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16745759918339186637890617 12559319938754389978417963)
              ·
                refine ⟨18838979908131584967626945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559319938754389978417963 18838979908131584967626945)
                ·
                  refine ⟨14129234931098688725720209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18838979908131584967626945 14129234931098688725720209)
                  ·
                    refine ⟨10596926198324016544290157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14129234931098688725720209 10596926198324016544290157)
                    ·
                      refine ⟨3973847324371506204108809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10596926198324016544290157 3973847324371506204108809)
                      ·
                        rfl

theorem cell23_7739040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_7739040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739040 prefixEnd_7739040 := by exact prefixLift 7739040
  have htrace : WordTrace (prefixWord ++ tailWord_7739040) baseStart_7739040 baseEnd_7739040 := by
    simpa [prefixWord, tailWord_7739040, baseEnd_7739040] using wordTrace_append hprefix tailTrace_7739040
  have hstable : (prefixWord ++ tailWord_7739040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739040).length < 2 ^ (prefixWord ++ tailWord_7739040).sum := by decide
  have hdescent : baseEnd_7739040 < baseStart_7739040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739097 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 2, 3, 2]
def baseStart_7739097 : Nat := 118140960795 + 7739097 * 2 ^ 59
def prefixEnd_7739097 : Nat := 4983230072969 + 3 ^ 40 * 7739097 * 2
def baseEnd_7739097 : Nat := 3973876592768812481096047

theorem tailTrace_7739097 : CollatzResearch.WordTrace tailWord_7739097 prefixEnd_7739097 3973876592768812481096047 := by
  unfold tailWord_7739097
  simp only [CollatzResearch.WordTrace]
  refine ⟨282268056843580776384207545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188178704562387184256138363 282268056843580776384207545)
  ·
    refine ⟨211701042632685582288155659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282268056843580776384207545 211701042632685582288155659)
    ·
      refine ⟨317551563949028373432233489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211701042632685582288155659 317551563949028373432233489)
      ·
        refine ⟨238163672961771280074175117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317551563949028373432233489 238163672961771280074175117)
        ·
          refine ⟨89311377360664230027815669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238163672961771280074175117 89311377360664230027815669)
          ·
            refine ⟨8372941627562271565107719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89311377360664230027815669 8372941627562271565107719)
            ·
              refine ⟨12559412441343407347661579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8372941627562271565107719 12559412441343407347661579)
              ·
                refine ⟨18839118662015111021492369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559412441343407347661579 18839118662015111021492369)
                ·
                  refine ⟨14129338996511333266119277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18839118662015111021492369 14129338996511333266119277)
                  ·
                    refine ⟨5298502123691749974794729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14129338996511333266119277 5298502123691749974794729)
                    ·
                      refine ⟨3973876592768812481096047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298502123691749974794729 3973876592768812481096047)
                      ·
                        rfl

theorem cell23_7739097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_7739097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739097 prefixEnd_7739097 := by exact prefixLift 7739097
  have htrace : WordTrace (prefixWord ++ tailWord_7739097) baseStart_7739097 baseEnd_7739097 := by
    simpa [prefixWord, tailWord_7739097, baseEnd_7739097] using wordTrace_append hprefix tailTrace_7739097
  have hstable : (prefixWord ++ tailWord_7739097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739097).length < 2 ^ (prefixWord ++ tailWord_7739097).sum := by decide
  have hdescent : baseEnd_7739097 < baseStart_7739097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739103 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 4, 4]
def baseStart_7739103 : Nat := 118140960795 + 7739103 * 2 ^ 59
def prefixEnd_7739103 : Nat := 4983230072969 + 3 ^ 40 * 7739103 * 2
def baseEnd_7739103 : Nat := 1324626557884246485873673

theorem tailTrace_7739103 : CollatzResearch.WordTrace tailWord_7739103 prefixEnd_7739103 1324626557884246485873673 := by
  unfold tailWord_7739103
  simp only [CollatzResearch.WordTrace]
  refine ⟨282268275681559039408925963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188178850454372692939283975 282268275681559039408925963)
  ·
    refine ⟨423402413522338559113388945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282268275681559039408925963 423402413522338559113388945)
    ·
      refine ⟨317551810141753919335041709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423402413522338559113388945 317551810141753919335041709)
      ·
        refine ⟨119081928803157719750640641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317551810141753919335041709 119081928803157719750640641)
        ·
          refine ⟨89311446602368289812980481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119081928803157719750640641 89311446602368289812980481)
          ·
            refine ⟨66983584951776217359735361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89311446602368289812980481 66983584951776217359735361)
            ·
              refine ⟨50237688713832163019801521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66983584951776217359735361 50237688713832163019801521)
              ·
                refine ⟨37678266535374122264851141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50237688713832163019801521 37678266535374122264851141)
                ·
                  refine ⟨7064674975382647924659589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37678266535374122264851141 7064674975382647924659589)
                  ·
                    refine ⟨1324626557884246485873673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7064674975382647924659589 1324626557884246485873673)
                    ·
                      rfl

theorem cell23_7739103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_7739103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739103 prefixEnd_7739103 := by exact prefixLift 7739103
  have htrace : WordTrace (prefixWord ++ tailWord_7739103) baseStart_7739103 baseEnd_7739103 := by
    simpa [prefixWord, tailWord_7739103, baseEnd_7739103] using wordTrace_append hprefix tailTrace_7739103
  have hstable : (prefixWord ++ tailWord_7739103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739103).length < 2 ^ (prefixWord ++ tailWord_7739103).sum := by decide
  have hdescent : baseEnd_7739103 < baseStart_7739103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739136 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_7739136 : Nat := 118140960795 + 7739136 * 2 ^ 59
def prefixEnd_7739136 : Nat := 4983230072969 + 3 ^ 40 * 7739136 * 2
def baseEnd_7739136 : Nat := 3973896618514337828508367

theorem tailTrace_7739136 : CollatzResearch.WordTrace tailWord_7739136 prefixEnd_7739136 3973896618514337828508367 := by
  unfold tailWord_7739136
  simp only [CollatzResearch.WordTrace]
  refine ⟨141134739645219743022438631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188179652860292990696584841 141134739645219743022438631)
  ·
    refine ⟨211702109467829614533657947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141134739645219743022438631 211702109467829614533657947)
    ·
      refine ⟨317553164201744421800486921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211702109467829614533657947 317553164201744421800486921)
      ·
        refine ⟨238164873151308316350365191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317553164201744421800486921 238164873151308316350365191)
        ·
          refine ⟨357247309726962474525547787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238164873151308316350365191 357247309726962474525547787)
          ·
            refine ⟨535870964590443711788321681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357247309726962474525547787 535870964590443711788321681)
            ·
              refine ⟨401903223442832783841241261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535870964590443711788321681 401903223442832783841241261)
              ·
                refine ⟨150713708791062293940465473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401903223442832783841241261 150713708791062293940465473)
                ·
                  refine ⟨113035281593296720455349105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150713708791062293940465473 113035281593296720455349105)
                  ·
                    refine ⟨84776461194972540341511829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113035281593296720455349105 84776461194972540341511829)
                    ·
                      refine ⟨3973896618514337828508367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84776461194972540341511829 3973896618514337828508367)
                      ·
                        rfl

theorem cell23_7739136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_7739136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739136 prefixEnd_7739136 := by exact prefixLift 7739136
  have htrace : WordTrace (prefixWord ++ tailWord_7739136) baseStart_7739136 baseEnd_7739136 := by
    simpa [prefixWord, tailWord_7739136, baseEnd_7739136] using wordTrace_append hprefix tailTrace_7739136
  have hstable : (prefixWord ++ tailWord_7739136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739136).length < 2 ^ (prefixWord ++ tailWord_7739136).sum := by decide
  have hdescent : baseEnd_7739136 < baseStart_7739136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739140 : List Nat := [2, 3, 2, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7739140 : Nat := 118140960795 + 7739140 * 2 ^ 59
def prefixEnd_7739140 : Nat := 4983230072969 + 3 ^ 40 * 7739140 * 2
def baseEnd_7739140 : Nat := 3973898672436955812858349

theorem tailTrace_7739140 : CollatzResearch.WordTrace tailWord_7739140 prefixEnd_7739140 3973898672436955812858349 := by
  unfold tailWord_7739140
  simp only [CollatzResearch.WordTrace]
  refine ⟨141134812591212497364011437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188179750121616663152015249 141134812591212497364011437)
  ·
    refine ⟨52925554721704686511504289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141134812591212497364011437 52925554721704686511504289)
    ·
      refine ⟨39694166041278514883628217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52925554721704686511504289 39694166041278514883628217)
      ·
        refine ⟨29770624530958886162721163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39694166041278514883628217 29770624530958886162721163)
        ·
          refine ⟨44655936796438329244081745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29770624530958886162721163 44655936796438329244081745)
          ·
            refine ⟨33491952597328746933061309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44655936796438329244081745 33491952597328746933061309)
            ·
              refine ⟨12559482223998280099897991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33491952597328746933061309 12559482223998280099897991)
              ·
                refine ⟨18839223335997420149846987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559482223998280099897991 18839223335997420149846987)
                ·
                  refine ⟨28258835003996130224770481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18839223335997420149846987 28258835003996130224770481)
                  ·
                    refine ⟨21194126252997097668577861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28258835003996130224770481 21194126252997097668577861)
                    ·
                      refine ⟨3973898672436955812858349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21194126252997097668577861 3973898672436955812858349)
                      ·
                        rfl

theorem cell23_7739140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7739140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739140 prefixEnd_7739140 := by exact prefixLift 7739140
  have htrace : WordTrace (prefixWord ++ tailWord_7739140) baseStart_7739140 baseEnd_7739140 := by
    simpa [prefixWord, tailWord_7739140, baseEnd_7739140] using wordTrace_append hprefix tailTrace_7739140
  have hstable : (prefixWord ++ tailWord_7739140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739140).length < 2 ^ (prefixWord ++ tailWord_7739140).sum := by decide
  have hdescent : baseEnd_7739140 < baseStart_7739140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739160 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_7739160 : Nat := 118140960795 + 7739160 * 2 ^ 59
def prefixEnd_7739160 : Nat := 4983230072969 + 3 ^ 40 * 7739160 * 2
def baseEnd_7739160 : Nat := 3973908942050045734608257

theorem tailTrace_7739160 : CollatzResearch.WordTrace tailWord_7739160 prefixEnd_7739160 3973908942050045734608257 := by
  unfold tailWord_7739160
  simp only [CollatzResearch.WordTrace]
  refine ⟨141135177321176269071875467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188180236428235025429167289 141135177321176269071875467)
  ·
    refine ⟨211702765981764403607813201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141135177321176269071875467 211702765981764403607813201)
    ·
      refine ⟨158777074486323302705859901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211702765981764403607813201 158777074486323302705859901)
      ·
        refine ⟨59541402932371238514697463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158777074486323302705859901 59541402932371238514697463)
        ·
          refine ⟨89312104398556857772046195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59541402932371238514697463 89312104398556857772046195)
          ·
            refine ⟨133968156597835286658069293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89312104398556857772046195 133968156597835286658069293)
            ·
              refine ⟨50238058724188232496775985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133968156597835286658069293 50238058724188232496775985)
              ·
                refine ⟨37678544043141174372581989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50238058724188232496775985 37678544043141174372581989)
                ·
                  refine ⟨7064727008088970194859123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37678544043141174372581989 7064727008088970194859123)
                  ·
                    refine ⟨10597090512133455292288685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7064727008088970194859123 10597090512133455292288685)
                    ·
                      refine ⟨3973908942050045734608257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10597090512133455292288685 3973908942050045734608257)
                      ·
                        rfl

theorem cell23_7739160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_7739160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739160 prefixEnd_7739160 := by exact prefixLift 7739160
  have htrace : WordTrace (prefixWord ++ tailWord_7739160) baseStart_7739160 baseEnd_7739160 := by
    simpa [prefixWord, tailWord_7739160, baseEnd_7739160] using wordTrace_append hprefix tailTrace_7739160
  have hstable : (prefixWord ++ tailWord_7739160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739160).length < 2 ^ (prefixWord ++ tailWord_7739160).sum := by decide
  have hdescent : baseEnd_7739160 < baseStart_7739160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739194 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3]
def baseStart_7739194 : Nat := 118140960795 + 7739194 * 2 ^ 59
def prefixEnd_7739194 : Nat := 4983230072969 + 3 ^ 40 * 7739194 * 2
def baseEnd_7739194 : Nat := 3973926400392298601583101

theorem tailTrace_7739194 : CollatzResearch.WordTrace tailWord_7739194 prefixEnd_7739194 3973926400392298601583101 := by
  unfold tailWord_7739194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70567898681057340487622159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188181063149486241300325757 70567898681057340487622159)
  ·
    refine ⟨105851848021586010731433239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70567898681057340487622159 105851848021586010731433239)
    ·
      refine ⟨158777772032379016097149859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105851848021586010731433239 158777772032379016097149859)
      ·
        refine ⟨238166658048568524145724789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158777772032379016097149859 238166658048568524145724789)
        ·
          refine ⟨22328124192053299138661699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238166658048568524145724789 22328124192053299138661699)
          ·
            refine ⟨33492186288079948707992549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22328124192053299138661699 33492186288079948707992549)
            ·
              refine ⟨6279784929014990382748603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33492186288079948707992549 6279784929014990382748603)
              ·
                refine ⟨9419677393522485574122905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279784929014990382748603 9419677393522485574122905)
                ·
                  refine ⟨7064758045141864180592179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9419677393522485574122905 7064758045141864180592179)
                  ·
                    refine ⟨10597137067712796270888269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7064758045141864180592179 10597137067712796270888269)
                    ·
                      refine ⟨3973926400392298601583101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10597137067712796270888269 3973926400392298601583101)
                      ·
                        rfl

theorem cell23_7739194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_7739194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739194 prefixEnd_7739194 := by exact prefixLift 7739194
  have htrace : WordTrace (prefixWord ++ tailWord_7739194) baseStart_7739194 baseEnd_7739194 := by
    simpa [prefixWord, tailWord_7739194, baseEnd_7739194] using wordTrace_append hprefix tailTrace_7739194
  have hstable : (prefixWord ++ tailWord_7739194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739194).length < 2 ^ (prefixWord ++ tailWord_7739194).sum := by decide
  have hdescent : baseEnd_7739194 < baseStart_7739194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739203 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_7739203 : Nat := 118140960795 + 7739203 * 2 ^ 59
def prefixEnd_7739203 : Nat := 4983230072969 + 3 ^ 40 * 7739203 * 2
def baseEnd_7739203 : Nat := 3973931021718189066370559

theorem tailTrace_7739203 : CollatzResearch.WordTrace tailWord_7739203 prefixEnd_7739203 3973931021718189066370559 := by
  unfold tailWord_7739203
  simp only [CollatzResearch.WordTrace]
  refine ⟨282271922981196756487566263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188181281987464504325044175 282271922981196756487566263)
  ·
    refine ⟨423407884471795134731349395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282271922981196756487566263 423407884471795134731349395)
    ·
      refine ⟨635111826707692702097024093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423407884471795134731349395 635111826707692702097024093)
      ·
        refine ⟨238166935015384763286384035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635111826707692702097024093 238166935015384763286384035)
        ·
          refine ⟨357250402523077144929576053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238166935015384763286384035 357250402523077144929576053)
          ·
            refine ⟨33492225236538482337147755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357250402523077144929576053 33492225236538482337147755)
            ·
              refine ⟨50238337854807723505721633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33492225236538482337147755 50238337854807723505721633)
              ·
                refine ⟨37678753391105792629291225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50238337854807723505721633 37678753391105792629291225)
                ·
                  refine ⟨28259065043329344471968419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37678753391105792629291225 28259065043329344471968419)
                  ·
                    refine ⟨42388597564994016707952629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28259065043329344471968419 42388597564994016707952629)
                    ·
                      refine ⟨3973931021718189066370559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42388597564994016707952629 3973931021718189066370559)
                      ·
                        rfl

theorem cell23_7739203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_7739203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739203 prefixEnd_7739203 := by exact prefixLift 7739203
  have htrace : WordTrace (prefixWord ++ tailWord_7739203) baseStart_7739203 baseEnd_7739203 := by
    simpa [prefixWord, tailWord_7739203, baseEnd_7739203] using wordTrace_append hprefix tailTrace_7739203
  have hstable : (prefixWord ++ tailWord_7739203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739203).length < 2 ^ (prefixWord ++ tailWord_7739203).sum := by decide
  have hdescent : baseEnd_7739203 < baseStart_7739203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739217 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 1, 4, 2]
def baseStart_7739217 : Nat := 118140960795 + 7739217 * 2 ^ 59
def prefixEnd_7739217 : Nat := 4983230072969 + 3 ^ 40 * 7739217 * 2
def baseEnd_7739217 : Nat := 3973938210447352011595495

theorem tailTrace_7739217 : CollatzResearch.WordTrace tailWord_7739217 prefixEnd_7739217 3973938210447352011595495 := by
  unfold tailWord_7739217
  simp only [CollatzResearch.WordTrace]
  refine ⟨282272433603146036878575905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188181622402097357919050603 282272433603146036878575905)
  ·
    refine ⟨211704325202359527658931929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282272433603146036878575905 211704325202359527658931929)
    ·
      refine ⟨158778243901769645744198947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211704325202359527658931929 158778243901769645744198947)
      ·
        refine ⟨238167365852654468616298421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158778243901769645744198947 238167365852654468616298421)
        ·
          refine ⟨22328190548686356432777977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238167365852654468616298421 22328190548686356432777977)
          ·
            refine ⟨16746142911514767324583483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22328190548686356432777977 16746142911514767324583483)
            ·
              refine ⟨25119214367272150986875225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16746142911514767324583483 25119214367272150986875225)
              ·
                refine ⟨18839410775454113240156419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25119214367272150986875225 18839410775454113240156419)
                ·
                  refine ⟨28259116163181169860234629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18839410775454113240156419 28259116163181169860234629)
                  ·
                    refine ⟨5298584280596469348793993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28259116163181169860234629 5298584280596469348793993)
                    ·
                      refine ⟨3973938210447352011595495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298584280596469348793993 3973938210447352011595495)
                      ·
                        rfl

theorem cell23_7739217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_7739217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739217 prefixEnd_7739217 := by exact prefixLift 7739217
  have htrace : WordTrace (prefixWord ++ tailWord_7739217) baseStart_7739217 baseEnd_7739217 := by
    simpa [prefixWord, tailWord_7739217, baseEnd_7739217] using wordTrace_append hprefix tailTrace_7739217
  have hstable : (prefixWord ++ tailWord_7739217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739217).length < 2 ^ (prefixWord ++ tailWord_7739217).sum := by decide
  have hdescent : baseEnd_7739217 < baseStart_7739217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739220 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_7739220 : Nat := 118140960795 + 7739220 * 2 ^ 59
def prefixEnd_7739220 : Nat := 4983230072969 + 3 ^ 40 * 7739220 * 2
def baseEnd_7739220 : Nat := 3973939750889315499857981

theorem tailTrace_7739220 : CollatzResearch.WordTrace tailWord_7739220 prefixEnd_7739220 3973939750889315499857981 := by
  unfold tailWord_7739220
  simp only [CollatzResearch.WordTrace]
  refine ⟨141136271511067584195467557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188181695348090112260623409 141136271511067584195467557)
  ·
    refine ⟨26463050908325172036650167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141136271511067584195467557 26463050908325172036650167)
    ·
      refine ⟨39694576362487758054975251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26463050908325172036650167 39694576362487758054975251)
      ·
        refine ⟨59541864543731637082462877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39694576362487758054975251 59541864543731637082462877)
        ·
          refine ⟨22328199203899363905923579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59541864543731637082462877 22328199203899363905923579)
          ·
            refine ⟨33492298805849045858885369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22328199203899363905923579 33492298805849045858885369)
            ·
              refine ⟨25119224104386784394164027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33492298805849045858885369 25119224104386784394164027)
              ·
                refine ⟨37678836156580176591246041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25119224104386784394164027 37678836156580176591246041)
                ·
                  refine ⟨28259127117435132443434531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37678836156580176591246041 28259127117435132443434531)
                  ·
                    refine ⟨42388690676152698665151797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28259127117435132443434531 42388690676152698665151797)
                    ·
                      refine ⟨3973939750889315499857981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42388690676152698665151797 3973939750889315499857981)
                      ·
                        rfl

theorem cell23_7739220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_7739220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739220 prefixEnd_7739220 := by exact prefixLift 7739220
  have htrace : WordTrace (prefixWord ++ tailWord_7739220) baseStart_7739220 baseEnd_7739220 := by
    simpa [prefixWord, tailWord_7739220, baseEnd_7739220] using wordTrace_append hprefix tailTrace_7739220
  have hstable : (prefixWord ++ tailWord_7739220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739220).length < 2 ^ (prefixWord ++ tailWord_7739220).sum := by decide
  have hdescent : baseEnd_7739220 < baseStart_7739220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739274 : List Nat := [3, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_7739274 : Nat := 118140960795 + 7739274 * 2 ^ 59
def prefixEnd_7739274 : Nat := 4983230072969 + 3 ^ 40 * 7739274 * 2
def baseEnd_7739274 : Nat := 441551942093850920953637

theorem tailTrace_7739274 : CollatzResearch.WordTrace tailWord_7739274 prefixEnd_7739274 441551942093850920953637 := by
  unfold tailWord_7739274
  simp only [CollatzResearch.WordTrace]
  refine ⟨70568628140984883903350219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188183008375959690408933917 70568628140984883903350219)
  ·
    refine ⟨105852942211477325855025329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70568628140984883903350219 105852942211477325855025329)
    ·
      refine ⟨79389706658607994391268997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105852942211477325855025329 79389706658607994391268997)
      ·
        refine ⟨14885569998488998948362937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79389706658607994391268997 14885569998488998948362937)
        ·
          refine ⟨11164177498866749211272203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14885569998488998948362937 11164177498866749211272203)
          ·
            refine ⟨16746266248300123816908305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164177498866749211272203 16746266248300123816908305)
            ·
              refine ⟨12559699686225092862681229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16746266248300123816908305 12559699686225092862681229)
              ·
                refine ⟨4709887382334409823505461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12559699686225092862681229 4709887382334409823505461)
                ·
                  refine ⟨441551942093850920953637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4709887382334409823505461 441551942093850920953637)
                  ·
                    rfl

theorem cell23_7739274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_7739274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739274 prefixEnd_7739274 := by exact prefixLift 7739274
  have htrace : WordTrace (prefixWord ++ tailWord_7739274) baseStart_7739274 baseEnd_7739274 := by
    simpa [prefixWord, tailWord_7739274, baseEnd_7739274] using wordTrace_append hprefix tailTrace_7739274
  have hstable : (prefixWord ++ tailWord_7739274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739274).length < 2 ^ (prefixWord ++ tailWord_7739274).sum := by decide
  have hdescent : baseEnd_7739274 < baseStart_7739274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739317 : List Nat := [1, 3, 3, 2, 1, 2, 2, 2, 3, 4]
def baseStart_7739317 : Nat := 118140960795 + 7739317 * 2 ^ 59
def prefixEnd_7739317 : Nat := 4983230072969 + 3 ^ 40 * 7739317 * 2
def baseEnd_7739317 : Nat := 1324663186170933873448345

theorem tailTrace_7739317 : CollatzResearch.WordTrace tailWord_7739317 prefixEnd_7739317 1324663186170933873448345 := by
  unfold tailWord_7739317
  simp only [CollatzResearch.WordTrace]
  refine ⟨282276080902783753957216205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188184053935189169304810803 282276080902783753957216205)
  ·
    refine ⟨105853530338543907733956077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282276080902783753957216205 105853530338543907733956077)
    ·
      refine ⟨39695073876953965400233529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105853530338543907733956077 39695073876953965400233529)
      ·
        refine ⟨29771305407715474050175147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39695073876953965400233529 29771305407715474050175147)
        ·
          refine ⟨44656958111573211075262721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29771305407715474050175147 44656958111573211075262721)
          ·
            refine ⟨33492718583679908306447041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44656958111573211075262721 33492718583679908306447041)
            ·
              refine ⟨25119538937759931229835281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33492718583679908306447041 25119538937759931229835281)
              ·
                refine ⟨18839654203319948422376461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25119538937759931229835281 18839654203319948422376461)
                ·
                  refine ⟨7064870326244980658391173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18839654203319948422376461 7064870326244980658391173)
                  ·
                    refine ⟨1324663186170933873448345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7064870326244980658391173 1324663186170933873448345)
                    ·
                      rfl

theorem cell23_7739317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_7739317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739317 prefixEnd_7739317 := by exact prefixLift 7739317
  have htrace : WordTrace (prefixWord ++ tailWord_7739317) baseStart_7739317 baseEnd_7739317 := by
    simpa [prefixWord, tailWord_7739317, baseEnd_7739317] using wordTrace_append hprefix tailTrace_7739317
  have hstable : (prefixWord ++ tailWord_7739317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739317).length < 2 ^ (prefixWord ++ tailWord_7739317).sum := by decide
  have hdescent : baseEnd_7739317 < baseStart_7739317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_7739333 : Nat := 118140960795 + 7739333 * 2 ^ 59
def prefixEnd_7739333 : Nat := 4983230072969 + 3 ^ 40 * 7739333 * 2
def baseEnd_7739333 : Nat := 3973997774203273557744961

theorem tailTrace_7739333 : CollatzResearch.WordTrace tailWord_7739333 prefixEnd_7739333 3973997774203273557744961 := by
  unfold tailWord_7739333
  simp only [CollatzResearch.WordTrace]
  refine ⟨282276664470725788689798653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188184442980483859126532435 282276664470725788689798653)
  ·
    refine ⟨105853749176522170758674495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282276664470725788689798653 105853749176522170758674495)
    ·
      refine ⟨158780623764783256138011743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105853749176522170758674495 158780623764783256138011743)
      ·
        refine ⟨238170935647174884207017615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158780623764783256138011743 238170935647174884207017615)
        ·
          refine ⟨357256403470762326310526423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238170935647174884207017615 357256403470762326310526423)
          ·
            refine ⟨535884605206143489465789635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357256403470762326310526423 535884605206143489465789635)
            ·
              refine ⟨803826907809215234198684453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535884605206143489465789635 803826907809215234198684453)
              ·
                refine ⟨150717545214227856412253335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803826907809215234198684453 150717545214227856412253335)
                ·
                  refine ⟨226076317821341784618380003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150717545214227856412253335 226076317821341784618380003)
                  ·
                    refine ⟨339114476732012676927570005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226076317821341784618380003 339114476732012676927570005)
                    ·
                      refine ⟨3973997774203273557744961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 339114476732012676927570005 3973997774203273557744961)
                      ·
                        rfl

theorem cell23_7739333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_7739333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739333 prefixEnd_7739333 := by exact prefixLift 7739333
  have htrace : WordTrace (prefixWord ++ tailWord_7739333) baseStart_7739333 baseEnd_7739333 := by
    simpa [prefixWord, tailWord_7739333, baseEnd_7739333] using wordTrace_append hprefix tailTrace_7739333
  have hstable : (prefixWord ++ tailWord_7739333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739333).length < 2 ^ (prefixWord ++ tailWord_7739333).sum := by decide
  have hdescent : baseEnd_7739333 < baseStart_7739333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739377 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 3, 5]
def baseStart_7739377 : Nat := 118140960795 + 7739377 * 2 ^ 59
def prefixEnd_7739377 : Nat := 4983230072969 + 3 ^ 40 * 7739377 * 2
def baseEnd_7739377 : Nat := 1324673455784023795198253

theorem tailTrace_7739377 : CollatzResearch.WordTrace tailWord_7739377 prefixEnd_7739377 1324673455784023795198253 := by
  unfold tailWord_7739377
  simp only [CollatzResearch.WordTrace]
  refine ⟨282278269282566384204400385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188185512855044256136266923 282278269282566384204400385)
  ·
    refine ⟨211708701961924788153300289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282278269282566384204400385 211708701961924788153300289)
    ·
      refine ⟨158781526471443591114975217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211708701961924788153300289 158781526471443591114975217)
      ·
        refine ⟨119086144853582693336231413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158781526471443591114975217 119086144853582693336231413)
        ·
          refine ⟨11164326080023377500271695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119086144853582693336231413 11164326080023377500271695)
          ·
            refine ⟨16746489120035066250407543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11164326080023377500271695 16746489120035066250407543)
            ·
              refine ⟨25119733680052599375611315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16746489120035066250407543 25119733680052599375611315)
              ·
                refine ⟨37679600520078899063416973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25119733680052599375611315 37679600520078899063416973)
                ·
                  refine ⟨14129850195029587148781365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37679600520078899063416973 14129850195029587148781365)
                  ·
                    refine ⟨1324673455784023795198253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14129850195029587148781365 1324673455784023795198253)
                    ·
                      rfl

theorem cell23_7739377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 5].length) (baseStart_7739377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739377 prefixEnd_7739377 := by exact prefixLift 7739377
  have htrace : WordTrace (prefixWord ++ tailWord_7739377) baseStart_7739377 baseEnd_7739377 := by
    simpa [prefixWord, tailWord_7739377, baseEnd_7739377] using wordTrace_append hprefix tailTrace_7739377
  have hstable : (prefixWord ++ tailWord_7739377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739377).length < 2 ^ (prefixWord ++ tailWord_7739377).sum := by decide
  have hdescent : baseEnd_7739377 < baseStart_7739377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739427 : List Nat := [1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4]
def baseStart_7739427 : Nat := 118140960795 + 7739427 * 2 ^ 59
def prefixEnd_7739427 : Nat := 4983230072969 + 3 ^ 40 * 7739427 * 2
def baseEnd_7739427 : Nat := 3974046041384796189969529

theorem tailTrace_7739427 : CollatzResearch.WordTrace tailWord_7739427 prefixEnd_7739427 3974046041384796189969529 := by
  unfold tailWord_7739427
  simp only [CollatzResearch.WordTrace]
  refine ⟨282280092932385242743720535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188186728621590161829147023 282280092932385242743720535)
  ·
    refine ⟨423420139398577864115580803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282280092932385242743720535 423420139398577864115580803)
    ·
      refine ⟨635130209097866796173371205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423420139398577864115580803 635130209097866796173371205)
      ·
        refine ⟨119086914205850024282507101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 635130209097866796173371205 119086914205850024282507101)
        ·
          refine ⟨44657592827193759105940163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119086914205850024282507101 44657592827193759105940163)
          ·
            refine ⟨66986389240790638658910245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44657592827193759105940163 66986389240790638658910245)
            ·
              refine ⟨12559947982648244748545671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66986389240790638658910245 12559947982648244748545671)
              ·
                refine ⟨18839921973972367122818507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12559947982648244748545671 18839921973972367122818507)
                ·
                  refine ⟨28259882960958550684227761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18839921973972367122818507 28259882960958550684227761)
                  ·
                    refine ⟨21194912220718913013170821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28259882960958550684227761 21194912220718913013170821)
                    ·
                      refine ⟨3974046041384796189969529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21194912220718913013170821 3974046041384796189969529)
                      ·
                        rfl

theorem cell23_7739427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_7739427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739427 prefixEnd_7739427 := by exact prefixLift 7739427
  have htrace : WordTrace (prefixWord ++ tailWord_7739427) baseStart_7739427 baseEnd_7739427 := by
    simpa [prefixWord, tailWord_7739427, baseEnd_7739427] using wordTrace_append hprefix tailTrace_7739427
  have hstable : (prefixWord ++ tailWord_7739427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739427).length < 2 ^ (prefixWord ++ tailWord_7739427).sum := by decide
  have hdescent : baseEnd_7739427 < baseStart_7739427 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739434 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_7739434 : Nat := 118140960795 + 7739434 * 2 ^ 59
def prefixEnd_7739434 : Nat := 4983230072969 + 3 ^ 40 * 7739434 * 2
def baseEnd_7739434 : Nat := 3974049635749377662581997

theorem tailTrace_7739434 : CollatzResearch.WordTrace tailWord_7739434 prefixEnd_7739434 3974049635749377662581997 := by
  unfold tailWord_7739434
  simp only [CollatzResearch.WordTrace]
  refine ⟨70570087060839970734806339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188186898828906588626150237 70570087060839970734806339)
  ·
    refine ⟨105855130591259956102209509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70570087060839970734806339 105855130591259956102209509)
    ·
      refine ⟨19847836985861241769164283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105855130591259956102209509 19847836985861241769164283)
      ·
        refine ⟨29771755478791862653746425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19847836985861241769164283 29771755478791862653746425)
        ·
          refine ⟨22328816609093896990309819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29771755478791862653746425 22328816609093896990309819)
          ·
            refine ⟨33493224913640845485464729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22328816609093896990309819 33493224913640845485464729)
            ·
              refine ⟨25119918685230634114098547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33493224913640845485464729 25119918685230634114098547)
              ·
                refine ⟨37679878027845951171147821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25119918685230634114098547 37679878027845951171147821)
                ·
                  refine ⟨14129954260442231689180433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37679878027845951171147821 14129954260442231689180433)
                  ·
                    refine ⟨10597465695331673766885325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14129954260442231689180433 10597465695331673766885325)
                    ·
                      refine ⟨3974049635749377662581997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10597465695331673766885325 3974049635749377662581997)
                      ·
                        rfl

theorem cell23_7739434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_7739434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739434 prefixEnd_7739434 := by exact prefixLift 7739434
  have htrace : WordTrace (prefixWord ++ tailWord_7739434) baseStart_7739434 baseEnd_7739434 := by
    simpa [prefixWord, tailWord_7739434, baseEnd_7739434] using wordTrace_append hprefix tailTrace_7739434
  have hstable : (prefixWord ++ tailWord_7739434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739434).length < 2 ^ (prefixWord ++ tailWord_7739434).sum := by decide
  have hdescent : baseEnd_7739434 < baseStart_7739434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739447 : List Nat := [1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_7739447 : Nat := 118140960795 + 7739447 * 2 ^ 59
def prefixEnd_7739447 : Nat := 4983230072969 + 3 ^ 40 * 7739447 * 2
def baseEnd_7739447 : Nat := 3974056310997886111719437

theorem tailTrace_7739447 : CollatzResearch.WordTrace tailWord_7739447 prefixEnd_7739447 3974056310997886111719437 := by
  unfold tailWord_7739447
  simp only [CollatzResearch.WordTrace]
  refine ⟨282280822392312786159448595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188187214928208524106299063 282280822392312786159448595)
  ·
    refine ⟨423421233588469179239172893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282280822392312786159448595 423421233588469179239172893)
    ·
      refine ⟨158782962595675942214689835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423421233588469179239172893 158782962595675942214689835)
      ·
        refine ⟨238174443893513913322034753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158782962595675942214689835 238174443893513913322034753)
        ·
          refine ⟨178630832920135434991526065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238174443893513913322034753 178630832920135434991526065)
          ·
            refine ⟨133973124690101576243644549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178630832920135434991526065 133973124690101576243644549)
            ·
              refine ⟨25119960879394045545683353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133973124690101576243644549 25119960879394045545683353)
              ·
                refine ⟨18839970659545534159262515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25119960879394045545683353 18839970659545534159262515)
                ·
                  refine ⟨28259955989318301238893773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18839970659545534159262515 28259955989318301238893773)
                  ·
                    refine ⟨10597483495994362964585165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28259955989318301238893773 10597483495994362964585165)
                    ·
                      refine ⟨3974056310997886111719437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10597483495994362964585165 3974056310997886111719437)
                      ·
                        rfl

theorem cell23_7739447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_7739447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739447 prefixEnd_7739447 := by exact prefixLift 7739447
  have htrace : WordTrace (prefixWord ++ tailWord_7739447) baseStart_7739447 baseEnd_7739447 := by
    simpa [prefixWord, tailWord_7739447, baseEnd_7739447] using wordTrace_append hprefix tailTrace_7739447
  have hstable : (prefixWord ++ tailWord_7739447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739447).length < 2 ^ (prefixWord ++ tailWord_7739447).sum := by decide
  have hdescent : baseEnd_7739447 < baseStart_7739447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739448 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_7739448 : Nat := 118140960795 + 7739448 * 2 ^ 59
def prefixEnd_7739448 : Nat := 4983230072969 + 3 ^ 40 * 7739448 * 2
def baseEnd_7739448 : Nat := 3974056824478540607806933

theorem tailTrace_7739448 : CollatzResearch.WordTrace tailWord_7739448 prefixEnd_7739448 3974056824478540607806933 := by
  unfold tailWord_7739448
  simp only [CollatzResearch.WordTrace]
  refine ⟨141140429432654581665117499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188187239243539442220156665 141140429432654581665117499)
  ·
    refine ⟨211710644148981872497676249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141140429432654581665117499 211710644148981872497676249)
    ·
      refine ⟨158782983111736404373257187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211710644148981872497676249 158782983111736404373257187)
      ·
        refine ⟨238174474667604606559885781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158782983111736404373257187 238174474667604606559885781)
        ·
          refine ⟨5582214250021982966247323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 238174474667604606559885781 5582214250021982966247323)
          ·
            refine ⟨8373321375032974449370985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582214250021982966247323 8373321375032974449370985)
            ·
              refine ⟨6279991031274730837028239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8373321375032974449370985 6279991031274730837028239)
              ·
                refine ⟨9419986546912096255542359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6279991031274730837028239 9419986546912096255542359)
                ·
                  refine ⟨14129979820368144383313539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9419986546912096255542359 14129979820368144383313539)
                  ·
                    refine ⟨21194969730552216574970309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14129979820368144383313539 21194969730552216574970309)
                    ·
                      refine ⟨3974056824478540607806933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21194969730552216574970309 3974056824478540607806933)
                      ·
                        rfl

theorem cell23_7739448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_7739448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739448 prefixEnd_7739448 := by exact prefixLift 7739448
  have htrace : WordTrace (prefixWord ++ tailWord_7739448) baseStart_7739448 baseEnd_7739448 := by
    simpa [prefixWord, tailWord_7739448, baseEnd_7739448] using wordTrace_append hprefix tailTrace_7739448
  have hstable : (prefixWord ++ tailWord_7739448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739448).length < 2 ^ (prefixWord ++ tailWord_7739448).sum := by decide
  have hdescent : baseEnd_7739448 < baseStart_7739448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739464 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_7739464 : Nat := 118140960795 + 7739464 * 2 ^ 59
def prefixEnd_7739464 : Nat := 4983230072969 + 3 ^ 40 * 7739464 * 2
def baseEnd_7739464 : Nat := 3974065040169012545206859

theorem tailTrace_7739464 : CollatzResearch.WordTrace tailWord_7739464 prefixEnd_7739464 3974065040169012545206859 := by
  unfold tailWord_7739464
  simp only [CollatzResearch.WordTrace]
  refine ⟨141140721216625599031408723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188187628288834132041878297 141140721216625599031408723)
  ·
    refine ⟨211711081824938398547113085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141140721216625599031408723 211711081824938398547113085)
    ·
      refine ⟨79391655684351899455167407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211711081824938398547113085 79391655684351899455167407)
      ·
        refine ⟨119087483526527849182751111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79391655684351899455167407 119087483526527849182751111)
        ·
          refine ⟨178631225289791773774126667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119087483526527849182751111 178631225289791773774126667)
          ·
            refine ⟨267946837934687660661190001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178631225289791773774126667 267946837934687660661190001)
            ·
              refine ⟨200960128451015745495892501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267946837934687660661190001 200960128451015745495892501)
              ·
                refine ⟨9420006021141363070119961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200960128451015745495892501 9420006021141363070119961)
                ·
                  refine ⟨7065004515856022302589971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420006021141363070119961 7065004515856022302589971)
                  ·
                    refine ⟨10597506773784033453884957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065004515856022302589971 10597506773784033453884957)
                    ·
                      refine ⟨3974065040169012545206859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10597506773784033453884957 3974065040169012545206859)
                      ·
                        rfl

theorem cell23_7739464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_7739464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739464 prefixEnd_7739464 := by exact prefixLift 7739464
  have htrace : WordTrace (prefixWord ++ tailWord_7739464) baseStart_7739464 baseEnd_7739464 := by
    simpa [prefixWord, tailWord_7739464, baseEnd_7739464] using wordTrace_append hprefix tailTrace_7739464
  have hstable : (prefixWord ++ tailWord_7739464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739464).length < 2 ^ (prefixWord ++ tailWord_7739464).sum := by decide
  have hdescent : baseEnd_7739464 < baseStart_7739464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739478 : List Nat := [5, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_7739478 : Nat := 118140960795 + 7739478 * 2 ^ 59
def prefixEnd_7739478 : Nat := 4983230072969 + 3 ^ 40 * 7739478 * 2
def baseEnd_7739478 : Nat := 3974072228898175490431795

theorem tailTrace_7739478 : CollatzResearch.WordTrace tailWord_7739478 prefixEnd_7739478 3974072228898175490431795 := by
  unfold tailWord_7739478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642622065950029903364193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188187968703466985635884725 17642622065950029903364193)
  ·
    refine ⟨13231966549462522427523145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17642622065950029903364193 13231966549462522427523145)
    ·
      refine ⟨9923974912096891820642359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13231966549462522427523145 9923974912096891820642359)
      ·
        refine ⟨14885962368145337730963539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9923974912096891820642359 14885962368145337730963539)
        ·
          refine ⟨22328943552218006596445309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14885962368145337730963539 22328943552218006596445309)
          ·
            refine ⟨8373353832081752473666991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22328943552218006596445309 8373353832081752473666991)
            ·
              refine ⟨12560030748122628710500487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373353832081752473666991 12560030748122628710500487)
              ·
                refine ⟨18840046122183943065750731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12560030748122628710500487 18840046122183943065750731)
                ·
                  refine ⟨28260069183275914598626097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18840046122183943065750731 28260069183275914598626097)
                  ·
                    refine ⟨21195051887456935948969573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28260069183275914598626097 21195051887456935948969573)
                    ·
                      refine ⟨3974072228898175490431795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21195051887456935948969573 3974072228898175490431795)
                      ·
                        rfl

theorem cell23_7739478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_7739478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739478 prefixEnd_7739478 := by exact prefixLift 7739478
  have htrace : WordTrace (prefixWord ++ tailWord_7739478) baseStart_7739478 baseEnd_7739478 := by
    simpa [prefixWord, tailWord_7739478, baseEnd_7739478] using wordTrace_append hprefix tailTrace_7739478
  have hstable : (prefixWord ++ tailWord_7739478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739478).length < 2 ^ (prefixWord ++ tailWord_7739478).sum := by decide
  have hdescent : baseEnd_7739478 < baseStart_7739478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739481 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 2, 1, 3]
def baseStart_7739481 : Nat := 118140960795 + 7739481 * 2 ^ 59
def prefixEnd_7739481 : Nat := 4983230072969 + 3 ^ 40 * 7739481 * 2
def baseEnd_7739481 : Nat := 3974073769340138978694281

theorem tailTrace_7739481 : CollatzResearch.WordTrace tailWord_7739481 prefixEnd_7739481 3974073769340138978694281 := by
  unfold tailWord_7739481
  simp only [CollatzResearch.WordTrace]
  refine ⟨282282062474189609966186297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188188041649459739977457531 282282062474189609966186297)
  ·
    refine ⟨211711546855642207474639723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282282062474189609966186297 211711546855642207474639723)
    ·
      refine ⟨317567320283463311211959585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211711546855642207474639723 317567320283463311211959585)
      ·
        refine ⟨238175490212597483408969689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317567320283463311211959585 238175490212597483408969689)
        ·
          refine ⟨178631617659448112556727267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238175490212597483408969689 178631617659448112556727267)
          ·
            refine ⟨267947426489172168835090901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178631617659448112556727267 267947426489172168835090901)
            ·
              refine ⟨6280017808339972707072443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 267947426489172168835090901 6280017808339972707072443)
              ·
                refine ⟨9420026712509959060608665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280017808339972707072443 9420026712509959060608665)
                ·
                  refine ⟨7065020034382469295456499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420026712509959060608665 7065020034382469295456499)
                  ·
                    refine ⟨10597530051573703943184749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065020034382469295456499 10597530051573703943184749)
                    ·
                      refine ⟨3974073769340138978694281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10597530051573703943184749 3974073769340138978694281)
                      ·
                        rfl

theorem cell23_7739481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_7739481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739481 prefixEnd_7739481 := by exact prefixLift 7739481
  have htrace : WordTrace (prefixWord ++ tailWord_7739481) baseStart_7739481 baseEnd_7739481 := by
    simpa [prefixWord, tailWord_7739481, baseEnd_7739481] using wordTrace_append hprefix tailTrace_7739481
  have hstable : (prefixWord ++ tailWord_7739481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739481).length < 2 ^ (prefixWord ++ tailWord_7739481).sum := by decide
  have hdescent : baseEnd_7739481 < baseStart_7739481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739520 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_7739520 : Nat := 118140960795 + 7739520 * 2 ^ 59
def prefixEnd_7739520 : Nat := 4983230072969 + 3 ^ 40 * 7739520 * 2
def baseEnd_7739520 : Nat := 3974093795085664326106601

theorem tailTrace_7739520 : CollatzResearch.WordTrace tailWord_7739520 prefixEnd_7739520 3974093795085664326106601 := by
  unfold tailWord_7739520
  simp only [CollatzResearch.WordTrace]
  refine ⟨141141742460524159813428007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188188989947365546417904009 141141742460524159813428007)
  ·
    refine ⟨211712613690786239720142011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141141742460524159813428007 211712613690786239720142011)
    ·
      refine ⟨317568920536179359580213017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211712613690786239720142011 317568920536179359580213017)
      ·
        refine ⟨238176690402134519685159763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317568920536179359580213017 238176690402134519685159763)
        ·
          refine ⟨357265035603201779527739645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238176690402134519685159763 357265035603201779527739645)
          ·
            refine ⟨133974388351200667322902367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357265035603201779527739645 133974388351200667322902367)
            ·
              refine ⟨200961582526801000984353551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133974388351200667322902367 200961582526801000984353551)
              ·
                refine ⟨301442373790201501476530327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200961582526801000984353551 301442373790201501476530327)
                ·
                  refine ⟨452163560685302252214795491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301442373790201501476530327 452163560685302252214795491)
                  ·
                    refine ⟨678245341027953378322193237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 452163560685302252214795491 678245341027953378322193237)
                    ·
                      refine ⟨3974093795085664326106601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 678245341027953378322193237 3974093795085664326106601)
                      ·
                        rfl

theorem cell23_7739520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_7739520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739520 prefixEnd_7739520 := by exact prefixLift 7739520
  have htrace : WordTrace (prefixWord ++ tailWord_7739520) baseStart_7739520 baseEnd_7739520 := by
    simpa [prefixWord, tailWord_7739520, baseEnd_7739520] using wordTrace_append hprefix tailTrace_7739520
  have hstable : (prefixWord ++ tailWord_7739520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739520).length < 2 ^ (prefixWord ++ tailWord_7739520).sum := by decide
  have hdescent : baseEnd_7739520 < baseStart_7739520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739527 : List Nat := [1, 1, 4, 2, 1, 1, 5, 1, 7]
def baseStart_7739527 : Nat := 118140960795 + 7739527 * 2 ^ 59
def prefixEnd_7739527 : Nat := 4983230072969 + 3 ^ 40 * 7739527 * 2
def baseEnd_7739527 : Nat := 441566376605582866524341

theorem tailTrace_7739527 : CollatzResearch.WordTrace tailWord_7739527 prefixEnd_7739527 441566376605582866524341 := by
  unfold tailWord_7739527
  simp only [CollatzResearch.WordTrace]
  refine ⟨282283740232022959822360835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188189160154681973214907223 282283740232022959822360835)
  ·
    refine ⟨423425610348034439733541253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282283740232022959822360835 423425610348034439733541253)
    ·
      refine ⟨79392301940256457450038985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 423425610348034439733541253 79392301940256457450038985)
      ·
        refine ⟨59544226455192343087529239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79392301940256457450038985 59544226455192343087529239)
        ·
          refine ⟨89316339682788514631293859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59544226455192343087529239 89316339682788514631293859)
          ·
            refine ⟨133974509524182771946940789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89316339682788514631293859 133974509524182771946940789)
            ·
              refine ⟨12560110267892134870025699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133974509524182771946940789 12560110267892134870025699)
              ·
                refine ⟨18840165401838202305038549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12560110267892134870025699 18840165401838202305038549)
                ·
                  refine ⟨441566376605582866524341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18840165401838202305038549 441566376605582866524341)
                  ·
                    rfl

theorem cell23_7739527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 7].length) (baseStart_7739527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739527 prefixEnd_7739527 := by exact prefixLift 7739527
  have htrace : WordTrace (prefixWord ++ tailWord_7739527) baseStart_7739527 baseEnd_7739527 := by
    simpa [prefixWord, tailWord_7739527, baseEnd_7739527] using wordTrace_append hprefix tailTrace_7739527
  have hstable : (prefixWord ++ tailWord_7739527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739527).length < 2 ^ (prefixWord ++ tailWord_7739527).sum := by decide
  have hdescent : baseEnd_7739527 < baseStart_7739527 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739538 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_7739538 : Nat := 118140960795 + 7739538 * 2 ^ 59
def prefixEnd_7739538 : Nat := 4983230072969 + 3 ^ 40 * 7739538 * 2
def baseEnd_7739538 : Nat := 3974103037737445255681519

theorem tailTrace_7739538 : CollatzResearch.WordTrace tailWord_7739538 prefixEnd_7739538 3974103037737445255681519 := by
  unfold tailWord_7739538
  simp only [CollatzResearch.WordTrace]
  refine ⟨70571035358745777175252817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188189427623322072467340845 70571035358745777175252817)
  ·
    refine ⟨52928276519059332881439613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70571035358745777175252817 52928276519059332881439613)
    ·
      refine ⟨19848103694647249830539855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52928276519059332881439613 19848103694647249830539855)
      ·
        refine ⟨29772155541970874745809783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19848103694647249830539855 29772155541970874745809783)
        ·
          refine ⟨44658233312956312118714675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29772155541970874745809783 44658233312956312118714675)
          ·
            refine ⟨66987349969434468178072013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44658233312956312118714675 66987349969434468178072013)
            ·
              refine ⟨25120256238537925566777005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66987349969434468178072013 25120256238537925566777005)
              ·
                refine ⟨9420096089451722087541377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25120256238537925566777005 9420096089451722087541377)
                ·
                  refine ⟨7065072067088791565656033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420096089451722087541377 7065072067088791565656033)
                  ·
                    refine ⟨5298804050316593674242025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065072067088791565656033 5298804050316593674242025)
                    ·
                      refine ⟨3974103037737445255681519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298804050316593674242025 3974103037737445255681519)
                      ·
                        rfl

theorem cell23_7739538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_7739538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739538 prefixEnd_7739538 := by exact prefixLift 7739538
  have htrace : WordTrace (prefixWord ++ tailWord_7739538) baseStart_7739538 baseEnd_7739538 := by
    simpa [prefixWord, tailWord_7739538, baseEnd_7739538] using wordTrace_append hprefix tailTrace_7739538
  have hstable : (prefixWord ++ tailWord_7739538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739538).length < 2 ^ (prefixWord ++ tailWord_7739538).sum := by decide
  have hdescent : baseEnd_7739538 < baseStart_7739538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739617 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 8]
def baseStart_7739617 : Nat := 118140960795 + 7739617 * 2 ^ 59
def prefixEnd_7739617 : Nat := 4983230072969 + 3 ^ 40 * 7739617 * 2
def baseEnd_7739617 : Nat := 441571511412127827399295

theorem tailTrace_7739617 : CollatzResearch.WordTrace tailWord_7739617 prefixEnd_7739617 441571511412127827399295 := by
  unfold tailWord_7739617
  simp only [CollatzResearch.WordTrace]
  refine ⟨282287022801696905193137105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188191348534464603462091403 282287022801696905193137105)
  ·
    refine ⟨211715267101272678894852829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282287022801696905193137105 211715267101272678894852829)
    ·
      refine ⟨79393225162977254585569811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211715267101272678894852829 79393225162977254585569811)
      ·
        refine ⟨119089837744465881878354717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79393225162977254585569811 119089837744465881878354717)
        ·
          refine ⟨44658689154174705704383019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119089837744465881878354717 44658689154174705704383019)
          ·
            refine ⟨66988033731262058556574529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44658689154174705704383019 66988033731262058556574529)
            ·
              refine ⟨50241025298446543917430897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66988033731262058556574529 50241025298446543917430897)
              ·
                refine ⟨37680768973834907938073173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50241025298446543917430897 37680768973834907938073173)
                ·
                  refine ⟨441571511412127827399295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37680768973834907938073173 441571511412127827399295)
                  ·
                    rfl

theorem cell23_7739617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 8].length) (baseStart_7739617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739617 prefixEnd_7739617 := by exact prefixLift 7739617
  have htrace : WordTrace (prefixWord ++ tailWord_7739617) baseStart_7739617 baseEnd_7739617 := by
    simpa [prefixWord, tailWord_7739617, baseEnd_7739617] using wordTrace_append hprefix tailTrace_7739617
  have hstable : (prefixWord ++ tailWord_7739617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739617).length < 2 ^ (prefixWord ++ tailWord_7739617).sum := by decide
  have hdescent : baseEnd_7739617 < baseStart_7739617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739634 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_7739634 : Nat := 118140960795 + 7739634 * 2 ^ 59
def prefixEnd_7739634 : Nat := 4983230072969 + 3 ^ 40 * 7739634 * 2
def baseEnd_7739634 : Nat := 441572481320030764453453

theorem tailTrace_7739634 : CollatzResearch.WordTrace tailWord_7739634 prefixEnd_7739634 441572481320030764453453 := by
  unfold tailWord_7739634
  simp only [CollatzResearch.WordTrace]
  refine ⟨70571910710658829274126489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188191761895090211397670637 70571910710658829274126489)
  ·
    refine ⟨52928933032994121955594867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70571910710658829274126489 52928933032994121955594867)
    ·
      refine ⟨79393399549491182933392301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52928933032994121955594867 79393399549491182933392301)
      ·
        refine ⟨29772524831059193600022113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79393399549491182933392301 29772524831059193600022113)
        ·
          refine ⟨22329393623294395200016585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29772524831059193600022113 22329393623294395200016585)
          ·
            refine ⟨16747045217470796400012439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22329393623294395200016585 16747045217470796400012439)
            ·
              refine ⟨25120567826206194600018659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747045217470796400012439 25120567826206194600018659)
              ·
                refine ⟨37680851739309291900027989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25120567826206194600018659 37680851739309291900027989)
                ·
                  refine ⟨441572481320030764453453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37680851739309291900027989 441572481320030764453453)
                  ·
                    rfl

theorem cell23_7739634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_7739634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739634 prefixEnd_7739634 := by exact prefixLift 7739634
  have htrace : WordTrace (prefixWord ++ tailWord_7739634) baseStart_7739634 baseEnd_7739634 := by
    simpa [prefixWord, tailWord_7739634, baseEnd_7739634] using wordTrace_append hprefix tailTrace_7739634
  have hstable : (prefixWord ++ tailWord_7739634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739634).length < 2 ^ (prefixWord ++ tailWord_7739634).sum := by decide
  have hdescent : baseEnd_7739634 < baseStart_7739634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739638 : List Nat := [5, 1, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_7739638 : Nat := 118140960795 + 7739638 * 2 ^ 59
def prefixEnd_7739638 : Nat := 4983230072969 + 3 ^ 40 * 7739638 * 2
def baseEnd_7739638 : Nat := 1324718128600964954810353

theorem tailTrace_7739638 : CollatzResearch.WordTrace tailWord_7739638 prefixEnd_7739638 1324718128600964954810353 := by
  unfold tailWord_7739638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17642986795913801611228223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188191859156413883853101045 17642986795913801611228223)
  ·
    refine ⟨26464480193870702416842335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17642986795913801611228223 26464480193870702416842335)
    ·
      refine ⟨39696720290806053625263503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26464480193870702416842335 39696720290806053625263503)
      ·
        refine ⟨59545080436209080437895255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39696720290806053625263503 59545080436209080437895255)
        ·
          refine ⟨89317620654313620656842883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59545080436209080437895255 89317620654313620656842883)
          ·
            refine ⟨133976430981470430985264325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89317620654313620656842883 133976430981470430985264325)
            ·
              refine ⟨25120580809025705809737061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133976430981470430985264325 25120580809025705809737061)
              ·
                refine ⟨4710108901692319839325699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25120580809025705809737061 4710108901692319839325699)
                ·
                  refine ⟨7065163352538479758988549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710108901692319839325699 7065163352538479758988549)
                  ·
                    refine ⟨1324718128600964954810353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065163352538479758988549 1324718128600964954810353)
                    ·
                      rfl

theorem cell23_7739638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_7739638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739638 prefixEnd_7739638 := by exact prefixLift 7739638
  have htrace : WordTrace (prefixWord ++ tailWord_7739638) baseStart_7739638 baseEnd_7739638 := by
    simpa [prefixWord, tailWord_7739638, baseEnd_7739638] using wordTrace_append hprefix tailTrace_7739638
  have hstable : (prefixWord ++ tailWord_7739638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739638).length < 2 ^ (prefixWord ++ tailWord_7739638).sum := by decide
  have hdescent : baseEnd_7739638 < baseStart_7739638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739667 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_7739667 : Nat := 118140960795 + 7739667 * 2 ^ 59
def prefixEnd_7739667 : Nat := 4983230072969 + 3 ^ 40 * 7739667 * 2
def baseEnd_7739667 : Nat := 3974169276741875250968425

theorem tailTrace_7739667 : CollatzResearch.WordTrace tailWord_7739667 prefixEnd_7739667 3974169276741875250968425 := by
  unfold tailWord_7739667
  simp only [CollatzResearch.WordTrace]
  refine ⟨282288846451515763732457255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188192564301010509154971503 282288846451515763732457255)
  ·
    refine ⟨423433269677273645598685883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282288846451515763732457255 423433269677273645598685883)
    ·
      refine ⟨635149904515910468398028825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423433269677273645598685883 635149904515910468398028825)
      ·
        refine ⟨476362428386932851298521619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635149904515910468398028825 476362428386932851298521619)
        ·
          refine ⟨714543642580399276947782429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476362428386932851298521619 714543642580399276947782429)
          ·
            refine ⟨267953865967649728855418411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 714543642580399276947782429 267953865967649728855418411)
            ·
              refine ⟨401930798951474593283127617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267953865967649728855418411 401930798951474593283127617)
              ·
                refine ⟨301448099213605944962345713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401930798951474593283127617 301448099213605944962345713)
                ·
                  refine ⟨226086074410204458721759285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301448099213605944962345713 226086074410204458721759285)
                  ·
                    refine ⟨21195569475956668005164933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226086074410204458721759285 21195569475956668005164933)
                    ·
                      refine ⟨3974169276741875250968425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21195569475956668005164933 3974169276741875250968425)
                      ·
                        rfl

theorem cell23_7739667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_7739667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739667 prefixEnd_7739667 := by exact prefixLift 7739667
  have htrace : WordTrace (prefixWord ++ tailWord_7739667) baseStart_7739667 baseEnd_7739667 := by
    simpa [prefixWord, tailWord_7739667, baseEnd_7739667] using wordTrace_append hprefix tailTrace_7739667
  have hstable : (prefixWord ++ tailWord_7739667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739667).length < 2 ^ (prefixWord ++ tailWord_7739667).sum := by decide
  have hdescent : baseEnd_7739667 < baseStart_7739667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739671 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_7739671 : Nat := 118140960795 + 7739671 * 2 ^ 59
def prefixEnd_7739671 : Nat := 4983230072969 + 3 ^ 40 * 7739671 * 2
def baseEnd_7739671 : Nat := 3974171330664493235318407

theorem tailTrace_7739671 : CollatzResearch.WordTrace tailWord_7739671 prefixEnd_7739671 3974171330664493235318407 := by
  unfold tailWord_7739671
  simp only [CollatzResearch.WordTrace]
  refine ⟨282288992343501272415602867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188192661562334181610401911 282288992343501272415602867)
  ·
    refine ⟨423433488515251908623404301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282288992343501272415602867 423433488515251908623404301)
    ·
      refine ⟨158787558193219465733776613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423433488515251908623404301 158787558193219465733776613)
      ·
        refine ⟨29772667161228649825083115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158787558193219465733776613 29772667161228649825083115)
        ·
          refine ⟨44659000741842974737624673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29772667161228649825083115 44659000741842974737624673)
          ·
            refine ⟨33494250556382231053218505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44659000741842974737624673 33494250556382231053218505)
            ·
              refine ⟨25120687917286673289913879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33494250556382231053218505 25120687917286673289913879)
              ·
                refine ⟨37681031875930009934870819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25120687917286673289913879 37681031875930009934870819)
                ·
                  refine ⟨56521547813895014902306229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37681031875930009934870819 56521547813895014902306229)
                  ·
                    refine ⟨5298895107552657647091209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56521547813895014902306229 5298895107552657647091209)
                    ·
                      refine ⟨3974171330664493235318407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298895107552657647091209 3974171330664493235318407)
                      ·
                        rfl

theorem cell23_7739671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_7739671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739671 prefixEnd_7739671 := by exact prefixLift 7739671
  have htrace : WordTrace (prefixWord ++ tailWord_7739671) baseStart_7739671 baseEnd_7739671 := by
    simpa [prefixWord, tailWord_7739671, baseEnd_7739671] using wordTrace_append hprefix tailTrace_7739671
  have hstable : (prefixWord ++ tailWord_7739671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739671).length < 2 ^ (prefixWord ++ tailWord_7739671).sum := by decide
  have hdescent : baseEnd_7739671 < baseStart_7739671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739704 : List Nat := [2, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_7739704 : Nat := 118140960795 + 7739704 * 2 ^ 59
def prefixEnd_7739704 : Nat := 4983230072969 + 3 ^ 40 * 7739704 * 2
def baseEnd_7739704 : Nat := 3974188275526091606205755

theorem tailTrace_7739704 : CollatzResearch.WordTrace tailWord_7739704 prefixEnd_7739704 3974188275526091606205755 := by
  unfold tailWord_7739704
  simp only [CollatzResearch.WordTrace]
  refine ⟨141145097976190859525777083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188193463968254479367702777 141145097976190859525777083)
  ·
    refine ⟨211717646964286289288665625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141145097976190859525777083 211717646964286289288665625)
    ·
      refine ⟨158788235223214716966499219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211717646964286289288665625 158788235223214716966499219)
      ·
        refine ⟨238182352834822075449748829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158788235223214716966499219 238182352834822075449748829)
        ·
          refine ⟨89318382313058278293655811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238182352834822075449748829 89318382313058278293655811)
          ·
            refine ⟨133977573469587417440483717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89318382313058278293655811 133977573469587417440483717)
            ·
              refine ⟨25120795025547640770090697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133977573469587417440483717 25120795025547640770090697)
              ·
                refine ⟨18840596269160730577568023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25120795025547640770090697 18840596269160730577568023)
                ·
                  refine ⟨28260894403741095866352035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18840596269160730577568023 28260894403741095866352035)
                  ·
                    refine ⟨42391341605611643799528053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28260894403741095866352035 42391341605611643799528053)
                    ·
                      refine ⟨3974188275526091606205755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42391341605611643799528053 3974188275526091606205755)
                      ·
                        rfl

theorem cell23_7739704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_7739704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739704 prefixEnd_7739704 := by exact prefixLift 7739704
  have htrace : WordTrace (prefixWord ++ tailWord_7739704) baseStart_7739704 baseEnd_7739704 := by
    simpa [prefixWord, tailWord_7739704, baseEnd_7739704] using wordTrace_append hprefix tailTrace_7739704
  have hstable : (prefixWord ++ tailWord_7739704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739704).length < 2 ^ (prefixWord ++ tailWord_7739704).sum := by decide
  have hdescent : baseEnd_7739704 < baseStart_7739704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739711 : List Nat := [1, 1, 2, 2, 4, 1, 3, 3, 2, 4]
def baseStart_7739711 : Nat := 118140960795 + 7739711 * 2 ^ 59
def prefixEnd_7739711 : Nat := 4983230072969 + 3 ^ 40 * 7739711 * 2
def baseEnd_7739711 : Nat := 1324730623296891026272741

theorem tailTrace_7739711 : CollatzResearch.WordTrace tailWord_7739711 prefixEnd_7739711 1324730623296891026272741 := by
  unfold tailWord_7739711
  simp only [CollatzResearch.WordTrace]
  refine ⟨282290451263356359247058987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188193634175570906164705991 282290451263356359247058987)
  ·
    refine ⟨423435676895034538870588481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282290451263356359247058987 423435676895034538870588481)
    ·
      refine ⟨317576757671275904152941361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423435676895034538870588481 317576757671275904152941361)
      ·
        refine ⟨238182568253456928114706021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317576757671275904152941361 238182568253456928114706021)
        ·
          refine ⟨44659231547523174021507379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238182568253456928114706021 44659231547523174021507379)
          ·
            refine ⟨66988847321284761032261069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44659231547523174021507379 66988847321284761032261069)
            ·
              refine ⟨25120817745481785387097901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66988847321284761032261069 25120817745481785387097901)
              ·
                refine ⟨9420306654555669520161713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25120817745481785387097901 9420306654555669520161713)
                ·
                  refine ⟨7065229990916752140121285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420306654555669520161713 7065229990916752140121285)
                  ·
                    refine ⟨1324730623296891026272741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065229990916752140121285 1324730623296891026272741)
                    ·
                      rfl

theorem cell23_7739711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_7739711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739711 prefixEnd_7739711 := by exact prefixLift 7739711
  have htrace : WordTrace (prefixWord ++ tailWord_7739711) baseStart_7739711 baseEnd_7739711 := by
    simpa [prefixWord, tailWord_7739711, baseEnd_7739711] using wordTrace_append hprefix tailTrace_7739711
  have hstable : (prefixWord ++ tailWord_7739711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739711).length < 2 ^ (prefixWord ++ tailWord_7739711).sum := by decide
  have hdescent : baseEnd_7739711 < baseStart_7739711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739735 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 1, 2, 2]
def baseStart_7739735 : Nat := 118140960795 + 7739735 * 2 ^ 59
def prefixEnd_7739735 : Nat := 4983230072969 + 3 ^ 40 * 7739735 * 2
def baseEnd_7739735 : Nat := 3974204193426380984918113

theorem tailTrace_7739735 : CollatzResearch.WordTrace tailWord_7739735 prefixEnd_7739735 3974204193426380984918113 := by
  unfold tailWord_7739735
  simp only [CollatzResearch.WordTrace]
  refine ⟨282291326615269411345932659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188194217743512940897288439 282291326615269411345932659)
  ·
    refine ⟨423436989922904117018898989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282291326615269411345932659 423436989922904117018898989)
    ·
      refine ⟨158788871221089043882087121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423436989922904117018898989 158788871221089043882087121)
      ·
        refine ⟨119091653415816782911565341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158788871221089043882087121 119091653415816782911565341)
        ·
          refine ⟨44659370030931293591837003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119091653415816782911565341 44659370030931293591837003)
          ·
            refine ⟨66989055046396940387755505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44659370030931293591837003 66989055046396940387755505)
            ·
              refine ⟨50241791284797705290816629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66989055046396940387755505 50241791284797705290816629)
              ·
                refine ⟨4710167932949784871014059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50241791284797705290816629 4710167932949784871014059)
                ·
                  refine ⟨7065251899424677306521089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710167932949784871014059 7065251899424677306521089)
                  ·
                    refine ⟨5298938924568507979890817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065251899424677306521089 5298938924568507979890817)
                    ·
                      refine ⟨3974204193426380984918113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298938924568507979890817 3974204193426380984918113)
                      ·
                        rfl

theorem cell23_7739735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_7739735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739735 prefixEnd_7739735 := by exact prefixLift 7739735
  have htrace : WordTrace (prefixWord ++ tailWord_7739735) baseStart_7739735 baseEnd_7739735 := by
    simpa [prefixWord, tailWord_7739735, baseEnd_7739735] using wordTrace_append hprefix tailTrace_7739735
  have hstable : (prefixWord ++ tailWord_7739735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739735).length < 2 ^ (prefixWord ++ tailWord_7739735).sum := by decide
  have hdescent : baseEnd_7739735 < baseStart_7739735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739752 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7739752 : Nat := 118140960795 + 7739752 * 2 ^ 59
def prefixEnd_7739752 : Nat := 4983230072969 + 3 ^ 40 * 7739752 * 2
def baseEnd_7739752 : Nat := 3974212922597507418405535

theorem tailTrace_7739752 : CollatzResearch.WordTrace tailWord_7739752 prefixEnd_7739752 3974212922597507418405535 := by
  unfold tailWord_7739752
  simp only [CollatzResearch.WordTrace]
  refine ⟨141145973328103911624650755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188194631104138548832867673 141145973328103911624650755)
  ·
    refine ⟨211718959992155867436976133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141145973328103911624650755 211718959992155867436976133)
    ·
      refine ⟨39697304998529225144433025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 211718959992155867436976133 39697304998529225144433025)
      ·
        refine ⟨29772978748896918858324769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39697304998529225144433025 29772978748896918858324769)
        ·
          refine ⟨22329734061672689143743577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29772978748896918858324769 22329734061672689143743577)
          ·
            refine ⟨16747300546254516857807683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22329734061672689143743577 16747300546254516857807683)
            ·
              refine ⟨25120950819381775286711525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747300546254516857807683 25120950819381775286711525)
              ·
                refine ⟨4710178278634082866258411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25120950819381775286711525 4710178278634082866258411)
                ·
                  refine ⟨7065267417951124299387617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710178278634082866258411 7065267417951124299387617)
                  ·
                    refine ⟨5298950563463343224540713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065267417951124299387617 5298950563463343224540713)
                    ·
                      refine ⟨3974212922597507418405535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5298950563463343224540713 3974212922597507418405535)
                      ·
                        rfl

theorem cell23_7739752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7739752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739752 prefixEnd_7739752 := by exact prefixLift 7739752
  have htrace : WordTrace (prefixWord ++ tailWord_7739752) baseStart_7739752 baseEnd_7739752 := by
    simpa [prefixWord, tailWord_7739752, baseEnd_7739752] using wordTrace_append hprefix tailTrace_7739752
  have hstable : (prefixWord ++ tailWord_7739752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739752).length < 2 ^ (prefixWord ++ tailWord_7739752).sum := by decide
  have hdescent : baseEnd_7739752 < baseStart_7739752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739784 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_7739784 : Nat := 118140960795 + 7739784 * 2 ^ 59
def prefixEnd_7739784 : Nat := 4983230072969 + 3 ^ 40 * 7739784 * 2
def baseEnd_7739784 : Nat := 1324743117992817097735129

theorem tailTrace_7739784 : CollatzResearch.WordTrace tailWord_7739784 prefixEnd_7739784 1324743117992817097735129 := by
  unfold tailWord_7739784
  simp only [CollatzResearch.WordTrace]
  refine ⟨141146556896045946357233203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188195409194727928476310937 141146556896045946357233203)
  ·
    refine ⟨211719835344068919535849805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141146556896045946357233203 211719835344068919535849805)
    ·
      refine ⟨79394938254025844825943677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211719835344068919535849805 79394938254025844825943677)
      ·
        refine ⟨29773101845259691809728879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79394938254025844825943677 29773101845259691809728879)
        ·
          refine ⟨44659652767889537714593319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29773101845259691809728879 44659652767889537714593319)
          ·
            refine ⟨66989479151834306571889979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44659652767889537714593319 66989479151834306571889979)
            ·
              refine ⟨100484218727751459857834969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66989479151834306571889979 100484218727751459857834969)
              ·
                refine ⟨75363164045813594893376227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100484218727751459857834969 75363164045813594893376227)
                ·
                  refine ⟨113044746068720392340064341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75363164045813594893376227 113044746068720392340064341)
                  ·
                    refine ⟨1324743117992817097735129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 113044746068720392340064341 1324743117992817097735129)
                    ·
                      rfl

theorem cell23_7739784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_7739784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739784 prefixEnd_7739784 := by exact prefixLift 7739784
  have htrace : WordTrace (prefixWord ++ tailWord_7739784) baseStart_7739784 baseEnd_7739784 := by
    simpa [prefixWord, tailWord_7739784, baseEnd_7739784] using wordTrace_append hprefix tailTrace_7739784
  have hstable : (prefixWord ++ tailWord_7739784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739784).length < 2 ^ (prefixWord ++ tailWord_7739784).sum := by decide
  have hdescent : baseEnd_7739784 < baseStart_7739784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739825 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 1, 4, 2]
def baseStart_7739825 : Nat := 118140960795 + 7739825 * 2 ^ 59
def prefixEnd_7739825 : Nat := 4983230072969 + 3 ^ 40 * 7739825 * 2
def baseEnd_7739825 : Nat := 3974250406685285632792699

theorem tailTrace_7739825 : CollatzResearch.WordTrace tailWord_7739825 prefixEnd_7739825 3974250406685285632792699 := by
  unfold tailWord_7739825
  simp only [CollatzResearch.WordTrace]
  refine ⟨282294609184943356716708929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188196406123295571144472619 282294609184943356716708929)
  ·
    refine ⟨211720956888707517537531697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282294609184943356716708929 211720956888707517537531697)
    ·
      refine ⟨158790717666530638153148773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211720956888707517537531697 158790717666530638153148773)
      ·
        refine ⟨29773259562474494653715395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158790717666530638153148773 29773259562474494653715395)
        ·
          refine ⟨44659889343711741980573093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29773259562474494653715395 44659889343711741980573093)
          ·
            refine ⟨8373729251945951621357455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44659889343711741980573093 8373729251945951621357455)
            ·
              refine ⟨12560593877918927432036183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373729251945951621357455 12560593877918927432036183)
              ·
                refine ⟨18840890816878391148054275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12560593877918927432036183 18840890816878391148054275)
                ·
                  refine ⟨28261336225317586722081413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18840890816878391148054275 28261336225317586722081413)
                  ·
                    refine ⟨5299000542247047510390265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28261336225317586722081413 5299000542247047510390265)
                    ·
                      refine ⟨3974250406685285632792699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299000542247047510390265 3974250406685285632792699)
                      ·
                        rfl

theorem cell23_7739825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_7739825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739825 prefixEnd_7739825 := by exact prefixLift 7739825
  have htrace : WordTrace (prefixWord ++ tailWord_7739825) baseStart_7739825 baseEnd_7739825 := by
    simpa [prefixWord, tailWord_7739825, baseEnd_7739825] using wordTrace_append hprefix tailTrace_7739825
  have hstable : (prefixWord ++ tailWord_7739825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739825).length < 2 ^ (prefixWord ++ tailWord_7739825).sum := by decide
  have hdescent : baseEnd_7739825 < baseStart_7739825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739848 : List Nat := [2, 1, 3, 1, 3, 2, 3, 3, 5]
def baseStart_7739848 : Nat := 118140960795 + 7739848 * 2 ^ 59
def prefixEnd_7739848 : Nat := 4983230072969 + 3 ^ 40 * 7739848 * 2
def baseEnd_7739848 : Nat := 441584690748926560311677

theorem tailTrace_7739848 : CollatzResearch.WordTrace tailWord_7739848 prefixEnd_7739848 441584690748926560311677 := by
  unfold tailWord_7739848
  simp only [CollatzResearch.WordTrace]
  refine ⟨141147724031930015822398099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188196965375906687763197465 141147724031930015822398099)
  ·
    refine ⟨211721586047895023733597149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141147724031930015822398099 211721586047895023733597149)
    ·
      refine ⟨79395594767960633900098931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211721586047895023733597149 79395594767960633900098931)
      ·
        refine ⟨119093392151940950850148397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79395594767960633900098931 119093392151940950850148397)
        ·
          refine ⟨44660022056977856568805649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119093392151940950850148397 44660022056977856568805649)
          ·
            refine ⟨33495016542733392426604237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44660022056977856568805649 33495016542733392426604237)
            ·
              refine ⟨12560631203525022159976589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33495016542733392426604237 12560631203525022159976589)
              ·
                refine ⟨4710236701321883309991221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560631203525022159976589 4710236701321883309991221)
                ·
                  refine ⟨441584690748926560311677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4710236701321883309991221 441584690748926560311677)
                  ·
                    rfl

theorem cell23_7739848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 5].length) (baseStart_7739848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739848 prefixEnd_7739848 := by exact prefixLift 7739848
  have htrace : WordTrace (prefixWord ++ tailWord_7739848) baseStart_7739848 baseEnd_7739848 := by
    simpa [prefixWord, tailWord_7739848, baseEnd_7739848] using wordTrace_append hprefix tailTrace_7739848
  have hstable : (prefixWord ++ tailWord_7739848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739848).length < 2 ^ (prefixWord ++ tailWord_7739848).sum := by decide
  have hdescent : baseEnd_7739848 < baseStart_7739848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739851 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 1, 7, 2]
def baseStart_7739851 : Nat := 118140960795 + 7739851 * 2 ^ 59
def prefixEnd_7739851 : Nat := 4983230072969 + 3 ^ 40 * 7739851 * 2
def baseEnd_7739851 : Nat := 3974263757182302531067579

theorem tailTrace_7739851 : CollatzResearch.WordTrace tailWord_7739851 prefixEnd_7739851 3974263757182302531067579 := by
  unfold tailWord_7739851
  simp only [CollatzResearch.WordTrace]
  refine ⟨282295557482849163157155407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188197038321899442104770271 282295557482849163157155407)
  ·
    refine ⟨423443336224273744735733111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282295557482849163157155407 423443336224273744735733111)
    ·
      refine ⟨635165004336410617103599667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423443336224273744735733111 635165004336410617103599667)
      ·
        refine ⟨952747506504615925655399501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635165004336410617103599667 952747506504615925655399501)
        ·
          refine ⟨357280314939230972120774813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952747506504615925655399501 357280314939230972120774813)
          ·
            refine ⟨133980118102211614545290555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357280314939230972120774813 133980118102211614545290555)
            ·
              refine ⟨200970177153317421817935833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133980118102211614545290555 200970177153317421817935833)
              ·
                refine ⟨150727632864988066363451875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200970177153317421817935833 150727632864988066363451875)
                ·
                  refine ⟨226091449297482099545177813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150727632864988066363451875 226091449297482099545177813)
                  ·
                    refine ⟨5299018342909736708090105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 226091449297482099545177813 5299018342909736708090105)
                    ·
                      refine ⟨3974263757182302531067579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299018342909736708090105 3974263757182302531067579)
                      ·
                        rfl

theorem cell23_7739851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 7, 2].length) (baseStart_7739851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739851 prefixEnd_7739851 := by exact prefixLift 7739851
  have htrace : WordTrace (prefixWord ++ tailWord_7739851) baseStart_7739851 baseEnd_7739851 := by
    simpa [prefixWord, tailWord_7739851, baseEnd_7739851] using wordTrace_append hprefix tailTrace_7739851
  have hstable : (prefixWord ++ tailWord_7739851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739851).length < 2 ^ (prefixWord ++ tailWord_7739851).sum := by decide
  have hdescent : baseEnd_7739851 < baseStart_7739851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739861 : List Nat := [1, 3, 2, 3, 1, 2, 1, 1, 4, 5]
def baseStart_7739861 : Nat := 118140960795 + 7739861 * 2 ^ 59
def prefixEnd_7739861 : Nat := 4983230072969 + 3 ^ 40 * 7739861 * 2
def baseEnd_7739861 : Nat := 1324756297329615830647511

theorem tailTrace_7739861 : CollatzResearch.WordTrace tailWord_7739861 prefixEnd_7739861 1324756297329615830647511 := by
  unfold tailWord_7739861
  simp only [CollatzResearch.WordTrace]
  refine ⟨282295922212812934865019437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188197281475208623243346291 282295922212812934865019437)
  ·
    refine ⟨105860970829804850574382289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282295922212812934865019437 105860970829804850574382289)
    ·
      refine ⟨79395728122353637930786717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105860970829804850574382289 79395728122353637930786717)
      ·
        refine ⟨29773398045882614224045019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79395728122353637930786717 29773398045882614224045019)
        ·
          refine ⟨44660097068823921336067529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29773398045882614224045019 44660097068823921336067529)
          ·
            refine ⟨33495072801617941002050647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44660097068823921336067529 33495072801617941002050647)
            ·
              refine ⟨50242609202426911503075971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33495072801617941002050647 50242609202426911503075971)
              ·
                refine ⟨75363913803640367254613957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50242609202426911503075971 75363913803640367254613957)
                ·
                  refine ⟨14130733838182568860240117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75363913803640367254613957 14130733838182568860240117)
                  ·
                    refine ⟨1324756297329615830647511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14130733838182568860240117 1324756297329615830647511)
                    ·
                      rfl

theorem cell23_7739861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_7739861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739861 prefixEnd_7739861 := by exact prefixLift 7739861
  have htrace : WordTrace (prefixWord ++ tailWord_7739861) baseStart_7739861 baseEnd_7739861 := by
    simpa [prefixWord, tailWord_7739861, baseEnd_7739861] using wordTrace_append hprefix tailTrace_7739861
  have hstable : (prefixWord ++ tailWord_7739861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739861).length < 2 ^ (prefixWord ++ tailWord_7739861).sum := by decide
  have hdescent : baseEnd_7739861 < baseStart_7739861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739871 : List Nat := [1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_7739871 : Nat := 118140960795 + 7739871 * 2 ^ 59
def prefixEnd_7739871 : Nat := 4983230072969 + 3 ^ 40 * 7739871 * 2
def baseEnd_7739871 : Nat := 3974274026795392452817487

theorem tailTrace_7739871 : CollatzResearch.WordTrace tailWord_7739871 prefixEnd_7739871 3974274026795392452817487 := by
  unfold tailWord_7739871
  simp only [CollatzResearch.WordTrace]
  refine ⟨282296286942776706572883467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188197524628517804381922311 282296286942776706572883467)
  ·
    refine ⟨423444430414165059859325201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282296286942776706572883467 423444430414165059859325201)
    ·
      refine ⟨317583322810623794894493901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423444430414165059859325201 317583322810623794894493901)
      ·
        refine ⟨119093746053983923085435213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317583322810623794894493901 119093746053983923085435213)
        ·
          refine ⟨44660154770243971157038205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119093746053983923085435213 44660154770243971157038205)
          ·
            refine ⟨16747558038841489183889327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44660154770243971157038205 16747558038841489183889327)
            ·
              refine ⟨25121337058262233775833991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747558038841489183889327 25121337058262233775833991)
              ·
                refine ⟨37682005587393350663750987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25121337058262233775833991 37682005587393350663750987)
                ·
                  refine ⟨56523008381090025995626481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37682005587393350663750987 56523008381090025995626481)
                  ·
                    refine ⟨42392256285817519496719861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56523008381090025995626481 42392256285817519496719861)
                    ·
                      refine ⟨3974274026795392452817487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42392256285817519496719861 3974274026795392452817487)
                      ·
                        rfl

theorem cell23_7739871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_7739871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739871 prefixEnd_7739871 := by exact prefixLift 7739871
  have htrace : WordTrace (prefixWord ++ tailWord_7739871) baseStart_7739871 baseEnd_7739871 := by
    simpa [prefixWord, tailWord_7739871, baseEnd_7739871] using wordTrace_append hprefix tailTrace_7739871
  have hstable : (prefixWord ++ tailWord_7739871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739871).length < 2 ^ (prefixWord ++ tailWord_7739871).sum := by decide
  have hdescent : baseEnd_7739871 < baseStart_7739871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739891 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 5, 4]
def baseStart_7739891 : Nat := 118140960795 + 7739891 * 2 ^ 59
def prefixEnd_7739891 : Nat := 4983230072969 + 3 ^ 40 * 7739891 * 2
def baseEnd_7739891 : Nat := 1324761432136160791522465

theorem tailTrace_7739891 : CollatzResearch.WordTrace tailWord_7739891 prefixEnd_7739891 1324761432136160791522465 := by
  unfold tailWord_7739891
  simp only [CollatzResearch.WordTrace]
  refine ⟨282297016402704249988611527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188198010935136166659074351 282297016402704249988611527)
  ·
    refine ⟨423445524604056374982917291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282297016402704249988611527 423445524604056374982917291)
    ·
      refine ⟨635168286906084562474375937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423445524604056374982917291 635168286906084562474375937)
      ·
        refine ⟨476376215179563421855781953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635168286906084562474375937 476376215179563421855781953)
        ·
          refine ⟨357282161384672566391836465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476376215179563421855781953 357282161384672566391836465)
          ·
            refine ⟨267961621038504424793877349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357282161384672566391836465 267961621038504424793877349)
            ·
              refine ⟨50242803944719579648852003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267961621038504424793877349 50242803944719579648852003)
              ·
                refine ⟨75364205917079369473278005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50242803944719579648852003 75364205917079369473278005)
                ·
                  refine ⟨7065394304726190888119813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75364205917079369473278005 7065394304726190888119813)
                  ·
                    refine ⟨1324761432136160791522465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065394304726190888119813 1324761432136160791522465)
                    ·
                      rfl

theorem cell23_7739891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 4].length) (baseStart_7739891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739891 prefixEnd_7739891 := by exact prefixLift 7739891
  have htrace : WordTrace (prefixWord ++ tailWord_7739891) baseStart_7739891 baseEnd_7739891 := by
    simpa [prefixWord, tailWord_7739891, baseEnd_7739891] using wordTrace_append hprefix tailTrace_7739891
  have hstable : (prefixWord ++ tailWord_7739891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739891).length < 2 ^ (prefixWord ++ tailWord_7739891).sum := by decide
  have hdescent : baseEnd_7739891 < baseStart_7739891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739925 : List Nat := [1, 3, 2, 1, 3, 1, 3, 4, 1, 4]
def baseStart_7739925 : Nat := 118140960795 + 7739925 * 2 ^ 59
def prefixEnd_7739925 : Nat := 4983230072969 + 3 ^ 40 * 7739925 * 2
def baseEnd_7739925 : Nat := 1324767251583578413847413

theorem tailTrace_7739925 : CollatzResearch.WordTrace tailWord_7739925 prefixEnd_7739925 1324767251583578413847413 := by
  unfold tailWord_7739925
  simp only [CollatzResearch.WordTrace]
  refine ⟨282298256484581073795349229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188198837656387382530232819 282298256484581073795349229)
  ·
    refine ⟨105861846181717902673255961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282298256484581073795349229 105861846181717902673255961)
    ·
      refine ⟨79396384636288427004941971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105861846181717902673255961 79396384636288427004941971)
      ·
        refine ⟨119094576954432640507412957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79396384636288427004941971 119094576954432640507412957)
        ·
          refine ⟨44660466357912240190279859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119094576954432640507412957 44660466357912240190279859)
          ·
            refine ⟨66990699536868360285419789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44660466357912240190279859 66990699536868360285419789)
            ·
              refine ⟨25121512326325635107032421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66990699536868360285419789 25121512326325635107032421)
              ·
                refine ⟨4710283561186056582568579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25121512326325635107032421 4710283561186056582568579)
                ·
                  refine ⟨7065425341779084873852869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710283561186056582568579 7065425341779084873852869)
                  ·
                    refine ⟨1324767251583578413847413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065425341779084873852869 1324767251583578413847413)
                    ·
                      rfl

theorem cell23_7739925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_7739925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739925 prefixEnd_7739925 := by exact prefixLift 7739925
  have htrace : WordTrace (prefixWord ++ tailWord_7739925) baseStart_7739925 baseEnd_7739925 := by
    simpa [prefixWord, tailWord_7739925, baseEnd_7739925] using wordTrace_append hprefix tailTrace_7739925
  have hstable : (prefixWord ++ tailWord_7739925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739925).length < 2 ^ (prefixWord ++ tailWord_7739925).sum := by decide
  have hdescent : baseEnd_7739925 < baseStart_7739925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739972 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 8]
def baseStart_7739972 : Nat := 118140960795 + 7739972 * 2 ^ 59
def prefixEnd_7739972 : Nat := 4983230072969 + 3 ^ 40 * 7739972 * 2
def baseEnd_7739972 : Nat := 441591765371277395294947

theorem tailTrace_7739972 : CollatzResearch.WordTrace tailWord_7739972 prefixEnd_7739972 441591765371277395294947 := by
  unfold tailWord_7739972
  simp only [CollatzResearch.WordTrace]
  refine ⟨141149985357705400411155085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188199980476940533881540113 141149985357705400411155085)
  ·
    refine ⟨52931244509139525154183157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141149985357705400411155085 52931244509139525154183157)
    ·
      refine ⟨4962304172731830483204671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52931244509139525154183157 4962304172731830483204671)
      ·
        refine ⟨7443456259097745724807007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962304172731830483204671 7443456259097745724807007)
        ·
          refine ⟨11165184388646618587210511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7443456259097745724807007 11165184388646618587210511)
          ·
            refine ⟨16747776582969927880815767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11165184388646618587210511 16747776582969927880815767)
            ·
              refine ⟨25121664874454891821223651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16747776582969927880815767 25121664874454891821223651)
              ·
                refine ⟨37682497311682337731835477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25121664874454891821223651 37682497311682337731835477)
                ·
                  refine ⟨441591765371277395294947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37682497311682337731835477 441591765371277395294947)
                  ·
                    rfl

theorem cell23_7739972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_7739972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739972 prefixEnd_7739972 := by exact prefixLift 7739972
  have htrace : WordTrace (prefixWord ++ tailWord_7739972) baseStart_7739972 baseEnd_7739972 := by
    simpa [prefixWord, tailWord_7739972, baseEnd_7739972] using wordTrace_append hprefix tailTrace_7739972
  have hstable : (prefixWord ++ tailWord_7739972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739972).length < 2 ^ (prefixWord ++ tailWord_7739972).sum := by decide
  have hdescent : baseEnd_7739972 < baseStart_7739972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7739982 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_7739982 : Nat := 118140960795 + 7739982 * 2 ^ 59
def prefixEnd_7739982 : Nat := 4983230072969 + 3 ^ 40 * 7739982 * 2
def baseEnd_7739982 : Nat := 3974331023148041518529477

theorem tailTrace_7739982 : CollatzResearch.WordTrace tailWord_7739982 prefixEnd_7739982 3974331023148041518529477 := by
  unfold tailWord_7739982
  simp only [CollatzResearch.WordTrace]
  refine ⟨35287541930671821566271775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188200223630249715020116133 35287541930671821566271775)
  ·
    refine ⟨52931312896007732349407663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35287541930671821566271775 52931312896007732349407663)
    ·
      refine ⟨79396969344011598524111495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52931312896007732349407663 79396969344011598524111495)
      ·
        refine ⟨119095454016017397786167243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79396969344011598524111495 119095454016017397786167243)
        ·
          refine ⟨178643181024026096679250865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119095454016017397786167243 178643181024026096679250865)
          ·
            refine ⟨133982385768019572509438149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178643181024026096679250865 133982385768019572509438149)
            ·
              refine ⟨25121697331503669845519653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133982385768019572509438149 25121697331503669845519653)
              ·
                refine ⟨4710318249656938096034935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25121697331503669845519653 4710318249656938096034935)
                ·
                  refine ⟨7065477374485407144052403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710318249656938096034935 7065477374485407144052403)
                  ·
                    refine ⟨10598216061728110716078605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065477374485407144052403 10598216061728110716078605)
                    ·
                      refine ⟨3974331023148041518529477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598216061728110716078605 3974331023148041518529477)
                      ·
                        rfl

theorem cell23_7739982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_7739982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7739982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7739982 prefixEnd_7739982 := by exact prefixLift 7739982
  have htrace : WordTrace (prefixWord ++ tailWord_7739982) baseStart_7739982 baseEnd_7739982 := by
    simpa [prefixWord, tailWord_7739982, baseEnd_7739982] using wordTrace_append hprefix tailTrace_7739982
  have hstable : (prefixWord ++ tailWord_7739982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7739982).length < 2 ^ (prefixWord ++ tailWord_7739982).sum := by decide
  have hdescent : baseEnd_7739982 < baseStart_7739982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7739982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740016 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 1, 1, 3]
def baseStart_7740016 : Nat := 118140960795 + 7740016 * 2 ^ 59
def prefixEnd_7740016 : Nat := 4983230072969 + 3 ^ 40 * 7740016 * 2
def baseEnd_7740016 : Nat := 3974348481490294385504321

theorem tailTrace_7740016 : CollatzResearch.WordTrace tailWord_7740016 prefixEnd_7740016 3974348481490294385504321 := by
  unfold tailWord_7740016
  simp only [CollatzResearch.WordTrace]
  refine ⟨141150787763625698168455951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188201050351500930891274601 141150787763625698168455951)
  ·
    refine ⟨211726181645438547252683927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141150787763625698168455951 211726181645438547252683927)
    ·
      refine ⟨317589272468157820879025891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211726181645438547252683927 317589272468157820879025891)
      ·
        refine ⟨476383908702236731318538837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317589272468157820879025891 476383908702236731318538837)
        ·
          refine ⟨5582623930104336695139127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 476383908702236731318538837 5582623930104336695139127)
          ·
            refine ⟨8373935895156505042708691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582623930104336695139127 8373935895156505042708691)
            ·
              refine ⟨12560903842734757564063037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8373935895156505042708691 12560903842734757564063037)
              ·
                refine ⟨4710338941025534086523639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12560903842734757564063037 4710338941025534086523639)
                ·
                  refine ⟨7065508411538301129785459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710338941025534086523639 7065508411538301129785459)
                  ·
                    refine ⟨10598262617307451694678189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065508411538301129785459 10598262617307451694678189)
                    ·
                      refine ⟨3974348481490294385504321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598262617307451694678189 3974348481490294385504321)
                      ·
                        rfl

theorem cell23_7740016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 1, 1, 3].length) (baseStart_7740016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740016 prefixEnd_7740016 := by exact prefixLift 7740016
  have htrace : WordTrace (prefixWord ++ tailWord_7740016) baseStart_7740016 baseEnd_7740016 := by
    simpa [prefixWord, tailWord_7740016, baseEnd_7740016] using wordTrace_append hprefix tailTrace_7740016
  have hstable : (prefixWord ++ tailWord_7740016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740016).length < 2 ^ (prefixWord ++ tailWord_7740016).sum := by decide
  have hdescent : baseEnd_7740016 < baseStart_7740016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740025 : List Nat := [1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 3]
def baseStart_7740025 : Nat := 118140960795 + 7740025 * 2 ^ 59
def prefixEnd_7740025 : Nat := 4983230072969 + 3 ^ 40 * 7740025 * 2
def baseEnd_7740025 : Nat := 3974353102816184850291779

theorem tailTrace_7740025 : CollatzResearch.WordTrace tailWord_7740025 prefixEnd_7740025 3974353102816184850291779 := by
  unfold tailWord_7740025
  simp only [CollatzResearch.WordTrace]
  refine ⟨282301903784218790873989529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188201269189479193915993019 282301903784218790873989529)
  ·
    refine ⟨211726427838164093155492147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282301903784218790873989529 211726427838164093155492147)
    ·
      refine ⟨317589641757246139733238221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211726427838164093155492147 317589641757246139733238221)
      ·
        refine ⟨119096115658967302399964333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317589641757246139733238221 119096115658967302399964333)
        ·
          refine ⟨44661043372112738399986625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119096115658967302399964333 44661043372112738399986625)
          ·
            refine ⟨33495782529084553799989969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44661043372112738399986625 33495782529084553799989969)
            ·
              refine ⟨25121836896813415349992477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33495782529084553799989969 25121836896813415349992477)
              ·
                refine ⟨9420688836305030756247179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25121836896813415349992477 9420688836305030756247179)
                ·
                  refine ⟨14131033254457546134370769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9420688836305030756247179 14131033254457546134370769)
                  ·
                    refine ⟨10598274940843159600778077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14131033254457546134370769 10598274940843159600778077)
                    ·
                      refine ⟨3974353102816184850291779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598274940843159600778077 3974353102816184850291779)
                      ·
                        rfl

theorem cell23_7740025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_7740025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740025 prefixEnd_7740025 := by exact prefixLift 7740025
  have htrace : WordTrace (prefixWord ++ tailWord_7740025) baseStart_7740025 baseEnd_7740025 := by
    simpa [prefixWord, tailWord_7740025, baseEnd_7740025] using wordTrace_append hprefix tailTrace_7740025
  have hstable : (prefixWord ++ tailWord_7740025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740025).length < 2 ^ (prefixWord ++ tailWord_7740025).sum := by decide
  have hdescent : baseEnd_7740025 < baseStart_7740025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740041 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 2, 7]
def baseStart_7740041 : Nat := 118140960795 + 7740041 * 2 ^ 59
def prefixEnd_7740041 : Nat := 4983230072969 + 3 ^ 40 * 7740041 * 2
def baseEnd_7740041 : Nat := 1324787106168885595897235

theorem tailTrace_7740041 : CollatzResearch.WordTrace tailWord_7740041 prefixEnd_7740041 1324787106168885595897235 := by
  unfold tailWord_7740041
  simp only [CollatzResearch.WordTrace]
  refine ⟨282302487352160825606571977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188201658234773883737714651 282302487352160825606571977)
  ·
    refine ⟨211726865514120619204928983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282302487352160825606571977 211726865514120619204928983)
    ·
      refine ⟨317590298271180928807393475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211726865514120619204928983 317590298271180928807393475)
      ·
        refine ⟨476385447406771393211090213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317590298271180928807393475 476385447406771393211090213)
        ·
          refine ⟨89322271388769636227079415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476385447406771393211090213 89322271388769636227079415)
          ·
            refine ⟨133983407083154454340619123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89322271388769636227079415 133983407083154454340619123)
            ·
              refine ⟨200975110624731681510928685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133983407083154454340619123 200975110624731681510928685)
              ·
                refine ⟨75365666484274380566598257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 200975110624731681510928685 75365666484274380566598257)
                ·
                  refine ⟨56524249863205785424948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75365666484274380566598257 56524249863205785424948693)
                  ·
                    refine ⟨1324787106168885595897235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56524249863205785424948693 1324787106168885595897235)
                    ·
                      rfl

theorem cell23_7740041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_7740041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740041 prefixEnd_7740041 := by exact prefixLift 7740041
  have htrace : WordTrace (prefixWord ++ tailWord_7740041) baseStart_7740041 baseEnd_7740041 := by
    simpa [prefixWord, tailWord_7740041, baseEnd_7740041] using wordTrace_append hprefix tailTrace_7740041
  have hstable : (prefixWord ++ tailWord_7740041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740041).length < 2 ^ (prefixWord ++ tailWord_7740041).sum := by decide
  have hdescent : baseEnd_7740041 < baseStart_7740041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740048 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2]
def baseStart_7740048 : Nat := 118140960795 + 7740048 * 2 ^ 59
def prefixEnd_7740048 : Nat := 4983230072969 + 3 ^ 40 * 7740048 * 2
def baseEnd_7740048 : Nat := 3974364912871238260304173

theorem tailTrace_7740048 : CollatzResearch.WordTrace tailWord_7740048 prefixEnd_7740048 3974364912871238260304173 := by
  unfold tailWord_7740048
  simp only [CollatzResearch.WordTrace]
  refine ⟨141151371331567732901038399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188201828442090310534717865 141151371331567732901038399)
  ·
    refine ⟨211727056997351599351557599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141151371331567732901038399 211727056997351599351557599)
    ·
      refine ⟨317590585496027399027336399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211727056997351599351557599 317590585496027399027336399)
      ·
        refine ⟨476385878244041098541004599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317590585496027399027336399 476385878244041098541004599)
        ·
          refine ⟨714578817366061647811506899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476385878244041098541004599 714578817366061647811506899)
          ·
            refine ⟨1071868226049092471717260349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714578817366061647811506899 1071868226049092471717260349)
            ·
              refine ⟨401950584768409676893972631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071868226049092471717260349 401950584768409676893972631)
              ·
                refine ⟨602925877152614515340958947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401950584768409676893972631 602925877152614515340958947)
                ·
                  refine ⟨904388815728921773011438421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602925877152614515340958947 904388815728921773011438421)
                  ·
                    refine ⟨5299153217161651013738897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 904388815728921773011438421 5299153217161651013738897)
                    ·
                      refine ⟨3974364912871238260304173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299153217161651013738897 3974364912871238260304173)
                      ·
                        rfl

theorem cell23_7740048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 9, 2].length) (baseStart_7740048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740048 prefixEnd_7740048 := by exact prefixLift 7740048
  have htrace : WordTrace (prefixWord ++ tailWord_7740048) baseStart_7740048 baseEnd_7740048 := by
    simpa [prefixWord, tailWord_7740048, baseEnd_7740048] using wordTrace_append hprefix tailTrace_7740048
  have hstable : (prefixWord ++ tailWord_7740048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740048).length < 2 ^ (prefixWord ++ tailWord_7740048).sum := by decide
  have hdescent : baseEnd_7740048 < baseStart_7740048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740051 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_7740051 : Nat := 118140960795 + 7740051 * 2 ^ 59
def prefixEnd_7740051 : Nat := 4983230072969 + 3 ^ 40 * 7740051 * 2
def baseEnd_7740051 : Nat := 3974366453313201748566659

theorem tailTrace_7740051 : CollatzResearch.WordTrace tailWord_7740051 prefixEnd_7740051 3974366453313201748566659 := by
  unfold tailWord_7740051
  simp only [CollatzResearch.WordTrace]
  refine ⟨282302852082124597314436007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188201901388083064876290671 282302852082124597314436007)
  ·
    refine ⟨423454278123186895971654011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282302852082124597314436007 423454278123186895971654011)
    ·
      refine ⟨635181417184780343957481017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423454278123186895971654011 635181417184780343957481017)
      ·
        refine ⟨476386062888585257968110763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635181417184780343957481017 476386062888585257968110763)
        ·
          refine ⟨714579094332877886952166145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476386062888585257968110763 714579094332877886952166145)
          ·
            refine ⟨535934320749658415214124609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714579094332877886952166145 535934320749658415214124609)
            ·
              refine ⟨401950740562243811410593457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535934320749658415214124609 401950740562243811410593457)
              ·
                refine ⟨301463055421682858557945093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401950740562243811410593457 301463055421682858557945093)
                ·
                  refine ⟨56524322891565535979614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 301463055421682858557945093 56524322891565535979614705)
                  ·
                    refine ⟨42393242168674151984711029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56524322891565535979614705 42393242168674151984711029)
                    ·
                      refine ⟨3974366453313201748566659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42393242168674151984711029 3974366453313201748566659)
                      ·
                        rfl

theorem cell23_7740051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_7740051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740051 prefixEnd_7740051 := by exact prefixLift 7740051
  have htrace : WordTrace (prefixWord ++ tailWord_7740051) baseStart_7740051 baseEnd_7740051 := by
    simpa [prefixWord, tailWord_7740051, baseEnd_7740051] using wordTrace_append hprefix tailTrace_7740051
  have hstable : (prefixWord ++ tailWord_7740051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740051).length < 2 ^ (prefixWord ++ tailWord_7740051).sum := by decide
  have hdescent : baseEnd_7740051 < baseStart_7740051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740091 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_7740091 : Nat := 118140960795 + 7740091 * 2 ^ 59
def prefixEnd_7740091 : Nat := 4983230072969 + 3 ^ 40 * 7740091 * 2
def baseEnd_7740091 : Nat := 3974386992539381592066475

theorem tailTrace_7740091 : CollatzResearch.WordTrace tailWord_7740091 prefixEnd_7740091 3974386992539381592066475 := by
  unfold tailWord_7740091
  simp only [CollatzResearch.WordTrace]
  refine ⟨282304311001979684145892127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188202874001319789430594751 282304311001979684145892127)
  ·
    refine ⟨423456466502969526218838191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282304311001979684145892127 423456466502969526218838191)
    ·
      refine ⟨635184699754454289328257287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423456466502969526218838191 635184699754454289328257287)
      ·
        refine ⟨952777049631681433992385931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635184699754454289328257287 952777049631681433992385931)
        ·
          refine ⟨1429165574447522150988578897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952777049631681433992385931 1429165574447522150988578897)
          ·
            refine ⟨1071874180835641613241434173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429165574447522150988578897 1071874180835641613241434173)
            ·
              refine ⟨401952817813365604965537815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071874180835641613241434173 401952817813365604965537815)
              ·
                refine ⟨602929226720048407448306723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401952817813365604965537815 602929226720048407448306723)
                ·
                  refine ⟨904393840080072611172460085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602929226720048407448306723 904393840080072611172460085)
                  ·
                    refine ⟨84786922507506807297418133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 904393840080072611172460085 84786922507506807297418133)
                    ·
                      refine ⟨3974386992539381592066475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84786922507506807297418133 3974386992539381592066475)
                      ·
                        rfl

theorem cell23_7740091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_7740091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740091 prefixEnd_7740091 := by exact prefixLift 7740091
  have htrace : WordTrace (prefixWord ++ tailWord_7740091) baseStart_7740091 baseEnd_7740091 := by
    simpa [prefixWord, tailWord_7740091, baseEnd_7740091] using wordTrace_append hprefix tailTrace_7740091
  have hstable : (prefixWord ++ tailWord_7740091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740091).length < 2 ^ (prefixWord ++ tailWord_7740091).sum := by decide
  have hdescent : baseEnd_7740091 < baseStart_7740091 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740128 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_7740128 : Nat := 118140960795 + 7740128 * 2 ^ 59
def prefixEnd_7740128 : Nat := 4983230072969 + 3 ^ 40 * 7740128 * 2
def baseEnd_7740128 : Nat := 3974405991323597947303805

theorem tailTrace_7740128 : CollatzResearch.WordTrace tailWord_7740128 prefixEnd_7740128 3974405991323597947303805 := by
  unfold tailWord_7740128
  simp only [CollatzResearch.WordTrace]
  refine ⟨141152830251422819732494519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188203773668563759643326025 141152830251422819732494519)
  ·
    refine ⟨211729245377134229598741779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141152830251422819732494519 211729245377134229598741779)
    ·
      refine ⟨317593868065701344398112669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211729245377134229598741779 317593868065701344398112669)
      ·
        refine ⟨119097700524638004149292251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317593868065701344398112669 119097700524638004149292251)
        ·
          refine ⟨178646550786957006223938377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119097700524638004149292251 178646550786957006223938377)
          ·
            refine ⟨133984913090217754667953783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178646550786957006223938377 133984913090217754667953783)
            ·
              refine ⟨200977369635326632001930675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133984913090217754667953783 200977369635326632001930675)
              ·
                refine ⟨301466054452989948002896013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200977369635326632001930675 301466054452989948002896013)
                ·
                  refine ⟨113049770419871230501086005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301466054452989948002896013 113049770419871230501086005)
                  ·
                    refine ⟨10598415976862927859476813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113049770419871230501086005 10598415976862927859476813)
                    ·
                      refine ⟨3974405991323597947303805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598415976862927859476813 3974405991323597947303805)
                      ·
                        rfl

theorem cell23_7740128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_7740128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740128 prefixEnd_7740128 := by exact prefixLift 7740128
  have htrace : WordTrace (prefixWord ++ tailWord_7740128) baseStart_7740128 baseEnd_7740128 := by
    simpa [prefixWord, tailWord_7740128, baseEnd_7740128] using wordTrace_append hprefix tailTrace_7740128
  have hstable : (prefixWord ++ tailWord_7740128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740128).length < 2 ^ (prefixWord ++ tailWord_7740128).sum := by decide
  have hdescent : baseEnd_7740128 < baseStart_7740128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740146 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_7740146 : Nat := 118140960795 + 7740146 * 2 ^ 59
def prefixEnd_7740146 : Nat := 4983230072969 + 3 ^ 40 * 7740146 * 2
def baseEnd_7740146 : Nat := 3974415233975378876878723

theorem tailTrace_7740146 : CollatzResearch.WordTrace tailWord_7740146 prefixEnd_7740146 3974415233975378876878723 := by
  unfold tailWord_7740146
  simp only [CollatzResearch.WordTrace]
  refine ⟨70576579254195107134786073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188204211344520285692762861 70576579254195107134786073)
  ·
    refine ⟨52932434440646330351089555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70576579254195107134786073 52932434440646330351089555)
    ·
      refine ⟨79398651660969495526634333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52932434440646330351089555 79398651660969495526634333)
      ·
        refine ⟨29774494372863560822487875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79398651660969495526634333 29774494372863560822487875)
        ·
          refine ⟨44661741559295341233731813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29774494372863560822487875 44661741559295341233731813)
          ·
            refine ⟨8374076542367876481324715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44661741559295341233731813 8374076542367876481324715)
            ·
              refine ⟨12561114813551814721987073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374076542367876481324715 12561114813551814721987073)
              ·
                refine ⟨9420836110163861041490305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12561114813551814721987073 9420836110163861041490305)
                ·
                  refine ⟨7065627082622895781117729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9420836110163861041490305 7065627082622895781117729)
                  ·
                    refine ⟨5299220311967171835838297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065627082622895781117729 5299220311967171835838297)
                    ·
                      refine ⟨3974415233975378876878723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299220311967171835838297 3974415233975378876878723)
                      ·
                        rfl

theorem cell23_7740146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_7740146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740146 prefixEnd_7740146 := by exact prefixLift 7740146
  have htrace : WordTrace (prefixWord ++ tailWord_7740146) baseStart_7740146 baseEnd_7740146 := by
    simpa [prefixWord, tailWord_7740146, baseEnd_7740146] using wordTrace_append hprefix tailTrace_7740146
  have hstable : (prefixWord ++ tailWord_7740146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740146).length < 2 ^ (prefixWord ++ tailWord_7740146).sum := by decide
  have hdescent : baseEnd_7740146 < baseStart_7740146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740162 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_7740162 : Nat := 118140960795 + 7740162 * 2 ^ 59
def prefixEnd_7740162 : Nat := 4983230072969 + 3 ^ 40 * 7740162 * 2
def baseEnd_7740162 : Nat := 3974423449665850814278649

theorem tailTrace_7740162 : CollatzResearch.WordTrace tailWord_7740162 prefixEnd_7740162 3974423449665850814278649 := by
  unfold tailWord_7740162
  simp only [CollatzResearch.WordTrace]
  refine ⟨70576725146180615817931685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188204600389814975514484493 70576725146180615817931685)
  ·
    refine ⟨13233135964908865465862191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70576725146180615817931685 13233135964908865465862191)
    ·
      refine ⟨19849703947363298198793287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13233135964908865465862191 19849703947363298198793287)
      ·
        refine ⟨29774555921044947298189931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19849703947363298198793287 29774555921044947298189931)
        ·
          refine ⟨44661833881567420947284897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29774555921044947298189931 44661833881567420947284897)
          ·
            refine ⟨33496375411175565710463673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44661833881567420947284897 33496375411175565710463673)
            ·
              refine ⟨25122281558381674282847755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33496375411175565710463673 25122281558381674282847755)
              ·
                refine ⟨37683422337572511424271633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25122281558381674282847755 37683422337572511424271633)
                ·
                  refine ⟨28262566753179383568203725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37683422337572511424271633 28262566753179383568203725)
                  ·
                    refine ⟨10598462532442268838076397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28262566753179383568203725 10598462532442268838076397)
                    ·
                      refine ⟨3974423449665850814278649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598462532442268838076397 3974423449665850814278649)
                      ·
                        rfl

theorem cell23_7740162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_7740162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740162 prefixEnd_7740162 := by exact prefixLift 7740162
  have htrace : WordTrace (prefixWord ++ tailWord_7740162) baseStart_7740162 baseEnd_7740162 := by
    simpa [prefixWord, tailWord_7740162, baseEnd_7740162] using wordTrace_append hprefix tailTrace_7740162
  have hstable : (prefixWord ++ tailWord_7740162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740162).length < 2 ^ (prefixWord ++ tailWord_7740162).sum := by decide
  have hdescent : baseEnd_7740162 < baseStart_7740162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740185 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 4, 4, 2]
def baseStart_7740185 : Nat := 118140960795 + 7740185 * 2 ^ 59
def prefixEnd_7740185 : Nat := 4983230072969 + 3 ^ 40 * 7740185 * 2
def baseEnd_7740185 : Nat := 3974435259720904224291043

theorem tailTrace_7740185 : CollatzResearch.WordTrace tailWord_7740185 prefixEnd_7740185 3974435259720904224291043 := by
  unfold tailWord_7740185
  simp only [CollatzResearch.WordTrace]
  refine ⟨282307739463639138199814009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188205159642426092133209339 282307739463639138199814009)
  ·
    refine ⟨211730804597729353649860507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282307739463639138199814009 211730804597729353649860507)
    ·
      refine ⟨317596206896594030474790761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211730804597729353649860507 317596206896594030474790761)
      ·
        refine ⟨238197155172445522856093071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317596206896594030474790761 238197155172445522856093071)
        ·
          refine ⟨357295732758668284284139607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238197155172445522856093071 357295732758668284284139607)
          ·
            refine ⟨535943599138002426426209411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357295732758668284284139607 535943599138002426426209411)
            ·
              refine ⟨803915398707003639639314117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535943599138002426426209411 803915398707003639639314117)
              ·
                refine ⟨150734137257563182432371397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 803915398707003639639314117 150734137257563182432371397)
                ·
                  refine ⟨28262650735793096706069637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150734137257563182432371397 28262650735793096706069637)
                  ·
                    refine ⟨5299247012961205632388057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28262650735793096706069637 5299247012961205632388057)
                    ·
                      refine ⟨3974435259720904224291043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299247012961205632388057 3974435259720904224291043)
                      ·
                        rfl

theorem cell23_7740185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_7740185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740185 prefixEnd_7740185 := by exact prefixLift 7740185
  have htrace : WordTrace (prefixWord ++ tailWord_7740185) baseStart_7740185 baseEnd_7740185 := by
    simpa [prefixWord, tailWord_7740185, baseEnd_7740185] using wordTrace_append hprefix tailTrace_7740185
  have hstable : (prefixWord ++ tailWord_7740185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740185).length < 2 ^ (prefixWord ++ tailWord_7740185).sum := by decide
  have hdescent : baseEnd_7740185 < baseStart_7740185 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740248 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_7740248 : Nat := 118140960795 + 7740248 * 2 ^ 59
def prefixEnd_7740248 : Nat := 4983230072969 + 3 ^ 40 * 7740248 * 2
def baseEnd_7740248 : Nat := 3974467609002137477803253

theorem tailTrace_7740248 : CollatzResearch.WordTrace tailWord_7740248 prefixEnd_7740248 3974467609002137477803253 := by
  unfold tailWord_7740248
  simp only [CollatzResearch.WordTrace]
  refine ⟨141155018631205449979678699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188206691508273933306238265 141155018631205449979678699)
  ·
    refine ⟨211732527946808174969518049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141155018631205449979678699 211732527946808174969518049)
    ·
      refine ⟨158799395960106131227138537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211732527946808174969518049 158799395960106131227138537)
      ·
        refine ⟨119099546970079598420353903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158799395960106131227138537 119099546970079598420353903)
        ·
          refine ⟨178649320455119397630530855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119099546970079598420353903 178649320455119397630530855)
          ·
            refine ⟨267973980682679096445796283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178649320455119397630530855 267973980682679096445796283)
            ·
              refine ⟨401960971024018644668694425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267973980682679096445796283 401960971024018644668694425)
              ·
                refine ⟨301470728268013983501520819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401960971024018644668694425 301470728268013983501520819)
                ·
                  refine ⟨452206092402020975252281229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 301470728268013983501520819 452206092402020975252281229)
                  ·
                    refine ⟨169577284650757865719605461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 452206092402020975252281229 169577284650757865719605461)
                    ·
                      refine ⟨3974467609002137477803253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169577284650757865719605461 3974467609002137477803253)
                      ·
                        rfl

theorem cell23_7740248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_7740248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740248 prefixEnd_7740248 := by exact prefixLift 7740248
  have htrace : WordTrace (prefixWord ++ tailWord_7740248) baseStart_7740248 baseEnd_7740248 := by
    simpa [prefixWord, tailWord_7740248, baseEnd_7740248] using wordTrace_append hprefix tailTrace_7740248
  have hstable : (prefixWord ++ tailWord_7740248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740248).length < 2 ^ (prefixWord ++ tailWord_7740248).sum := by decide
  have hdescent : baseEnd_7740248 < baseStart_7740248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740275 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4]
def baseStart_7740275 : Nat := 118140960795 + 7740275 * 2 ^ 59
def prefixEnd_7740275 : Nat := 4983230072969 + 3 ^ 40 * 7740275 * 2
def baseEnd_7740275 : Nat := 3974481472979808872165629

theorem tailTrace_7740275 : CollatzResearch.WordTrace tailWord_7740275 prefixEnd_7740275 3974481472979808872165629 := by
  unfold tailWord_7740275
  simp only [CollatzResearch.WordTrace]
  refine ⟨282311022033313083570590279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188207348022208722380393519 282311022033313083570590279)
  ·
    refine ⟨423466533049969625355885419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282311022033313083570590279 423466533049969625355885419)
    ·
      refine ⟨635199799574954438033828129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423466533049969625355885419 635199799574954438033828129)
      ·
        refine ⟨476399849681215828525371097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635199799574954438033828129 476399849681215828525371097)
        ·
          refine ⟨357299887260911871394028323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476399849681215828525371097 357299887260911871394028323)
          ·
            refine ⟨535949830891367807091042485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357299887260911871394028323 535949830891367807091042485)
            ·
              refine ⟨50245296646065731914785233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 535949830891367807091042485 50245296646065731914785233)
              ·
                refine ⟨37683972484549298936088925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50245296646065731914785233 37683972484549298936088925)
                ·
                  refine ⟨14131489681705987101033347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37683972484549298936088925 14131489681705987101033347)
                  ·
                    refine ⟨21197234522558980651550021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14131489681705987101033347 21197234522558980651550021)
                    ·
                      refine ⟨3974481472979808872165629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21197234522558980651550021 3974481472979808872165629)
                      ·
                        rfl

theorem cell23_7740275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_7740275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740275 prefixEnd_7740275 := by exact prefixLift 7740275
  have htrace : WordTrace (prefixWord ++ tailWord_7740275) baseStart_7740275 baseEnd_7740275 := by
    simpa [prefixWord, tailWord_7740275, baseEnd_7740275] using wordTrace_append hprefix tailTrace_7740275
  have hstable : (prefixWord ++ tailWord_7740275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740275).length < 2 ^ (prefixWord ++ tailWord_7740275).sum := by decide
  have hdescent : baseEnd_7740275 < baseStart_7740275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740285 : List Nat := [1, 4, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_7740285 : Nat := 118140960795 + 7740285 * 2 ^ 59
def prefixEnd_7740285 : Nat := 4983230072969 + 3 ^ 40 * 7740285 * 2
def baseEnd_7740285 : Nat := 1324828869262117944346861

theorem tailTrace_7740285 : CollatzResearch.WordTrace tailWord_7740285 prefixEnd_7740285 1324828869262117944346861 := by
  unfold tailWord_7740285
  simp only [CollatzResearch.WordTrace]
  refine ⟨282311386763276855278454309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188207591175517903518969539 282311386763276855278454309)
  ·
    refine ⟨52933385018114410364710183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282311386763276855278454309 52933385018114410364710183)
    ·
      refine ⟨79400077527171615547065275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52933385018114410364710183 79400077527171615547065275)
      ·
        refine ⟨119100116290757423320597913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79400077527171615547065275 119100116290757423320597913)
        ·
          refine ⟨89325087218068067490448435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119100116290757423320597913 89325087218068067490448435)
          ·
            refine ⟨133987630827102101235672653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89325087218068067490448435 133987630827102101235672653)
            ·
              refine ⟨50245361560163287963377245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133987630827102101235672653 50245361560163287963377245)
              ·
                refine ⟨18842010585061232986266467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50245361560163287963377245 18842010585061232986266467)
                ·
                  refine ⟨28263015877591849479399701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18842010585061232986266467 28263015877591849479399701)
                  ·
                    refine ⟨1324828869262117944346861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28263015877591849479399701 1324828869262117944346861)
                    ·
                      rfl

theorem cell23_7740285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_7740285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740285 prefixEnd_7740285 := by exact prefixLift 7740285
  have htrace : WordTrace (prefixWord ++ tailWord_7740285) baseStart_7740285 baseEnd_7740285 := by
    simpa [prefixWord, tailWord_7740285, baseEnd_7740285] using wordTrace_append hprefix tailTrace_7740285
  have hstable : (prefixWord ++ tailWord_7740285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740285).length < 2 ^ (prefixWord ++ tailWord_7740285).sum := by decide
  have hdescent : baseEnd_7740285 < baseStart_7740285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740290 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_7740290 : Nat := 118140960795 + 7740290 * 2 ^ 59
def prefixEnd_7740290 : Nat := 4983230072969 + 3 ^ 40 * 7740290 * 2
def baseEnd_7740290 : Nat := 3974489175189626313478061

theorem tailTrace_7740290 : CollatzResearch.WordTrace tailWord_7740290 prefixEnd_7740290 3974489175189626313478061 := by
  unfold tailWord_7740290
  simp only [CollatzResearch.WordTrace]
  refine ⟨70577892282064685283096581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188207712752172494088257549 70577892282064685283096581)
  ·
    refine ⟨13233354802887128490580609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70577892282064685283096581 13233354802887128490580609)
    ·
      refine ⟨9925016102165346367935457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13233354802887128490580609 9925016102165346367935457)
      ·
        refine ⟨7443762076624009775951593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9925016102165346367935457 7443762076624009775951593)
        ·
          refine ⟨5582821557468007331963695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7443762076624009775951593 5582821557468007331963695)
          ·
            refine ⟨8374232336202010997945543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5582821557468007331963695 8374232336202010997945543)
            ·
              refine ⟨12561348504303016496918315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374232336202010997945543 12561348504303016496918315)
              ·
                refine ⟨18842022756454524745377473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12561348504303016496918315 18842022756454524745377473)
                ·
                  refine ⟨14131517067340893559033105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18842022756454524745377473 14131517067340893559033105)
                  ·
                    refine ⟨10598637800505670169274829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14131517067340893559033105 10598637800505670169274829)
                    ·
                      refine ⟨3974489175189626313478061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598637800505670169274829 3974489175189626313478061)
                      ·
                        rfl

theorem cell23_7740290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_7740290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740290 prefixEnd_7740290 := by exact prefixLift 7740290
  have htrace : WordTrace (prefixWord ++ tailWord_7740290) baseStart_7740290 baseEnd_7740290 := by
    simpa [prefixWord, tailWord_7740290, baseEnd_7740290] using wordTrace_append hprefix tailTrace_7740290
  have hstable : (prefixWord ++ tailWord_7740290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740290).length < 2 ^ (prefixWord ++ tailWord_7740290).sum := by decide
  have hdescent : baseEnd_7740290 < baseStart_7740290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740292 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7740292 : Nat := 118140960795 + 7740292 * 2 ^ 59
def prefixEnd_7740292 : Nat := 4983230072969 + 3 ^ 40 * 7740292 * 2
def baseEnd_7740292 : Nat := 3974490202150935305653051

theorem tailTrace_7740292 : CollatzResearch.WordTrace tailWord_7740292 prefixEnd_7740292 3974490202150935305653051 := by
  unfold tailWord_7740292
  simp only [CollatzResearch.WordTrace]
  refine ⟨141155821037125747736979565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188207761382834330315972753 141155821037125747736979565)
  ·
    refine ⟨52933432888922155401367337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141155821037125747736979565 52933432888922155401367337)
    ·
      refine ⟨39700074666691616551025503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52933432888922155401367337 39700074666691616551025503)
      ·
        refine ⟨59550112000037424826538255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39700074666691616551025503 59550112000037424826538255)
        ·
          refine ⟨89325168000056137239807383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59550112000037424826538255 89325168000056137239807383)
          ·
            refine ⟨133987752000084205859711075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89325168000056137239807383 133987752000084205859711075)
            ·
              refine ⟨200981628000126308789566613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133987752000084205859711075 200981628000126308789566613)
              ·
                refine ⟨9421013812505920724510935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 200981628000126308789566613 9421013812505920724510935)
                ·
                  refine ⟨14131520718758881086766403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421013812505920724510935 14131520718758881086766403)
                  ·
                    refine ⟨21197281078138321630149605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14131520718758881086766403 21197281078138321630149605)
                    ·
                      refine ⟨3974490202150935305653051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21197281078138321630149605 3974490202150935305653051)
                      ·
                        rfl

theorem cell23_7740292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7740292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740292 prefixEnd_7740292 := by exact prefixLift 7740292
  have htrace : WordTrace (prefixWord ++ tailWord_7740292) baseStart_7740292 baseEnd_7740292 := by
    simpa [prefixWord, tailWord_7740292, baseEnd_7740292] using wordTrace_append hprefix tailTrace_7740292
  have hstable : (prefixWord ++ tailWord_7740292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740292).length < 2 ^ (prefixWord ++ tailWord_7740292).sum := by decide
  have hdescent : baseEnd_7740292 < baseStart_7740292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740296 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7740296 : Nat := 118140960795 + 7740296 * 2 ^ 59
def prefixEnd_7740296 : Nat := 4983230072969 + 3 ^ 40 * 7740296 * 2
def baseEnd_7740296 : Nat := 3974492256073553290003033

theorem tailTrace_7740296 : CollatzResearch.WordTrace tailWord_7740296 prefixEnd_7740296 3974492256073553290003033 := by
  unfold tailWord_7740296
  simp only [CollatzResearch.WordTrace]
  refine ⟨141155893983118502078552371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188207858644158002771403161 141155893983118502078552371)
  ·
    refine ⟨211733840974677753117828557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141155893983118502078552371 211733840974677753117828557)
    ·
      refine ⟨79400190365504157419185709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211733840974677753117828557 79400190365504157419185709)
      ·
        refine ⟨29775071387064059032194641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79400190365504157419185709 29775071387064059032194641)
        ·
          refine ⟨22331303540298044274145981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29775071387064059032194641 22331303540298044274145981)
          ·
            refine ⟨8374238827611766602804743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22331303540298044274145981 8374238827611766602804743)
            ·
              refine ⟨12561358241417649904207115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374238827611766602804743 12561358241417649904207115)
              ·
                refine ⟨18842037362126474856310673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12561358241417649904207115 18842037362126474856310673)
                ·
                  refine ⟨14131528021594856142233005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18842037362126474856310673 14131528021594856142233005)
                  ·
                    refine ⟨5299323008098071053337377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14131528021594856142233005 5299323008098071053337377)
                    ·
                      refine ⟨3974492256073553290003033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299323008098071053337377 3974492256073553290003033)
                      ·
                        rfl

theorem cell23_7740296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7740296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740296 prefixEnd_7740296 := by exact prefixLift 7740296
  have htrace : WordTrace (prefixWord ++ tailWord_7740296) baseStart_7740296 baseEnd_7740296 := by
    simpa [prefixWord, tailWord_7740296, baseEnd_7740296] using wordTrace_append hprefix tailTrace_7740296
  have hstable : (prefixWord ++ tailWord_7740296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740296).length < 2 ^ (prefixWord ++ tailWord_7740296).sum := by decide
  have hdescent : baseEnd_7740296 < baseStart_7740296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740309 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_7740309 : Nat := 118140960795 + 7740309 * 2 ^ 59
def prefixEnd_7740309 : Nat := 4983230072969 + 3 ^ 40 * 7740309 * 2
def baseEnd_7740309 : Nat := 3974498931322061739140473

theorem tailTrace_7740309 : CollatzResearch.WordTrace tailWord_7740309 prefixEnd_7740309 3974498931322061739140473 := by
  unfold tailWord_7740309
  simp only [CollatzResearch.WordTrace]
  refine ⟨282312262115189907377327981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188208174743459938251551987 282312262115189907377327981)
  ·
    refine ⟨105867098293196215266497993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282312262115189907377327981 105867098293196215266497993)
    ·
      refine ⟨79400323719897161449873495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105867098293196215266497993 79400323719897161449873495)
      ·
        refine ⟨119100485579845742174810243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79400323719897161449873495 119100485579845742174810243)
        ·
          refine ⟨178650728369768613262215365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119100485579845742174810243 178650728369768613262215365)
          ·
            refine ⟨33497011569331614986665381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178650728369768613262215365 33497011569331614986665381)
            ·
              refine ⟨6280689669249677809999759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33497011569331614986665381 6280689669249677809999759)
              ·
                refine ⟨9421034503874516714999639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280689669249677809999759 9421034503874516714999639)
                ·
                  refine ⟨14131551755811775072499459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421034503874516714999639 14131551755811775072499459)
                  ·
                    refine ⟨21197327633717662608749189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14131551755811775072499459 21197327633717662608749189)
                    ·
                      refine ⟨3974498931322061739140473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21197327633717662608749189 3974498931322061739140473)
                      ·
                        rfl

theorem cell23_7740309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_7740309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740309 prefixEnd_7740309 := by exact prefixLift 7740309
  have htrace : WordTrace (prefixWord ++ tailWord_7740309) baseStart_7740309 baseEnd_7740309 := by
    simpa [prefixWord, tailWord_7740309, baseEnd_7740309] using wordTrace_append hprefix tailTrace_7740309
  have hstable : (prefixWord ++ tailWord_7740309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740309).length < 2 ^ (prefixWord ++ tailWord_7740309).sum := by decide
  have hdescent : baseEnd_7740309 < baseStart_7740309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740319 : List Nat := [1, 1, 2, 5, 2, 1, 3, 2, 2, 4]
def baseStart_7740319 : Nat := 118140960795 + 7740319 * 2 ^ 59
def prefixEnd_7740319 : Nat := 4983230072969 + 3 ^ 40 * 7740319 * 2
def baseEnd_7740319 : Nat := 1324834688709535566671809

theorem tailTrace_7740319 : CollatzResearch.WordTrace tailWord_7740319 prefixEnd_7740319 1324834688709535566671809 := by
  unfold tailWord_7740319
  simp only [CollatzResearch.WordTrace]
  refine ⟨282312626845153679085192011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188208417896769119390128007 282312626845153679085192011)
  ·
    refine ⟨423468940267730518627788017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282312626845153679085192011 423468940267730518627788017)
    ·
      refine ⟨317601705200797888970841013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423468940267730518627788017 317601705200797888970841013)
      ·
        refine ⟨29775159862574802091016345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 317601705200797888970841013 29775159862574802091016345)
        ·
          refine ⟨22331369896931101568262259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29775159862574802091016345 22331369896931101568262259)
          ·
            refine ⟨33497054845396652352393389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22331369896931101568262259 33497054845396652352393389)
            ·
              refine ⟨12561395567023744632147521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33497054845396652352393389 12561395567023744632147521)
              ·
                refine ⟨9421046675267808474110641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12561395567023744632147521 9421046675267808474110641)
                ·
                  refine ⟨7065785006450856355582981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9421046675267808474110641 7065785006450856355582981)
                  ·
                    refine ⟨1324834688709535566671809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7065785006450856355582981 1324834688709535566671809)
                    ·
                      rfl

theorem cell23_7740319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_7740319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740319 prefixEnd_7740319 := by exact prefixLift 7740319
  have htrace : WordTrace (prefixWord ++ tailWord_7740319) baseStart_7740319 baseEnd_7740319 := by
    simpa [prefixWord, tailWord_7740319, baseEnd_7740319] using wordTrace_append hprefix tailTrace_7740319
  have hstable : (prefixWord ++ tailWord_7740319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740319).length < 2 ^ (prefixWord ++ tailWord_7740319).sum := by decide
  have hdescent : baseEnd_7740319 < baseStart_7740319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740325 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_7740325 : Nat := 118140960795 + 7740325 * 2 ^ 59
def prefixEnd_7740325 : Nat := 4983230072969 + 3 ^ 40 * 7740325 * 2
def baseEnd_7740325 : Nat := 3974507147012533676540399

theorem tailTrace_7740325 : CollatzResearch.WordTrace tailWord_7740325 prefixEnd_7740325 3974507147012533676540399 := by
  unfold tailWord_7740325
  simp only [CollatzResearch.WordTrace]
  refine ⟨282312845683131942109910429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188208563788754628073273619 282312845683131942109910429)
  ·
    refine ⟨105867317131174478291216411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282312845683131942109910429 105867317131174478291216411)
    ·
      refine ⟨158800975696761717436824617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105867317131174478291216411 158800975696761717436824617)
      ·
        refine ⟨119100731772571288077618463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158800975696761717436824617 119100731772571288077618463)
        ·
          refine ⟨178651097658856932116427695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119100731772571288077618463 178651097658856932116427695)
          ·
            refine ⟨267976646488285398174641543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178651097658856932116427695 267976646488285398174641543)
            ·
              refine ⟨401964969732428097261962315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267976646488285398174641543 401964969732428097261962315)
              ·
                refine ⟨602947454598642145892943473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401964969732428097261962315 602947454598642145892943473)
                ·
                  refine ⟨452210590948981609419707605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 602947454598642145892943473 452210590948981609419707605)
                  ·
                    refine ⟨10598685725366756470774397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 452210590948981609419707605 10598685725366756470774397)
                    ·
                      refine ⟨3974507147012533676540399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598685725366756470774397 3974507147012533676540399)
                      ·
                        rfl

theorem cell23_7740325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_7740325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740325 prefixEnd_7740325 := by exact prefixLift 7740325
  have htrace : WordTrace (prefixWord ++ tailWord_7740325) baseStart_7740325 baseEnd_7740325 := by
    simpa [prefixWord, tailWord_7740325, baseEnd_7740325] using wordTrace_append hprefix tailTrace_7740325
  have hstable : (prefixWord ++ tailWord_7740325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740325).length < 2 ^ (prefixWord ++ tailWord_7740325).sum := by decide
  have hdescent : baseEnd_7740325 < baseStart_7740325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740349 : List Nat := [1, 4, 1, 2, 4, 2, 2, 7]
def baseStart_7740349 : Nat := 118140960795 + 7740349 * 2 ^ 59
def prefixEnd_7740349 : Nat := 4983230072969 + 3 ^ 40 * 7740349 * 2
def baseEnd_7740349 : Nat := 147204424835120058616307

theorem tailTrace_7740349 : CollatzResearch.WordTrace tailWord_7740349 prefixEnd_7740349 147204424835120058616307 := by
  unfold tailWord_7740349
  simp only [CollatzResearch.WordTrace]
  refine ⟨282313721035044994208784101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188209147356696662805856067 282313721035044994208784101)
  ·
    refine ⟨52933822694070936414147019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 282313721035044994208784101 52933822694070936414147019)
    ·
      refine ⟨79400734041106404621220529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52933822694070936414147019 79400734041106404621220529)
      ·
        refine ⟨59550550530829803465915397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79400734041106404621220529 59550550530829803465915397)
        ·
          refine ⟨11165728224530588149859137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59550550530829803465915397 11165728224530588149859137)
          ·
            refine ⟨8374296168397941112394353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165728224530588149859137 8374296168397941112394353)
            ·
              refine ⟨6280722126298455834295765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374296168397941112394353 6280722126298455834295765)
              ·
                refine ⟨147204424835120058616307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6280722126298455834295765 147204424835120058616307)
                ·
                  rfl

theorem cell23_7740349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 7].length) (baseStart_7740349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740349 prefixEnd_7740349 := by exact prefixLift 7740349
  have htrace : WordTrace (prefixWord ++ tailWord_7740349) baseStart_7740349 baseEnd_7740349 := by
    simpa [prefixWord, tailWord_7740349, baseEnd_7740349] using wordTrace_append hprefix tailTrace_7740349
  have hstable : (prefixWord ++ tailWord_7740349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740349).length < 2 ^ (prefixWord ++ tailWord_7740349).sum := by decide
  have hdescent : baseEnd_7740349 < baseStart_7740349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740360 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_7740360 : Nat := 118140960795 + 7740360 * 2 ^ 59
def prefixEnd_7740360 : Nat := 4983230072969 + 3 ^ 40 * 7740360 * 2
def baseEnd_7740360 : Nat := 3974525118835441039602739

theorem tailTrace_7740360 : CollatzResearch.WordTrace tailWord_7740360 prefixEnd_7740360 3974525118835441039602739 := by
  unfold tailWord_7740360
  simp only [CollatzResearch.WordTrace]
  refine ⟨141157061119002571543717267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188209414825336762058289689 141157061119002571543717267)
  ·
    refine ⟨211735591678503857315575901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141157061119002571543717267 211735591678503857315575901)
    ·
      refine ⟨79400846879438946493340963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211735591678503857315575901 79400846879438946493340963)
      ·
        refine ⟨119101270319158419740011445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79400846879438946493340963 119101270319158419740011445)
        ·
          refine ⟨11165744092421101850626073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119101270319158419740011445 11165744092421101850626073)
          ·
            refine ⟨8374308069315826387969555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11165744092421101850626073 8374308069315826387969555)
            ·
              refine ⟨12561462103973739581954333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374308069315826387969555 12561462103973739581954333)
              ·
                refine ⟨4710548288990152343232875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12561462103973739581954333 4710548288990152343232875)
                ·
                  refine ⟨7065822433485228514849313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4710548288990152343232875 7065822433485228514849313)
                  ·
                    refine ⟨5299366825113921386136985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7065822433485228514849313 5299366825113921386136985)
                    ·
                      refine ⟨3974525118835441039602739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299366825113921386136985 3974525118835441039602739)
                      ·
                        rfl

theorem cell23_7740360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_7740360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740360 prefixEnd_7740360 := by exact prefixLift 7740360
  have htrace : WordTrace (prefixWord ++ tailWord_7740360) baseStart_7740360 baseEnd_7740360 := by
    simpa [prefixWord, tailWord_7740360, baseEnd_7740360] using wordTrace_append hprefix tailTrace_7740360
  have hstable : (prefixWord ++ tailWord_7740360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740360).length < 2 ^ (prefixWord ++ tailWord_7740360).sum := by decide
  have hdescent : baseEnd_7740360 < baseStart_7740360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740369 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 1, 3, 2]
def baseStart_7740369 : Nat := 118140960795 + 7740369 * 2 ^ 59
def prefixEnd_7740369 : Nat := 4983230072969 + 3 ^ 40 * 7740369 * 2
def baseEnd_7740369 : Nat := 3974529740161331504390197

theorem tailTrace_7740369 : CollatzResearch.WordTrace tailWord_7740369 prefixEnd_7740369 3974529740161331504390197 := by
  unfold tailWord_7740369
  simp only [CollatzResearch.WordTrace]
  refine ⟨282314450494972537624512161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188209633663315025083008107 282314450494972537624512161)
  ·
    refine ⟨211735837871229403218384121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282314450494972537624512161 211735837871229403218384121)
    ·
      refine ⟨158801878403422052413788091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211735837871229403218384121 158801878403422052413788091)
      ·
        refine ⟨238202817605133078620682137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158801878403422052413788091 238202817605133078620682137)
        ·
          refine ⟨178652113203849808965511603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238202817605133078620682137 178652113203849808965511603)
          ·
            refine ⟨267978169805774713448267405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178652113203849808965511603 267978169805774713448267405)
            ·
              refine ⟨100491813677165517543100277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 267978169805774713448267405 100491813677165517543100277)
              ·
                refine ⟨9421107532234267269665651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 100491813677165517543100277 9421107532234267269665651)
                ·
                  refine ⟨14131661298351400904498477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421107532234267269665651 14131661298351400904498477)
                  ·
                    refine ⟨5299372986881775339186929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14131661298351400904498477 5299372986881775339186929)
                    ·
                      refine ⟨3974529740161331504390197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299372986881775339186929 3974529740161331504390197)
                      ·
                        rfl

theorem cell23_7740369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_7740369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740369 prefixEnd_7740369 := by exact prefixLift 7740369
  have htrace : WordTrace (prefixWord ++ tailWord_7740369) baseStart_7740369 baseEnd_7740369 := by
    simpa [prefixWord, tailWord_7740369, baseEnd_7740369] using wordTrace_append hprefix tailTrace_7740369
  have hstable : (prefixWord ++ tailWord_7740369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740369).length < 2 ^ (prefixWord ++ tailWord_7740369).sum := by decide
  have hdescent : baseEnd_7740369 < baseStart_7740369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740375 : List Nat := [1, 1, 3, 2, 1, 1, 2, 4, 2, 6]
def baseStart_7740375 : Nat := 118140960795 + 7740375 * 2 ^ 59
def prefixEnd_7740375 : Nat := 4983230072969 + 3 ^ 40 * 7740375 * 2
def baseEnd_7740375 : Nat := 1324844273681752826971723

theorem tailTrace_7740375 : CollatzResearch.WordTrace tailWord_7740375 prefixEnd_7740375 1324844273681752826971723 := by
  unfold tailWord_7740375
  simp only [CollatzResearch.WordTrace]
  refine ⟨282314669332950800649230579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188209779555300533766153719 282314669332950800649230579)
  ·
    refine ⟨423472003999426200973845869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282314669332950800649230579 423472003999426200973845869)
    ·
      refine ⟨158802001499784825365192201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423472003999426200973845869 158802001499784825365192201)
      ·
        refine ⟨119101501124838619023894151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158802001499784825365192201 119101501124838619023894151)
        ·
          refine ⟨178652251687257928535841227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119101501124838619023894151 178652251687257928535841227)
          ·
            refine ⟨267978377530886892803761841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178652251687257928535841227 267978377530886892803761841)
            ·
              refine ⟨200983783148165169602821381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267978377530886892803761841 200983783148165169602821381)
              ·
                refine ⟨37684459340280969300529009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 200983783148165169602821381 37684459340280969300529009)
                ·
                  refine ⟨28263344505210726975396757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37684459340280969300529009 28263344505210726975396757)
                  ·
                    refine ⟨1324844273681752826971723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28263344505210726975396757 1324844273681752826971723)
                    ·
                      rfl

theorem cell23_7740375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_7740375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740375 prefixEnd_7740375 := by exact prefixLift 7740375
  have htrace : WordTrace (prefixWord ++ tailWord_7740375) baseStart_7740375 baseEnd_7740375 := by
    simpa [prefixWord, tailWord_7740375, baseEnd_7740375] using wordTrace_append hprefix tailTrace_7740375
  have hstable : (prefixWord ++ tailWord_7740375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740375).length < 2 ^ (prefixWord ++ tailWord_7740375).sum := by decide
  have hdescent : baseEnd_7740375 < baseStart_7740375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740385 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_7740385 : Nat := 118140960795 + 7740385 * 2 ^ 59
def prefixEnd_7740385 : Nat := 4983230072969 + 3 ^ 40 * 7740385 * 2
def baseEnd_7740385 : Nat := 3974537955851803441790123

theorem tailTrace_7740385 : CollatzResearch.WordTrace tailWord_7740385 prefixEnd_7740385 3974537955851803441790123 := by
  unfold tailWord_7740385
  simp only [CollatzResearch.WordTrace]
  refine ⟨282315034062914572357094609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188210022708609714904729739 282315034062914572357094609)
  ·
    refine ⟨211736275547185929267820957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282315034062914572357094609 211736275547185929267820957)
    ·
      refine ⟨79401103330194723475432859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211736275547185929267820957 79401103330194723475432859)
      ·
        refine ⟨119101654995292085213149289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79401103330194723475432859 119101654995292085213149289)
        ·
          refine ⟨89326241246469063909861967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119101654995292085213149289 89326241246469063909861967)
          ·
            refine ⟨133989361869703595864792951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89326241246469063909861967 133989361869703595864792951)
            ·
              refine ⟨200984042804555393797189427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133989361869703595864792951 200984042804555393797189427)
              ·
                refine ⟨301476064206833090695784141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200984042804555393797189427 301476064206833090695784141)
                ·
                  refine ⟨113053524077562409010919053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301476064206833090695784141 113053524077562409010919053)
                  ·
                    refine ⟨42395071529085903379094645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113053524077562409010919053 42395071529085903379094645)
                    ·
                      refine ⟨3974537955851803441790123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42395071529085903379094645 3974537955851803441790123)
                      ·
                        rfl

theorem cell23_7740385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_7740385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740385 prefixEnd_7740385 := by exact prefixLift 7740385
  have htrace : WordTrace (prefixWord ++ tailWord_7740385) baseStart_7740385 baseEnd_7740385 := by
    simpa [prefixWord, tailWord_7740385, baseEnd_7740385] using wordTrace_append hprefix tailTrace_7740385
  have hstable : (prefixWord ++ tailWord_7740385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740385).length < 2 ^ (prefixWord ++ tailWord_7740385).sum := by decide
  have hdescent : baseEnd_7740385 < baseStart_7740385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740435 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 3, 7]
def baseStart_7740435 : Nat := 118140960795 + 7740435 * 2 ^ 59
def prefixEnd_7740435 : Nat := 4983230072969 + 3 ^ 40 * 7740435 * 2
def baseEnd_7740435 : Nat := 1324854543294842748721631

theorem tailTrace_7740435 : CollatzResearch.WordTrace tailWord_7740435 prefixEnd_7740435 1324854543294842748721631 := by
  unfold tailWord_7740435
  simp only [CollatzResearch.WordTrace]
  refine ⟨282316857712733430896414759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188211238475155620597609839 282316857712733430896414759)
  ·
    refine ⟨423475286569100146344622139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282316857712733430896414759 423475286569100146344622139)
    ·
      refine ⟨635212929853650219516933209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423475286569100146344622139 635212929853650219516933209)
      ·
        refine ⟨476409697390237664637699907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635212929853650219516933209 476409697390237664637699907)
        ·
          refine ⟨714614546085356496956549861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476409697390237664637699907 714614546085356496956549861)
          ·
            refine ⟨133990227391004343179353099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 714614546085356496956549861 133990227391004343179353099)
            ·
              refine ⟨200985341086506514769029649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133990227391004343179353099 200985341086506514769029649)
              ·
                refine ⟨150739005814879886076772237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 200985341086506514769029649 150739005814879886076772237)
                ·
                  refine ⟨56527127180579957278789589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150739005814879886076772237 56527127180579957278789589)
                  ·
                    refine ⟨1324854543294842748721631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56527127180579957278789589 1324854543294842748721631)
                    ·
                      rfl

theorem cell23_7740435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_7740435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740435 prefixEnd_7740435 := by exact prefixLift 7740435
  have htrace : WordTrace (prefixWord ++ tailWord_7740435) baseStart_7740435 baseEnd_7740435 := by
    simpa [prefixWord, tailWord_7740435, baseEnd_7740435] using wordTrace_append hprefix tailTrace_7740435
  have hstable : (prefixWord ++ tailWord_7740435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740435).length < 2 ^ (prefixWord ++ tailWord_7740435).sum := by decide
  have hdescent : baseEnd_7740435 < baseStart_7740435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740449 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 3]
def baseStart_7740449 : Nat := 118140960795 + 7740449 * 2 ^ 59
def prefixEnd_7740449 : Nat := 4983230072969 + 3 ^ 40 * 7740449 * 2
def baseEnd_7740449 : Nat := 3974570818613691191389829

theorem tailTrace_7740449 : CollatzResearch.WordTrace tailWord_7740449 prefixEnd_7740449 3974570818613691191389829 := by
  unfold tailWord_7740449
  simp only [CollatzResearch.WordTrace]
  refine ⟨282317368334682711287424401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188211578889788474191616267 282317368334682711287424401)
  ·
    refine ⟨211738026251012033465568301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282317368334682711287424401 211738026251012033465568301)
    ·
      refine ⟨79401759844129512549588113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211738026251012033465568301 79401759844129512549588113)
      ·
        refine ⟨59551319883097134412191085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79401759844129512549588113 59551319883097134412191085)
        ·
          refine ⟨22331744956161425404571657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59551319883097134412191085 22331744956161425404571657)
          ·
            refine ⟨16748808717121069053428743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22331744956161425404571657 16748808717121069053428743)
            ·
              refine ⟨25123213075681603580143115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16748808717121069053428743 25123213075681603580143115)
              ·
                refine ⟨37684819613522405370214673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25123213075681603580143115 37684819613522405370214673)
                ·
                  refine ⟨28263614710141804027661005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37684819613522405370214673 28263614710141804027661005)
                  ·
                    refine ⟨10598855516303176510372877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28263614710141804027661005 10598855516303176510372877)
                    ·
                      refine ⟨3974570818613691191389829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598855516303176510372877 3974570818613691191389829)
                      ·
                        rfl

theorem cell23_7740449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_7740449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740449 prefixEnd_7740449 := by exact prefixLift 7740449
  have htrace : WordTrace (prefixWord ++ tailWord_7740449) baseStart_7740449 baseEnd_7740449 := by
    simpa [prefixWord, tailWord_7740449, baseEnd_7740449] using wordTrace_append hprefix tailTrace_7740449
  have hstable : (prefixWord ++ tailWord_7740449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740449).length < 2 ^ (prefixWord ++ tailWord_7740449).sum := by decide
  have hdescent : baseEnd_7740449 < baseStart_7740449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740475 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_7740475 : Nat := 118140960795 + 7740475 * 2 ^ 59
def prefixEnd_7740475 : Nat := 4983230072969 + 3 ^ 40 * 7740475 * 2
def baseEnd_7740475 : Nat := 3974584169110708089664709

theorem tailTrace_7740475 : CollatzResearch.WordTrace tailWord_7740475 prefixEnd_7740475 3974584169110708089664709 := by
  unfold tailWord_7740475
  simp only [CollatzResearch.WordTrace]
  refine ⟨282318316632588517727870879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188212211088392345151913919 282318316632588517727870879)
  ·
    refine ⟨423477474948882776591806319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282318316632588517727870879 423477474948882776591806319)
    ·
      refine ⟨635216212423324164887709479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423477474948882776591806319 635216212423324164887709479)
      ·
        refine ⟨952824318634986247331564219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635216212423324164887709479 952824318634986247331564219)
        ·
          refine ⟨1429236477952479370997346329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952824318634986247331564219 1429236477952479370997346329)
          ·
            refine ⟨1071927358464359528248009747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429236477952479370997346329 1071927358464359528248009747)
            ·
              refine ⟨1607891037696539292372014621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071927358464359528248009747 1607891037696539292372014621)
              ·
                refine ⟨602959139136202234639505483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607891037696539292372014621 602959139136202234639505483)
                ·
                  refine ⟨904438708704303351959258225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 602959139136202234639505483 904438708704303351959258225)
                  ·
                    refine ⟨678329031528227513969443669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 904438708704303351959258225 678329031528227513969443669)
                    ·
                      refine ⟨3974584169110708089664709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 678329031528227513969443669 3974584169110708089664709)
                      ·
                        rfl

theorem cell23_7740475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_7740475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740475 prefixEnd_7740475 := by exact prefixLift 7740475
  have htrace : WordTrace (prefixWord ++ tailWord_7740475) baseStart_7740475 baseEnd_7740475 := by
    simpa [prefixWord, tailWord_7740475, baseEnd_7740475] using wordTrace_append hprefix tailTrace_7740475
  have hstable : (prefixWord ++ tailWord_7740475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740475).length < 2 ^ (prefixWord ++ tailWord_7740475).sum := by decide
  have hdescent : baseEnd_7740475 < baseStart_7740475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740539 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 3]
def baseStart_7740539 : Nat := 118140960795 + 7740539 * 2 ^ 59
def prefixEnd_7740539 : Nat := 4983230072969 + 3 ^ 40 * 7740539 * 2
def baseEnd_7740539 : Nat := 3974617031872595839264415

theorem tailTrace_7740539 : CollatzResearch.WordTrace tailWord_7740539 prefixEnd_7740539 3974617031872595839264415 := by
  unfold tailWord_7740539
  simp only [CollatzResearch.WordTrace]
  refine ⟨282320650904356656658200671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188213767269571104438800447 282320650904356656658200671)
  ·
    refine ⟨423480976356534984987301007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282320650904356656658200671 423480976356534984987301007)
    ·
      refine ⟨635221464534802477480951511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423480976356534984987301007 635221464534802477480951511)
      ·
        refine ⟨952832196802203716221427267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635221464534802477480951511 952832196802203716221427267)
        ·
          refine ⟨1429248295203305574332140901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952832196802203716221427267 1429248295203305574332140901)
          ·
            refine ⟨267984055350619795187276419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1429248295203305574332140901 267984055350619795187276419)
            ·
              refine ⟨401976083025929692780914629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267984055350619795187276419 401976083025929692780914629)
              ·
                refine ⟨75370515567361817396421493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401976083025929692780914629 75370515567361817396421493)
                ·
                  refine ⟨7065985834440170380914515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 75370515567361817396421493 7065985834440170380914515)
                  ·
                    refine ⟨10598978751660255571371773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7065985834440170380914515 10598978751660255571371773)
                    ·
                      refine ⟨3974617031872595839264415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10598978751660255571371773 3974617031872595839264415)
                      ·
                        rfl

theorem cell23_7740539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 5, 1, 3].length) (baseStart_7740539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740539 prefixEnd_7740539 := by exact prefixLift 7740539
  have htrace : WordTrace (prefixWord ++ tailWord_7740539) baseStart_7740539 baseEnd_7740539 := by
    simpa [prefixWord, tailWord_7740539, baseEnd_7740539] using wordTrace_append hprefix tailTrace_7740539
  have hstable : (prefixWord ++ tailWord_7740539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740539).length < 2 ^ (prefixWord ++ tailWord_7740539).sum := by decide
  have hdescent : baseEnd_7740539 < baseStart_7740539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740579 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 2, 6, 2]
def baseStart_7740579 : Nat := 118140960795 + 7740579 * 2 ^ 59
def prefixEnd_7740579 : Nat := 4983230072969 + 3 ^ 40 * 7740579 * 2
def baseEnd_7740579 : Nat := 3974637571098775682764231

theorem tailTrace_7740579 : CollatzResearch.WordTrace tailWord_7740579 prefixEnd_7740579 3974637571098775682764231 := by
  unfold tailWord_7740579
  simp only [CollatzResearch.WordTrace]
  refine ⟨282322109824211743489656791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188214739882807828993104527 282322109824211743489656791)
  ·
    refine ⟨423483164736317615234485187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282322109824211743489656791 423483164736317615234485187)
    ·
      refine ⟨635224747104476422851727781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423483164736317615234485187 635224747104476422851727781)
      ·
        refine ⟨119104640082089329284698959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 635224747104476422851727781 119104640082089329284698959)
        ·
          refine ⟨178656960123133993927048439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119104640082089329284698959 178656960123133993927048439)
          ·
            refine ⟨267985440184700990890572659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178656960123133993927048439 267985440184700990890572659)
            ·
              refine ⟨401978160277051486335858989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 267985440184700990890572659 401978160277051486335858989)
              ·
                refine ⟨150741810103894307375947121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 401978160277051486335858989 150741810103894307375947121)
                ·
                  refine ⟨113056357577920730531960341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150741810103894307375947121 113056357577920730531960341)
                  ·
                    refine ⟨5299516761465034243685641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113056357577920730531960341 5299516761465034243685641)
                    ·
                      refine ⟨3974637571098775682764231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299516761465034243685641 3974637571098775682764231)
                      ·
                        rfl

theorem cell23_7740579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6, 2].length) (baseStart_7740579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740579 prefixEnd_7740579 := by exact prefixLift 7740579
  have htrace : WordTrace (prefixWord ++ tailWord_7740579) baseStart_7740579 baseEnd_7740579 := by
    simpa [prefixWord, tailWord_7740579, baseEnd_7740579] using wordTrace_append hprefix tailTrace_7740579
  have hstable : (prefixWord ++ tailWord_7740579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740579).length < 2 ^ (prefixWord ++ tailWord_7740579).sum := by decide
  have hdescent : baseEnd_7740579 < baseStart_7740579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740583 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7740583 : Nat := 118140960795 + 7740583 * 2 ^ 59
def prefixEnd_7740583 : Nat := 4983230072969 + 3 ^ 40 * 7740583 * 2
def baseEnd_7740583 : Nat := 3974639625021393667114213

theorem tailTrace_7740583 : CollatzResearch.WordTrace tailWord_7740583 prefixEnd_7740583 3974639625021393667114213 := by
  unfold tailWord_7740583
  simp only [CollatzResearch.WordTrace]
  refine ⟨282322255716197252172802403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188214837144131501448534935 282322255716197252172802403)
  ·
    refine ⟨423483383574295878259203605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282322255716197252172802403 423483383574295878259203605)
    ·
      refine ⟨19850783605045119293400169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 423483383574295878259203605 19850783605045119293400169)
      ·
        refine ⟨14888087703783839470050127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19850783605045119293400169 14888087703783839470050127)
        ·
          refine ⟨22332131555675759205075191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14888087703783839470050127 22332131555675759205075191)
          ·
            refine ⟨33498197333513638807612787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22332131555675759205075191 33498197333513638807612787)
            ·
              refine ⟨50247296000270458211419181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33498197333513638807612787 50247296000270458211419181)
              ·
                refine ⟨18842736000101421829282193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50247296000270458211419181 18842736000101421829282193)
                ·
                  refine ⟨14132052000076066371961645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18842736000101421829282193 14132052000076066371961645)
                  ·
                    refine ⟨5299519500028524889485617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14132052000076066371961645 5299519500028524889485617)
                    ·
                      refine ⟨3974639625021393667114213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299519500028524889485617 3974639625021393667114213)
                      ·
                        rfl

theorem cell23_7740583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7740583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740583 prefixEnd_7740583 := by exact prefixLift 7740583
  have htrace : WordTrace (prefixWord ++ tailWord_7740583) baseStart_7740583 baseEnd_7740583 := by
    simpa [prefixWord, tailWord_7740583, baseEnd_7740583] using wordTrace_append hprefix tailTrace_7740583
  have hstable : (prefixWord ++ tailWord_7740583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740583).length < 2 ^ (prefixWord ++ tailWord_7740583).sum := by decide
  have hdescent : baseEnd_7740583 < baseStart_7740583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740593 : List Nat := [1, 2, 2, 5, 1, 2, 3, 1, 1, 5]
def baseStart_7740593 : Nat := 118140960795 + 7740593 * 2 ^ 59
def prefixEnd_7740593 : Nat := 4983230072969 + 3 ^ 40 * 7740593 * 2
def baseEnd_7740593 : Nat := 1324881586609312875996389

theorem tailTrace_7740593 : CollatzResearch.WordTrace tailWord_7740593 prefixEnd_7740593 1324881586609312875996389 := by
  unfold tailWord_7740593
  simp only [CollatzResearch.WordTrace]
  refine ⟨282322620446161023880666433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188215080297440682587110955 282322620446161023880666433)
  ·
    refine ⟨211741965334620767910499825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282322620446161023880666433 211741965334620767910499825)
    ·
      refine ⟨158806474000965575932874869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211741965334620767910499825 158806474000965575932874869)
      ·
        refine ⟨14888106937590522743707019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158806474000965575932874869 14888106937590522743707019)
        ·
          refine ⟨22332160406385784115560529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14888106937590522743707019 22332160406385784115560529)
          ·
            refine ⟨16749120304789338086670397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22332160406385784115560529 16749120304789338086670397)
            ·
              refine ⟨6280920114296001782501399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16749120304789338086670397 6280920114296001782501399)
              ·
                refine ⟨9421380171444002673752099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280920114296001782501399 9421380171444002673752099)
                ·
                  refine ⟨14132070257166004010628149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421380171444002673752099 14132070257166004010628149)
                  ·
                    refine ⟨1324881586609312875996389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14132070257166004010628149 1324881586609312875996389)
                    ·
                      rfl

theorem cell23_7740593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 3, 1, 1, 5].length) (baseStart_7740593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740593 prefixEnd_7740593 := by exact prefixLift 7740593
  have htrace : WordTrace (prefixWord ++ tailWord_7740593) baseStart_7740593 baseEnd_7740593 := by
    simpa [prefixWord, tailWord_7740593, baseEnd_7740593] using wordTrace_append hprefix tailTrace_7740593
  have hstable : (prefixWord ++ tailWord_7740593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740593).length < 2 ^ (prefixWord ++ tailWord_7740593).sum := by decide
  have hdescent : baseEnd_7740593 < baseStart_7740593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740626 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_7740626 : Nat := 118140960795 + 7740626 * 2 ^ 59
def prefixEnd_7740626 : Nat := 4983230072969 + 3 ^ 40 * 7740626 * 2
def baseEnd_7740626 : Nat := 3974661704689536998876515

theorem tailTrace_7740626 : CollatzResearch.WordTrace tailWord_7740626 prefixEnd_7740626 3974661704689536998876515 := by
  unfold tailWord_7740626
  simp only [CollatzResearch.WordTrace]
  refine ⟨70580956013760367629154433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188215882703360980344411821 70580956013760367629154433)
  ·
    refine ⟨52935717010320275721865825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70580956013760367629154433 52935717010320275721865825)
    ·
      refine ⟨39701787757740206791399369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52935717010320275721865825 39701787757740206791399369)
      ·
        refine ⟨29776340818305155093549527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39701787757740206791399369 29776340818305155093549527)
        ·
          refine ⟨44664511227457732640324291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29776340818305155093549527 44664511227457732640324291)
          ·
            refine ⟨66996766841186598960486437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44664511227457732640324291 66996766841186598960486437)
            ·
              refine ⟨12561893782722487305091207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66996766841186598960486437 12561893782722487305091207)
              ·
                refine ⟨18842840674083730957636811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12561893782722487305091207 18842840674083730957636811)
                ·
                  refine ⟨28264261011125596436455217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18842840674083730957636811 28264261011125596436455217)
                  ·
                    refine ⟨21198195758344197327341413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28264261011125596436455217 21198195758344197327341413)
                    ·
                      refine ⟨3974661704689536998876515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21198195758344197327341413 3974661704689536998876515)
                      ·
                        rfl

theorem cell23_7740626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_7740626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740626 prefixEnd_7740626 := by exact prefixLift 7740626
  have htrace : WordTrace (prefixWord ++ tailWord_7740626) baseStart_7740626 baseEnd_7740626 := by
    simpa [prefixWord, tailWord_7740626, baseEnd_7740626] using wordTrace_append hprefix tailTrace_7740626
  have hstable : (prefixWord ++ tailWord_7740626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740626).length < 2 ^ (prefixWord ++ tailWord_7740626).sum := by decide
  have hdescent : baseEnd_7740626 < baseStart_7740626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740647 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7740647 : Nat := 118140960795 + 7740647 * 2 ^ 59
def prefixEnd_7740647 : Nat := 4983230072969 + 3 ^ 40 * 7740647 * 2
def baseEnd_7740647 : Nat := 3974672487783281416713919

theorem tailTrace_7740647 : CollatzResearch.WordTrace tailWord_7740647 prefixEnd_7740647 3974672487783281416713919 := by
  unfold tailWord_7740647
  simp only [CollatzResearch.WordTrace]
  refine ⟨282324589987965391103132195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188216393325310260735421463 282324589987965391103132195)
  ·
    refine ⟨423486884981948086654698293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282324589987965391103132195 423486884981948086654698293)
    ·
      refine ⟨39701895467057633123877965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423486884981948086654698293 39701895467057633123877965)
      ·
        refine ⟨14888210800146612421454237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39701895467057633123877965 14888210800146612421454237)
        ·
          refine ⟨5583079050054979658045339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14888210800146612421454237 5583079050054979658045339)
          ·
            refine ⟨8374618575082469487068009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583079050054979658045339 8374618575082469487068009)
            ·
              refine ⟨6280963931311852115301007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374618575082469487068009 6280963931311852115301007)
              ·
                refine ⟨9421445896967778172951511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280963931311852115301007 9421445896967778172951511)
                ·
                  refine ⟨14132168845451667259427267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421445896967778172951511 14132168845451667259427267)
                  ·
                    refine ⟨21198253268177500889140901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14132168845451667259427267 21198253268177500889140901)
                    ·
                      refine ⟨3974672487783281416713919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21198253268177500889140901 3974672487783281416713919)
                      ·
                        rfl

theorem cell23_7740647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7740647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740647 prefixEnd_7740647 := by exact prefixLift 7740647
  have htrace : WordTrace (prefixWord ++ tailWord_7740647) baseStart_7740647 baseEnd_7740647 := by
    simpa [prefixWord, tailWord_7740647, baseEnd_7740647] using wordTrace_append hprefix tailTrace_7740647
  have hstable : (prefixWord ++ tailWord_7740647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740647).length < 2 ^ (prefixWord ++ tailWord_7740647).sum := by decide
  have hdescent : baseEnd_7740647 < baseStart_7740647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740650 : List Nat := [3, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_7740650 : Nat := 118140960795 + 7740650 * 2 ^ 59
def prefixEnd_7740650 : Nat := 4983230072969 + 3 ^ 40 * 7740650 * 2
def baseEnd_7740650 : Nat := 3974674028225244904976405

theorem tailTrace_7740650 : CollatzResearch.WordTrace tailWord_7740650 prefixEnd_7740650 3974674028225244904976405 := by
  unfold tailWord_7740650
  simp only [CollatzResearch.WordTrace]
  refine ⟨70581174851738630653872851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188216466271303015076994269 70581174851738630653872851)
  ·
    refine ⟨105871762277607945980809277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70581174851738630653872851 105871762277607945980809277)
    ·
      refine ⟨39701910854102979742803479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105871762277607945980809277 39701910854102979742803479)
      ·
        refine ⟨59552866281154469614205219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39701910854102979742803479 59552866281154469614205219)
        ·
          refine ⟨89329299421731704421307829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59552866281154469614205219 89329299421731704421307829)
          ·
            refine ⟨8374621820787347289497609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89329299421731704421307829 8374621820787347289497609)
            ·
              refine ⟨6280966365590510467123207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8374621820787347289497609 6280966365590510467123207)
              ·
                refine ⟨9421449548385765700684811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6280966365590510467123207 9421449548385765700684811)
                ·
                  refine ⟨14132174322578648551027217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421449548385765700684811 14132174322578648551027217)
                  ·
                    refine ⟨10599130741933986413270413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14132174322578648551027217 10599130741933986413270413)
                    ·
                      refine ⟨3974674028225244904976405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10599130741933986413270413 3974674028225244904976405)
                      ·
                        rfl

theorem cell23_7740650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_7740650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740650 prefixEnd_7740650 := by exact prefixLift 7740650
  have htrace : WordTrace (prefixWord ++ tailWord_7740650) baseStart_7740650 baseEnd_7740650 := by
    simpa [prefixWord, tailWord_7740650, baseEnd_7740650] using wordTrace_append hprefix tailTrace_7740650
  have hstable : (prefixWord ++ tailWord_7740650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740650).length < 2 ^ (prefixWord ++ tailWord_7740650).sum := by decide
  have hdescent : baseEnd_7740650 < baseStart_7740650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740680 : List Nat := [2, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_7740680 : Nat := 118140960795 + 7740680 * 2 ^ 59
def prefixEnd_7740680 : Nat := 4983230072969 + 3 ^ 40 * 7740680 * 2
def baseEnd_7740680 : Nat := 3974689432644879787601267

theorem tailTrace_7740680 : CollatzResearch.WordTrace tailWord_7740680 prefixEnd_7740680 3974689432644879787601267 := by
  unfold tailWord_7740680
  simp only [CollatzResearch.WordTrace]
  refine ⟨141162896798422918869541747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188217195731230558492722329 141162896798422918869541747)
  ·
    refine ⟨211744345197634378304312621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141162896798422918869541747 211744345197634378304312621)
    ·
      refine ⟨79404129449112891864117233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211744345197634378304312621 79404129449112891864117233)
      ·
        refine ⟨59553097086834668898087925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79404129449112891864117233 59553097086834668898087925)
        ·
          refine ⟨5583102851890750209195743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59553097086834668898087925 5583102851890750209195743)
          ·
            refine ⟨8374654277836125313793615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583102851890750209195743 8374654277836125313793615)
            ·
              refine ⟨12561981416754187970690423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8374654277836125313793615 12561981416754187970690423)
              ·
                refine ⟨18842972125131281956035635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12561981416754187970690423 18842972125131281956035635)
                ·
                  refine ⟨28264458187696922934053453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18842972125131281956035635 28264458187696922934053453)
                  ·
                    refine ⟨10599171820386346100270045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28264458187696922934053453 10599171820386346100270045)
                    ·
                      refine ⟨3974689432644879787601267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10599171820386346100270045 3974689432644879787601267)
                      ·
                        rfl

theorem cell23_7740680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_7740680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740680 prefixEnd_7740680 := by exact prefixLift 7740680
  have htrace : WordTrace (prefixWord ++ tailWord_7740680) baseStart_7740680 baseEnd_7740680 := by
    simpa [prefixWord, tailWord_7740680, baseEnd_7740680] using wordTrace_append hprefix tailTrace_7740680
  have hstable : (prefixWord ++ tailWord_7740680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740680).length < 2 ^ (prefixWord ++ tailWord_7740680).sum := by decide
  have hdescent : baseEnd_7740680 < baseStart_7740680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740689 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_7740689 : Nat := 118140960795 + 7740689 * 2 ^ 59
def prefixEnd_7740689 : Nat := 4983230072969 + 3 ^ 40 * 7740689 * 2
def baseEnd_7740689 : Nat := 3974694053970770252388725

theorem tailTrace_7740689 : CollatzResearch.WordTrace tailWord_7740689 prefixEnd_7740689 3974694053970770252388725 := by
  unfold tailWord_7740689
  simp only [CollatzResearch.WordTrace]
  refine ⟨282326121853813232276161121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188217414569208821517440747 282326121853813232276161121)
  ·
    refine ⟨211744591390359924207120841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282326121853813232276161121 211744591390359924207120841)
    ·
      refine ⟨158808443542769943155340631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211744591390359924207120841 158808443542769943155340631)
      ·
        refine ⟨238212665314154914733010947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158808443542769943155340631 238212665314154914733010947)
        ·
          refine ⟨357318997971232372099516421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238212665314154914733010947 357318997971232372099516421)
          ·
            refine ⟨66997312119606069768659329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357318997971232372099516421 66997312119606069768659329)
            ·
              refine ⟨50247984089704552326494497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66997312119606069768659329 50247984089704552326494497)
              ·
                refine ⟨37685988067278414244870873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50247984089704552326494497 37685988067278414244870873)
                ·
                  refine ⟨28264491050458810683653155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37685988067278414244870873 28264491050458810683653155)
                  ·
                    refine ⟨42396736575688216025479733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28264491050458810683653155 42396736575688216025479733)
                    ·
                      refine ⟨3974694053970770252388725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42396736575688216025479733 3974694053970770252388725)
                      ·
                        rfl

theorem cell23_7740689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_7740689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740689 prefixEnd_7740689 := by exact prefixLift 7740689
  have htrace : WordTrace (prefixWord ++ tailWord_7740689) baseStart_7740689 baseEnd_7740689 := by
    simpa [prefixWord, tailWord_7740689, baseEnd_7740689] using wordTrace_append hprefix tailTrace_7740689
  have hstable : (prefixWord ++ tailWord_7740689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740689).length < 2 ^ (prefixWord ++ tailWord_7740689).sum := by decide
  have hdescent : baseEnd_7740689 < baseStart_7740689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740737 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7740737 : Nat := 118140960795 + 7740737 * 2 ^ 59
def prefixEnd_7740737 : Nat := 4983230072969 + 3 ^ 40 * 7740737 * 2
def baseEnd_7740737 : Nat := 3974718701042186064588505

theorem tailTrace_7740737 : CollatzResearch.WordTrace tailWord_7740737 prefixEnd_7740737 3974718701042186064588505 := by
  unfold tailWord_7740737
  simp only [CollatzResearch.WordTrace]
  refine ⟨282327872557639336473908465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188218581705092890982605643 282327872557639336473908465)
  ·
    refine ⟨211745904418229502355431349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282327872557639336473908465 211745904418229502355431349)
    ·
      refine ⟨19851178539209015845821689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211745904418229502355431349 19851178539209015845821689)
      ·
        refine ⟨14888383904406761884366267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19851178539209015845821689 14888383904406761884366267)
        ·
          refine ⟨22332575856610142826549401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14888383904406761884366267 22332575856610142826549401)
          ·
            refine ⟨16749431892457607119912051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22332575856610142826549401 16749431892457607119912051)
            ·
              refine ⟨25124147838686410679868077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16749431892457607119912051 25124147838686410679868077)
              ·
                refine ⟨9421555439507404004950529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25124147838686410679868077 9421555439507404004950529)
                ·
                  refine ⟨7066166579630553003712897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9421555439507404004950529 7066166579630553003712897)
                  ·
                    refine ⟨5299624934722914752784673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7066166579630553003712897 5299624934722914752784673)
                    ·
                      refine ⟨3974718701042186064588505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299624934722914752784673 3974718701042186064588505)
                      ·
                        rfl

theorem cell23_7740737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7740737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740737 prefixEnd_7740737 := by exact prefixLift 7740737
  have htrace : WordTrace (prefixWord ++ tailWord_7740737) baseStart_7740737 baseEnd_7740737 := by
    simpa [prefixWord, tailWord_7740737, baseEnd_7740737] using wordTrace_append hprefix tailTrace_7740737
  have hstable : (prefixWord ++ tailWord_7740737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740737).length < 2 ^ (prefixWord ++ tailWord_7740737).sum := by decide
  have hdescent : baseEnd_7740737 < baseStart_7740737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740739 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 6, 5]
def baseStart_7740739 : Nat := 118140960795 + 7740739 * 2 ^ 59
def prefixEnd_7740739 : Nat := 4983230072969 + 3 ^ 40 * 7740739 * 2
def baseEnd_7740739 : Nat := 1324906576001165018921165

theorem tailTrace_7740739 : CollatzResearch.WordTrace tailWord_7740739 prefixEnd_7740739 1324906576001165018921165 := by
  unfold tailWord_7740739
  simp only [CollatzResearch.WordTrace]
  refine ⟨282327945503632090815481271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188218630335754727210320847 282327945503632090815481271)
  ·
    refine ⟨423491918255448136223221907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282327945503632090815481271 423491918255448136223221907)
    ·
      refine ⟨635237877383172204334832861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423491918255448136223221907 635237877383172204334832861)
      ·
        refine ⟨238214204018689576625562323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635237877383172204334832861 238214204018689576625562323)
        ·
          refine ⟨357321306028034364938343485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238214204018689576625562323 357321306028034364938343485)
          ·
            refine ⟨133995489760512886851878807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357321306028034364938343485 133995489760512886851878807)
            ·
              refine ⟨200993234640769330277818211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133995489760512886851878807 200993234640769330277818211)
              ·
                refine ⟨301489851961153995416727317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200993234640769330277818211 301489851961153995416727317)
                ·
                  refine ⟨14132336810679093535159093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301489851961153995416727317 14132336810679093535159093)
                  ·
                    refine ⟨1324906576001165018921165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14132336810679093535159093 1324906576001165018921165)
                    ·
                      rfl

theorem cell23_7740739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 5].length) (baseStart_7740739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740739 prefixEnd_7740739 := by exact prefixLift 7740739
  have htrace : WordTrace (prefixWord ++ tailWord_7740739) baseStart_7740739 baseEnd_7740739 := by
    simpa [prefixWord, tailWord_7740739, baseEnd_7740739] using wordTrace_append hprefix tailTrace_7740739
  have hstable : (prefixWord ++ tailWord_7740739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740739).length < 2 ^ (prefixWord ++ tailWord_7740739).sum := by decide
  have hdescent : baseEnd_7740739 < baseStart_7740739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740758 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7740758 : Nat := 118140960795 + 7740758 * 2 ^ 59
def prefixEnd_7740758 : Nat := 4983230072969 + 3 ^ 40 * 7740758 * 2
def baseEnd_7740758 : Nat := 3974729484135930482425909

theorem tailTrace_7740758 : CollatzResearch.WordTrace tailWord_7740758 prefixEnd_7740758 3974729484135930482425909 := by
  unfold tailWord_7740758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17645539905660203566276433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188219092327042171373615285 17645539905660203566276433)
  ·
    refine ⟨13234154929245152674707325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17645539905660203566276433 13234154929245152674707325)
    ·
      refine ⟨4962808098466932253015247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13234154929245152674707325 4962808098466932253015247)
      ·
        refine ⟨7444212147700398379522871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4962808098466932253015247 7444212147700398379522871)
        ·
          refine ⟨11166318221550597569284307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7444212147700398379522871 11166318221550597569284307)
          ·
            refine ⟨16749477332325896353926461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11166318221550597569284307 16749477332325896353926461)
            ·
              refine ⟨6281053999622211132722423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16749477332325896353926461 6281053999622211132722423)
              ·
                refine ⟨9421580999433316699083635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281053999622211132722423 9421580999433316699083635)
                ·
                  refine ⟨14132371499149975048625453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421580999433316699083635 14132371499149975048625453)
                  ·
                    refine ⟨5299639312181240643234545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14132371499149975048625453 5299639312181240643234545)
                    ·
                      refine ⟨3974729484135930482425909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299639312181240643234545 3974729484135930482425909)
                      ·
                        rfl

theorem cell23_7740758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7740758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740758 prefixEnd_7740758 := by exact prefixLift 7740758
  have htrace : WordTrace (prefixWord ++ tailWord_7740758) baseStart_7740758 baseEnd_7740758 := by
    simpa [prefixWord, tailWord_7740758, baseEnd_7740758] using wordTrace_append hprefix tailTrace_7740758
  have hstable : (prefixWord ++ tailWord_7740758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740758).length < 2 ^ (prefixWord ++ tailWord_7740758).sum := by decide
  have hdescent : baseEnd_7740758 < baseStart_7740758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740796 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_7740796 : Nat := 118140960795 + 7740796 * 2 ^ 59
def prefixEnd_7740796 : Nat := 4983230072969 + 3 ^ 40 * 7740796 * 2
def baseEnd_7740796 : Nat := 3974748996400801333750733

theorem tailTrace_7740796 : CollatzResearch.WordTrace tailWord_7740796 prefixEnd_7740796 3974748996400801333750733 := by
  unfold tailWord_7740796
  simp only [CollatzResearch.WordTrace]
  refine ⟨141165012232212794775153121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188220016309617059700204161 141165012232212794775153121)
  ·
    refine ⟨105873759174159596081364841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141165012232212794775153121 105873759174159596081364841)
    ·
      refine ⟨79405319380619697061023631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105873759174159596081364841 79405319380619697061023631)
      ·
        refine ⟨119107979070929545591535447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79405319380619697061023631 119107979070929545591535447)
        ·
          refine ⟨178661968606394318387303171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119107979070929545591535447 178661968606394318387303171)
          ·
            refine ⟨267992952909591477580954757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178661968606394318387303171 267992952909591477580954757)
            ·
              refine ⟨50248678670548402046429017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 267992952909591477580954757 50248678670548402046429017)
              ·
                refine ⟨37686509002911301534821763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50248678670548402046429017 37686509002911301534821763)
                ·
                  refine ⟨56529763504366952302232645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37686509002911301534821763 56529763504366952302232645)
                  ·
                    refine ⟨10599330657068803556668621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56529763504366952302232645 10599330657068803556668621)
                    ·
                      refine ⟨3974748996400801333750733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10599330657068803556668621 3974748996400801333750733)
                      ·
                        rfl

theorem cell23_7740796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_7740796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740796 prefixEnd_7740796 := by exact prefixLift 7740796
  have htrace : WordTrace (prefixWord ++ tailWord_7740796) baseStart_7740796 baseEnd_7740796 := by
    simpa [prefixWord, tailWord_7740796, baseEnd_7740796] using wordTrace_append hprefix tailTrace_7740796
  have hstable : (prefixWord ++ tailWord_7740796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740796).length < 2 ^ (prefixWord ++ tailWord_7740796).sum := by decide
  have hdescent : baseEnd_7740796 < baseStart_7740796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740803 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 3, 4]
def baseStart_7740803 : Nat := 118140960795 + 7740803 * 2 ^ 59
def prefixEnd_7740803 : Nat := 4983230072969 + 3 ^ 40 * 7740803 * 2
def baseEnd_7740803 : Nat := 1324917530255127602121067

theorem tailTrace_7740803 : CollatzResearch.WordTrace tailWord_7740803 prefixEnd_7740803 1324917530255127602121067 := by
  unfold tailWord_7740803
  simp only [CollatzResearch.WordTrace]
  refine ⟨282330279775400229745811063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188220186516933486497207375 282330279775400229745811063)
  ·
    refine ⟨423495419663100344618716595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282330279775400229745811063 423495419663100344618716595)
    ·
      refine ⟨635243129494650516928074893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423495419663100344618716595 635243129494650516928074893)
      ·
        refine ⟨238216173560493943848028085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 635243129494650516928074893 238216173560493943848028085)
        ·
          refine ⟨22332766271296307235752633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238216173560493943848028085 22332766271296307235752633)
          ·
            refine ⟨16749574703472230426814475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22332766271296307235752633 16749574703472230426814475)
            ·
              refine ⟨25124362055208345640221713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16749574703472230426814475 25124362055208345640221713)
              ·
                refine ⟨18843271541406259230166285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25124362055208345640221713 18843271541406259230166285)
                ·
                  refine ⟨7066226828027347211312357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18843271541406259230166285 7066226828027347211312357)
                  ·
                    refine ⟨1324917530255127602121067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066226828027347211312357 1324917530255127602121067)
                    ·
                      rfl

theorem cell23_7740803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 4].length) (baseStart_7740803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740803 prefixEnd_7740803 := by exact prefixLift 7740803
  have htrace : WordTrace (prefixWord ++ tailWord_7740803) baseStart_7740803 baseEnd_7740803 := by
    simpa [prefixWord, tailWord_7740803, baseEnd_7740803] using wordTrace_append hprefix tailTrace_7740803
  have hstable : (prefixWord ++ tailWord_7740803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740803).length < 2 ^ (prefixWord ++ tailWord_7740803).sum := by decide
  have hdescent : baseEnd_7740803 < baseStart_7740803 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740819 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_7740819 : Nat := 118140960795 + 7740819 * 2 ^ 59
def prefixEnd_7740819 : Nat := 4983230072969 + 3 ^ 40 * 7740819 * 2
def baseEnd_7740819 : Nat := 3974760806455854743763127

theorem tailTrace_7740819 : CollatzResearch.WordTrace tailWord_7740819 prefixEnd_7740819 3974760806455854743763127 := by
  unfold tailWord_7740819
  simp only [CollatzResearch.WordTrace]
  refine ⟨282330863343342264478393511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188220575562228176318929007 282330863343342264478393511)
  ·
    refine ⟨423496295015013396717590267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282330863343342264478393511 423496295015013396717590267)
    ·
      refine ⟨635244442522520095076385401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423496295015013396717590267 635244442522520095076385401)
      ·
        refine ⟨476433331891890071307289051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635244442522520095076385401 476433331891890071307289051)
        ·
          refine ⟨714649997837835106960933577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476433331891890071307289051 714649997837835106960933577)
          ·
            refine ⟨535987498378376330220700183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714649997837835106960933577 535987498378376330220700183)
            ·
              refine ⟨803981247567564495331050275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535987498378376330220700183 803981247567564495331050275)
              ·
                refine ⟨1205971871351346742996575413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 803981247567564495331050275 1205971871351346742996575413)
                ·
                  refine ⟨113059862939188757155928945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1205971871351346742996575413 113059862939188757155928945)
                  ·
                    refine ⟨84794897204391567866946709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113059862939188757155928945 84794897204391567866946709)
                    ·
                      refine ⟨3974760806455854743763127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84794897204391567866946709 3974760806455854743763127)
                      ·
                        rfl

theorem cell23_7740819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_7740819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740819 prefixEnd_7740819 := by exact prefixLift 7740819
  have htrace : WordTrace (prefixWord ++ tailWord_7740819) baseStart_7740819 baseEnd_7740819 := by
    simpa [prefixWord, tailWord_7740819, baseEnd_7740819] using wordTrace_append hprefix tailTrace_7740819
  have hstable : (prefixWord ++ tailWord_7740819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740819).length < 2 ^ (prefixWord ++ tailWord_7740819).sum := by decide
  have hdescent : baseEnd_7740819 < baseStart_7740819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740896 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_7740896 : Nat := 118140960795 + 7740896 * 2 ^ 59
def prefixEnd_7740896 : Nat := 4983230072969 + 3 ^ 40 * 7740896 * 2
def baseEnd_7740896 : Nat := 3974800344466250942500273

theorem tailTrace_7740896 : CollatzResearch.WordTrace tailWord_7740896 prefixEnd_7740896 3974800344466250942500273 := by
  unfold tailWord_7740896
  simp only [CollatzResearch.WordTrace]
  refine ⟨141166835882031653314473271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188222447842708871085964361 141166835882031653314473271)
  ·
    refine ⟨211750253823047479971709907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141166835882031653314473271 211750253823047479971709907)
    ·
      refine ⟨317625380734571219957564861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211750253823047479971709907 317625380734571219957564861)
      ·
        refine ⟨119109517775464207484086823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317625380734571219957564861 119109517775464207484086823)
        ·
          refine ⟨178664276663196311226130235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119109517775464207484086823 178664276663196311226130235)
          ·
            refine ⟨267996414994794466839195353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178664276663196311226130235 267996414994794466839195353)
            ·
              refine ⟨200997311246095850129396515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 267996414994794466839195353 200997311246095850129396515)
              ·
                refine ⟨301495966869143775194094773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 200997311246095850129396515 301495966869143775194094773)
                ·
                  refine ⟨28265246893982228924446385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 301495966869143775194094773 28265246893982228924446385)
                  ·
                    refine ⟨21198935170486671693334789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28265246893982228924446385 21198935170486671693334789)
                    ·
                      refine ⟨3974800344466250942500273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21198935170486671693334789 3974800344466250942500273)
                      ·
                        rfl

theorem cell23_7740896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_7740896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740896 prefixEnd_7740896 := by exact prefixLift 7740896
  have htrace : WordTrace (prefixWord ++ tailWord_7740896) baseStart_7740896 baseEnd_7740896 := by
    simpa [prefixWord, tailWord_7740896, baseEnd_7740896] using wordTrace_append hprefix tailTrace_7740896
  have hstable : (prefixWord ++ tailWord_7740896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740896).length < 2 ^ (prefixWord ++ tailWord_7740896).sum := by decide
  have hdescent : baseEnd_7740896 < baseStart_7740896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740903 : List Nat := [1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7740903 : Nat := 118140960795 + 7740903 * 2 ^ 59
def prefixEnd_7740903 : Nat := 4983230072969 + 3 ^ 40 * 7740903 * 2
def baseEnd_7740903 : Nat := 3974803938830832415112741

theorem tailTrace_7740903 : CollatzResearch.WordTrace tailWord_7740903 prefixEnd_7740903 3974803938830832415112741 := by
  unfold tailWord_7740903
  simp only [CollatzResearch.WordTrace]
  refine ⟨282333927075037946824451363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188222618050025297882967575 282333927075037946824451363)
  ·
    refine ⟨423500890612556920236677045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282333927075037946824451363 423500890612556920236677045)
    ·
      refine ⟨39703208494927211272188473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 423500890612556920236677045 39703208494927211272188473)
      ·
        refine ⟨29777406371195408454141355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39703208494927211272188473 29777406371195408454141355)
        ·
          refine ⟨44666109556793112681212033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29777406371195408454141355 44666109556793112681212033)
          ·
            refine ⟨33499582167594834510909025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44666109556793112681212033 33499582167594834510909025)
            ·
              refine ⟨25124686625696125883181769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33499582167594834510909025 25124686625696125883181769)
              ·
                refine ⟨18843514969272094412386327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25124686625696125883181769 18843514969272094412386327)
                ·
                  refine ⟨28265272453908141618579491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18843514969272094412386327 28265272453908141618579491)
                  ·
                    refine ⟨42397908680862212427869237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28265272453908141618579491 42397908680862212427869237)
                    ·
                      refine ⟨3974803938830832415112741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42397908680862212427869237 3974803938830832415112741)
                      ·
                        rfl

theorem cell23_7740903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7740903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740903 prefixEnd_7740903 := by exact prefixLift 7740903
  have htrace : WordTrace (prefixWord ++ tailWord_7740903) baseStart_7740903 baseEnd_7740903 := by
    simpa [prefixWord, tailWord_7740903, baseEnd_7740903] using wordTrace_append hprefix tailTrace_7740903
  have hstable : (prefixWord ++ tailWord_7740903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740903).length < 2 ^ (prefixWord ++ tailWord_7740903).sum := by decide
  have hdescent : baseEnd_7740903 < baseStart_7740903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740910 : List Nat := [4, 1, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_7740910 : Nat := 118140960795 + 7740910 * 2 ^ 59
def prefixEnd_7740910 : Nat := 4983230072969 + 3 ^ 40 * 7740910 * 2
def baseEnd_7740910 : Nat := 1324935844398471295908403

theorem tailTrace_7740910 : CollatzResearch.WordTrace tailWord_7740910 prefixEnd_7740910 1324935844398471295908403 := by
  unfold tailWord_7740910
  simp only [CollatzResearch.WordTrace]
  refine ⟨35291772798251573377494523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188222788257341724679970789 35291772798251573377494523)
  ·
    refine ⟨52937659197377360066241785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35291772798251573377494523 52937659197377360066241785)
    ·
      refine ⟨39703244398033020049681339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52937659197377360066241785 39703244398033020049681339)
      ·
        refine ⟨59554866597049530074522009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39703244398033020049681339 59554866597049530074522009)
        ·
          refine ⟨44666149947787147555891507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59554866597049530074522009 44666149947787147555891507)
          ·
            refine ⟨66999224921680721333837261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44666149947787147555891507 66999224921680721333837261)
            ·
              refine ⟨25124709345630270500188973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66999224921680721333837261 25124709345630270500188973)
              ·
                refine ⟨9421766004611351437570865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25124709345630270500188973 9421766004611351437570865)
                ·
                  refine ⟨7066324503458513578178149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9421766004611351437570865 7066324503458513578178149)
                  ·
                    refine ⟨1324935844398471295908403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066324503458513578178149 1324935844398471295908403)
                    ·
                      rfl

theorem cell23_7740910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_7740910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740910 prefixEnd_7740910 := by exact prefixLift 7740910
  have htrace : WordTrace (prefixWord ++ tailWord_7740910) baseStart_7740910 baseEnd_7740910 := by
    simpa [prefixWord, tailWord_7740910, baseEnd_7740910] using wordTrace_append hprefix tailTrace_7740910
  have hstable : (prefixWord ++ tailWord_7740910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740910).length < 2 ^ (prefixWord ++ tailWord_7740910).sum := by decide
  have hdescent : baseEnd_7740910 < baseStart_7740910 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740917 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7740917 : Nat := 118140960795 + 7740917 * 2 ^ 59
def prefixEnd_7740917 : Nat := 4983230072969 + 3 ^ 40 * 7740917 * 2
def baseEnd_7740917 : Nat := 3974811127559995360337677

theorem tailTrace_7740917 : CollatzResearch.WordTrace tailWord_7740917 prefixEnd_7740917 3974811127559995360337677 := by
  unfold tailWord_7740917
  simp only [CollatzResearch.WordTrace]
  refine ⟨282334437696987227215461005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188222958464658151476974003 282334437696987227215461005)
  ·
    refine ⟨105875414136370210205797877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282334437696987227215461005 105875414136370210205797877)
    ·
      refine ⟨9925820075284707206793551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105875414136370210205797877 9925820075284707206793551)
      ·
        refine ⟨14888730112927060810190327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9925820075284707206793551 14888730112927060810190327)
        ·
          refine ⟨22333095169390591215285491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14888730112927060810190327 22333095169390591215285491)
          ·
            refine ⟨33499642754085886822928237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22333095169390591215285491 33499642754085886822928237)
            ·
              refine ⟨12562366032782207558598089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33499642754085886822928237 12562366032782207558598089)
              ·
                refine ⟨9421774524586655668948567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12562366032782207558598089 9421774524586655668948567)
                ·
                  refine ⟨14132661786879983503422851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421774524586655668948567 14132661786879983503422851)
                  ·
                    refine ⟨21198992680319975255134277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14132661786879983503422851 21198992680319975255134277)
                    ·
                      refine ⟨3974811127559995360337677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21198992680319975255134277 3974811127559995360337677)
                      ·
                        rfl

theorem cell23_7740917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7740917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740917 prefixEnd_7740917 := by exact prefixLift 7740917
  have htrace : WordTrace (prefixWord ++ tailWord_7740917) baseStart_7740917 baseEnd_7740917 := by
    simpa [prefixWord, tailWord_7740917, baseEnd_7740917] using wordTrace_append hprefix tailTrace_7740917
  have hstable : (prefixWord ++ tailWord_7740917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740917).length < 2 ^ (prefixWord ++ tailWord_7740917).sum := by decide
  have hdescent : baseEnd_7740917 < baseStart_7740917 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740920 : List Nat := [2, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_7740920 : Nat := 118140960795 + 7740920 * 2 ^ 59
def prefixEnd_7740920 : Nat := 4983230072969 + 3 ^ 40 * 7740920 * 2
def baseEnd_7740920 : Nat := 3974812668001958848600163

theorem tailTrace_7740920 : CollatzResearch.WordTrace tailWord_7740920 prefixEnd_7740920 3974812668001958848600163 := by
  unfold tailWord_7740920
  simp only [CollatzResearch.WordTrace]
  refine ⟨141167273557988179363910107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188223031410650905818546809 141167273557988179363910107)
  ·
    refine ⟨211750910336982269045865161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141167273557988179363910107 211750910336982269045865161)
    ·
      refine ⟨158813182752736701784398871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211750910336982269045865161 158813182752736701784398871)
      ·
        refine ⟨238219774129105052676598307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158813182752736701784398871 238219774129105052676598307)
        ·
          refine ⟨357329661193657579014897461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238219774129105052676598307 357329661193657579014897461)
          ·
            refine ⟨33499655736905398032646637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357329661193657579014897461 33499655736905398032646637)
            ·
              refine ⟨12562370901339524262242489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33499655736905398032646637 12562370901339524262242489)
              ·
                refine ⟨9421778176004643196681867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12562370901339524262242489 9421778176004643196681867)
                ·
                  refine ⟨14132667264006964795022801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9421778176004643196681867 14132667264006964795022801)
                  ·
                    refine ⟨10599500448005223596267101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14132667264006964795022801 10599500448005223596267101)
                    ·
                      refine ⟨3974812668001958848600163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10599500448005223596267101 3974812668001958848600163)
                      ·
                        rfl

theorem cell23_7740920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_7740920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740920 prefixEnd_7740920 := by exact prefixLift 7740920
  have htrace : WordTrace (prefixWord ++ tailWord_7740920) baseStart_7740920 baseEnd_7740920 := by
    simpa [prefixWord, tailWord_7740920, baseEnd_7740920] using wordTrace_append hprefix tailTrace_7740920
  have hstable : (prefixWord ++ tailWord_7740920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740920).length < 2 ^ (prefixWord ++ tailWord_7740920).sum := by decide
  have hdescent : baseEnd_7740920 < baseStart_7740920 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740930 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7740930 : Nat := 118140960795 + 7740930 * 2 ^ 59
def prefixEnd_7740930 : Nat := 4983230072969 + 3 ^ 40 * 7740930 * 2
def baseEnd_7740930 : Nat := 3974817802808503809475117

theorem tailTrace_7740930 : CollatzResearch.WordTrace tailWord_7740930 prefixEnd_7740930 3974817802808503809475117 := by
  unfold tailWord_7740930
  simp only [CollatzResearch.WordTrace]
  refine ⟨70583727961485032608921061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188223274563960086957122829 70583727961485032608921061)
  ·
    refine ⟨13234448992778443614172699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70583727961485032608921061 13234448992778443614172699)
    ·
      refine ⟨19851673489167665421259049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13234448992778443614172699 19851673489167665421259049)
      ·
        refine ⟨14888755116875749065944287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19851673489167665421259049 14888755116875749065944287)
        ·
          refine ⟨22333132675313623598916431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14888755116875749065944287 22333132675313623598916431)
          ·
            refine ⟨33499699012970435398374647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22333132675313623598916431 33499699012970435398374647)
            ·
              refine ⟨50249548519455653097561971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33499699012970435398374647 50249548519455653097561971)
              ·
                refine ⟨75374322779183479646342957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50249548519455653097561971 75374322779183479646342957)
                ·
                  refine ⟨28265371042193804867378609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75374322779183479646342957 28265371042193804867378609)
                  ·
                    refine ⟨21199028281645353650533957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28265371042193804867378609 21199028281645353650533957)
                    ·
                      refine ⟨3974817802808503809475117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21199028281645353650533957 3974817802808503809475117)
                      ·
                        rfl

theorem cell23_7740930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7740930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740930 prefixEnd_7740930 := by exact prefixLift 7740930
  have htrace : WordTrace (prefixWord ++ tailWord_7740930) baseStart_7740930 baseEnd_7740930 := by
    simpa [prefixWord, tailWord_7740930, baseEnd_7740930] using wordTrace_append hprefix tailTrace_7740930
  have hstable : (prefixWord ++ tailWord_7740930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740930).length < 2 ^ (prefixWord ++ tailWord_7740930).sum := by decide
  have hdescent : baseEnd_7740930 < baseStart_7740930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7740993 : List Nat := [1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_7740993 : Nat := 118140960795 + 7740993 * 2 ^ 59
def prefixEnd_7740993 : Nat := 4983230072969 + 3 ^ 40 * 7740993 * 2
def baseEnd_7740993 : Nat := 3974850152089737062987327

theorem tailTrace_7740993 : CollatzResearch.WordTrace tailWord_7740993 prefixEnd_7740993 3974850152089737062987327 := by
  unfold tailWord_7740993
  simp only [CollatzResearch.WordTrace]
  refine ⟨282337209644711892195227633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188224806429807928130151755 282337209644711892195227633)
  ·
    refine ⟨211752907233533919146420725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282337209644711892195227633 211752907233533919146420725)
    ·
      refine ⟨19851835053143804919976943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211752907233533919146420725 19851835053143804919976943)
      ·
        refine ⟨29777752579715707379965415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19851835053143804919976943 29777752579715707379965415)
        ·
          refine ⟨44666628869573561069948123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29777752579715707379965415 44666628869573561069948123)
          ·
            refine ⟨66999943304360341604922185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44666628869573561069948123 66999943304360341604922185)
            ·
              refine ⟨50249957478270256203691639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66999943304360341604922185 50249957478270256203691639)
              ·
                refine ⟨75374936217405384305537459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50249957478270256203691639 75374936217405384305537459)
                ·
                  refine ⟨113062404326108076458306189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75374936217405384305537459 113062404326108076458306189)
                  ·
                    refine ⟨42398401622290528671864821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113062404326108076458306189 42398401622290528671864821)
                    ·
                      refine ⟨3974850152089737062987327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42398401622290528671864821 3974850152089737062987327)
                      ·
                        rfl

theorem cell23_7740993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_7740993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7740993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7740993 prefixEnd_7740993 := by exact prefixLift 7740993
  have htrace : WordTrace (prefixWord ++ tailWord_7740993) baseStart_7740993 baseEnd_7740993 := by
    simpa [prefixWord, tailWord_7740993, baseEnd_7740993] using wordTrace_append hprefix tailTrace_7740993
  have hstable : (prefixWord ++ tailWord_7740993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7740993).length < 2 ^ (prefixWord ++ tailWord_7740993).sum := by decide
  have hdescent : baseEnd_7740993 < baseStart_7740993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7740993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741020 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_7741020 : Nat := 118140960795 + 7741020 * 2 ^ 59
def prefixEnd_7741020 : Nat := 4983230072969 + 3 ^ 40 * 7741020 * 2
def baseEnd_7741020 : Nat := 3974864016067408457349703

theorem tailTrace_7741020 : CollatzResearch.WordTrace tailWord_7741020 prefixEnd_7741020 3974864016067408457349703 := by
  unfold tailWord_7741020
  simp only [CollatzResearch.WordTrace]
  refine ⟨141169097207807037903230257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188225462943742717204307009 141169097207807037903230257)
  ·
    refine ⟨105876822905855278427422693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141169097207807037903230257 105876822905855278427422693)
    ·
      refine ⟨19851904294847864705141755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105876822905855278427422693 19851904294847864705141755)
      ·
        refine ⟨29777856442271797057712633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19851904294847864705141755 29777856442271797057712633)
        ·
          refine ⟨22333392331703847793284475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29777856442271797057712633 22333392331703847793284475)
          ·
            refine ⟨33500088497555771689926713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22333392331703847793284475 33500088497555771689926713)
            ·
              refine ⟨25125066373166828767445035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33500088497555771689926713 25125066373166828767445035)
              ·
                refine ⟨37687599559750243151167553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25125066373166828767445035 37687599559750243151167553)
                ·
                  refine ⟨28265699669812682363375665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37687599559750243151167553 28265699669812682363375665)
                  ·
                    refine ⟨21199274752359511772531749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28265699669812682363375665 21199274752359511772531749)
                    ·
                      refine ⟨3974864016067408457349703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21199274752359511772531749 3974864016067408457349703)
                      ·
                        rfl

theorem cell23_7741020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_7741020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741020 prefixEnd_7741020 := by exact prefixLift 7741020
  have htrace : WordTrace (prefixWord ++ tailWord_7741020) baseStart_7741020 baseEnd_7741020 := by
    simpa [prefixWord, tailWord_7741020, baseEnd_7741020] using wordTrace_append hprefix tailTrace_7741020
  have hstable : (prefixWord ++ tailWord_7741020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741020).length < 2 ^ (prefixWord ++ tailWord_7741020).sum := by decide
  have hdescent : baseEnd_7741020 < baseStart_7741020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741064 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 7]
def baseStart_7741064 : Nat := 118140960795 + 7741064 * 2 ^ 59
def prefixEnd_7741064 : Nat := 4983230072969 + 3 ^ 40 * 7741064 * 2
def baseEnd_7741064 : Nat := 441654067690689587244389

theorem tailTrace_7741064 : CollatzResearch.WordTrace tailWord_7741064 prefixEnd_7741064 441654067690689587244389 := by
  unfold tailWord_7741064
  simp only [CollatzResearch.WordTrace]
  refine ⟨141169899613727335660531123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188226532818303114214041497 141169899613727335660531123)
  ·
    refine ⟨211754849420591003490796685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141169899613727335660531123 211754849420591003490796685)
    ·
      refine ⟨79408068532721626309048757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211754849420591003490796685 79408068532721626309048757)
      ·
        refine ⟨7444506424942652466473321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79408068532721626309048757 7444506424942652466473321)
        ·
          refine ⟨5583379818706989349854991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7444506424942652466473321 5583379818706989349854991)
          ·
            refine ⟨8375069728060484024782487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5583379818706989349854991 8375069728060484024782487)
            ·
              refine ⟨12562604592090726037173731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375069728060484024782487 12562604592090726037173731)
              ·
                refine ⟨18843906888136089055760597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12562604592090726037173731 18843906888136089055760597)
                ·
                  refine ⟨441654067690689587244389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18843906888136089055760597 441654067690689587244389)
                  ·
                    rfl

theorem cell23_7741064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 7].length) (baseStart_7741064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741064 prefixEnd_7741064 := by exact prefixLift 7741064
  have htrace : WordTrace (prefixWord ++ tailWord_7741064) baseStart_7741064 baseEnd_7741064 := by
    simpa [prefixWord, tailWord_7741064, baseEnd_7741064] using wordTrace_append hprefix tailTrace_7741064
  have hstable : (prefixWord ++ tailWord_7741064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741064).length < 2 ^ (prefixWord ++ tailWord_7741064).sum := by decide
  have hdescent : baseEnd_7741064 < baseStart_7741064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741070 : List Nat := [4, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7741070 : Nat := 118140960795 + 7741070 * 2 ^ 59
def prefixEnd_7741070 : Nat := 4983230072969 + 3 ^ 40 * 7741070 * 2
def baseEnd_7741070 : Nat := 3974889690100133261724473

theorem tailTrace_7741070 : CollatzResearch.WordTrace tailWord_7741070 prefixEnd_7741070 3974889690100133261724473 := by
  unfold tailWord_7741070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35292502258179116793222583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 188226678710288622897187109 35292502258179116793222583)
  ·
    refine ⟨52938753387268675189833875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35292502258179116793222583 52938753387268675189833875)
    ·
      refine ⟨79408130080903012784750813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52938753387268675189833875 79408130080903012784750813)
      ·
        refine ⟨29778048780338629794281555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79408130080903012784750813 29778048780338629794281555)
        ·
          refine ⟨44667073170507944691422333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778048780338629794281555 44667073170507944691422333)
          ·
            refine ⟨16750152438940479259283375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44667073170507944691422333 16750152438940479259283375)
            ·
              refine ⟨25125228658410718888925063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16750152438940479259283375 25125228658410718888925063)
              ·
                refine ⟨37687842987616078333387595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25125228658410718888925063 37687842987616078333387595)
                ·
                  refine ⟨56531764481424117500081393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37687842987616078333387595 56531764481424117500081393)
                  ·
                    refine ⟨42398823361068088125061045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56531764481424117500081393 42398823361068088125061045)
                    ·
                      refine ⟨3974889690100133261724473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42398823361068088125061045 3974889690100133261724473)
                      ·
                        rfl

theorem cell23_7741070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7741070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741070 prefixEnd_7741070 := by exact prefixLift 7741070
  have htrace : WordTrace (prefixWord ++ tailWord_7741070) baseStart_7741070 baseEnd_7741070 := by
    simpa [prefixWord, tailWord_7741070, baseEnd_7741070] using wordTrace_append hprefix tailTrace_7741070
  have hstable : (prefixWord ++ tailWord_7741070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741070).length < 2 ^ (prefixWord ++ tailWord_7741070).sum := by decide
  have hdescent : baseEnd_7741070 < baseStart_7741070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741093 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_7741093 : Nat := 118140960795 + 7741093 * 2 ^ 59
def prefixEnd_7741093 : Nat := 4983230072969 + 3 ^ 40 * 7741093 * 2
def baseEnd_7741093 : Nat := 3974901500155186671736867

theorem tailTrace_7741093 : CollatzResearch.WordTrace tailWord_7741093 prefixEnd_7741093 3974901500155186671736867 := by
  unfold tailWord_7741093
  simp only [CollatzResearch.WordTrace]
  refine ⟨282340856944349609273867933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188227237962899739515911955 282340856944349609273867933)
  ·
    refine ⟨105877821354131103477700475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282340856944349609273867933 105877821354131103477700475)
    ·
      refine ⟨158816732031196655216550713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105877821354131103477700475 158816732031196655216550713)
      ·
        refine ⟨119112549023397491412413035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158816732031196655216550713 119112549023397491412413035)
        ·
          refine ⟨178668823535096237118619553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119112549023397491412413035 178668823535096237118619553)
          ·
            refine ⟨134001617651322177838964665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178668823535096237118619553 134001617651322177838964665)
            ·
              refine ⟨100501213238491633379223499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134001617651322177838964665 100501213238491633379223499)
              ·
                refine ⟨150751819857737450068835249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100501213238491633379223499 150751819857737450068835249)
                ·
                  refine ⟨113063864893303087551626437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150751819857737450068835249 113063864893303087551626437)
                  ·
                    refine ⟨21199474667494328915929957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 113063864893303087551626437 21199474667494328915929957)
                    ·
                      refine ⟨3974901500155186671736867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21199474667494328915929957 3974901500155186671736867)
                      ·
                        rfl

theorem cell23_7741093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_7741093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741093 prefixEnd_7741093 := by exact prefixLift 7741093
  have htrace : WordTrace (prefixWord ++ tailWord_7741093) baseStart_7741093 baseEnd_7741093 := by
    simpa [prefixWord, tailWord_7741093, baseEnd_7741093] using wordTrace_append hprefix tailTrace_7741093
  have hstable : (prefixWord ++ tailWord_7741093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741093).length < 2 ^ (prefixWord ++ tailWord_7741093).sum := by decide
  have hdescent : baseEnd_7741093 < baseStart_7741093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741107 : List Nat := [1, 1, 1, 2, 3, 3, 2, 5, 1, 4]
def baseStart_7741107 : Nat := 118140960795 + 7741107 * 2 ^ 59
def prefixEnd_7741107 : Nat := 4983230072969 + 3 ^ 40 * 7741107 * 2
def baseEnd_7741107 : Nat := 1324969562961449872320601

theorem tailTrace_7741107 : CollatzResearch.WordTrace tailWord_7741107 prefixEnd_7741107 1324969562961449872320601 := by
  unfold tailWord_7741107
  simp only [CollatzResearch.WordTrace]
  refine ⟨282341367566298889664877575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188227578377532593109918383 282341367566298889664877575)
  ·
    refine ⟨423512051349448334497316363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282341367566298889664877575 423512051349448334497316363)
    ·
      refine ⟨635268077024172501745974545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423512051349448334497316363 635268077024172501745974545)
      ·
        refine ⟨476451057768129376309480909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635268077024172501745974545 476451057768129376309480909)
        ·
          refine ⟨178669146663048516116055341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476451057768129376309480909 178669146663048516116055341)
          ·
            refine ⟨67000929998643193543520753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178669146663048516116055341 67000929998643193543520753)
            ·
              refine ⟨50250697498982395157640565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67000929998643193543520753 50250697498982395157640565)
              ·
                refine ⟨4711002890529599546028803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50250697498982395157640565 4711002890529599546028803)
                ·
                  refine ⟨7066504335794399319043205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711002890529599546028803 7066504335794399319043205)
                  ·
                    refine ⟨1324969562961449872320601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066504335794399319043205 1324969562961449872320601)
                    ·
                      rfl

theorem cell23_7741107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 5, 1, 4].length) (baseStart_7741107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741107 prefixEnd_7741107 := by exact prefixLift 7741107
  have htrace : WordTrace (prefixWord ++ tailWord_7741107) baseStart_7741107 baseEnd_7741107 := by
    simpa [prefixWord, tailWord_7741107, baseEnd_7741107] using wordTrace_append hprefix tailTrace_7741107
  have hstable : (prefixWord ++ tailWord_7741107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741107).length < 2 ^ (prefixWord ++ tailWord_7741107).sum := by decide
  have hdescent : baseEnd_7741107 < baseStart_7741107 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741120 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 6]
def baseStart_7741120 : Nat := 118140960795 + 7741120 * 2 ^ 59
def prefixEnd_7741120 : Nat := 4983230072969 + 3 ^ 40 * 7741120 * 2
def baseEnd_7741120 : Nat := 441657262681428674011027

theorem tailTrace_7741120 : CollatzResearch.WordTrace tailWord_7741120 prefixEnd_7741120 441657262681428674011027 := by
  unfold tailWord_7741120
  simp only [CollatzResearch.WordTrace]
  refine ⟨141170920857625896442550407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188227894476834528590067209 141170920857625896442550407)
  ·
    refine ⟨211756381286438844663825611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141170920857625896442550407 211756381286438844663825611)
    ·
      refine ⟨317634571929658266995738417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211756381286438844663825611 317634571929658266995738417)
      ·
        refine ⟨238225928947243700246803813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317634571929658266995738417 238225928947243700246803813)
        ·
          refine ⟨44667361677608193796275715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238225928947243700246803813 44667361677608193796275715)
          ·
            refine ⟨67001042516412290694413573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44667361677608193796275715 67001042516412290694413573)
            ·
              refine ⟨12562695471827304505202545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67001042516412290694413573 12562695471827304505202545)
              ·
                refine ⟨9422021603870478378901909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12562695471827304505202545 9422021603870478378901909)
                ·
                  refine ⟨441657262681428674011027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9422021603870478378901909 441657262681428674011027)
                  ·
                    rfl

theorem cell23_7741120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_7741120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741120 prefixEnd_7741120 := by exact prefixLift 7741120
  have htrace : WordTrace (prefixWord ++ tailWord_7741120) baseStart_7741120 baseEnd_7741120 := by
    simpa [prefixWord, tailWord_7741120, baseEnd_7741120] using wordTrace_append hprefix tailTrace_7741120
  have hstable : (prefixWord ++ tailWord_7741120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741120).length < 2 ^ (prefixWord ++ tailWord_7741120).sum := by decide
  have hdescent : baseEnd_7741120 < baseStart_7741120 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741124 : List Nat := [2, 3, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_7741124 : Nat := 118140960795 + 7741124 * 2 ^ 59
def prefixEnd_7741124 : Nat := 4983230072969 + 3 ^ 40 * 7741124 * 2
def baseEnd_7741124 : Nat := 1324972472685158683483075

theorem tailTrace_7741124 : CollatzResearch.WordTrace tailWord_7741124 prefixEnd_7741124 1324972472685158683483075 := by
  unfold tailWord_7741124
  simp only [CollatzResearch.WordTrace]
  refine ⟨141170993803618650784123213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188227991738158201045497617 141170993803618650784123213)
  ·
    refine ⟨52939122676356994044046205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141170993803618650784123213 52939122676356994044046205)
    ·
      refine ⟨19852171003633872766517327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52939122676356994044046205 19852171003633872766517327)
      ·
        refine ⟨29778256505450809149775991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19852171003633872766517327 29778256505450809149775991)
        ·
          refine ⟨44667384758176213724663987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778256505450809149775991 44667384758176213724663987)
          ·
            refine ⟨67001077137264320586995981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44667384758176213724663987 67001077137264320586995981)
            ·
              refine ⟨25125403926474120220123493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67001077137264320586995981 25125403926474120220123493)
              ·
                refine ⟨4711013236213897541273155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25125403926474120220123493 4711013236213897541273155)
                ·
                  refine ⟨7066519854320846311909733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711013236213897541273155 7066519854320846311909733)
                  ·
                    refine ⟨1324972472685158683483075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066519854320846311909733 1324972472685158683483075)
                    ·
                      rfl

theorem cell23_7741124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_7741124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741124 prefixEnd_7741124 := by exact prefixLift 7741124
  have htrace : WordTrace (prefixWord ++ tailWord_7741124) baseStart_7741124 baseEnd_7741124 := by
    simpa [prefixWord, tailWord_7741124, baseEnd_7741124] using wordTrace_append hprefix tailTrace_7741124
  have hstable : (prefixWord ++ tailWord_7741124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741124).length < 2 ^ (prefixWord ++ tailWord_7741124).sum := by decide
  have hdescent : baseEnd_7741124 < baseStart_7741124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741143 : List Nat := [1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_7741143 : Nat := 118140960795 + 7741143 * 2 ^ 59
def prefixEnd_7741143 : Nat := 4983230072969 + 3 ^ 40 * 7741143 * 2
def baseEnd_7741143 : Nat := 3974927174187911476111637

theorem tailTrace_7741143 : CollatzResearch.WordTrace tailWord_7741143 prefixEnd_7741143 3974927174187911476111637 := by
  unfold tailWord_7741143
  simp only [CollatzResearch.WordTrace]
  refine ⟨282342680594168467813188083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188228453729445645208792055 282342680594168467813188083)
  ·
    refine ⟨423514020891252701719782125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282342680594168467813188083 423514020891252701719782125)
    ·
      refine ⟨158817757834219763144918297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 423514020891252701719782125 158817757834219763144918297)
      ·
        refine ⟨119113318375664822358688723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158817757834219763144918297 119113318375664822358688723)
        ·
          refine ⟨178669977563497233538033085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119113318375664822358688723 178669977563497233538033085)
          ·
            refine ⟨67001241586311462576762407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178669977563497233538033085 67001241586311462576762407)
            ·
              refine ⟨100501862379467193865143611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67001241586311462576762407 100501862379467193865143611)
              ·
                refine ⟨150752793569200790797715417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100501862379467193865143611 150752793569200790797715417)
                ·
                  refine ⟨113064595176900593098286563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 150752793569200790797715417 113064595176900593098286563)
                  ·
                    refine ⟨169596892765350889647429845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113064595176900593098286563 169596892765350889647429845)
                    ·
                      refine ⟨3974927174187911476111637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 169596892765350889647429845 3974927174187911476111637)
                      ·
                        rfl

theorem cell23_7741143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_7741143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741143 prefixEnd_7741143 := by exact prefixLift 7741143
  have htrace : WordTrace (prefixWord ++ tailWord_7741143) baseStart_7741143 baseEnd_7741143 := by
    simpa [prefixWord, tailWord_7741143, baseEnd_7741143] using wordTrace_append hprefix tailTrace_7741143
  have hstable : (prefixWord ++ tailWord_7741143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741143).length < 2 ^ (prefixWord ++ tailWord_7741143).sum := by decide
  have hdescent : baseEnd_7741143 < baseStart_7741143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741157 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 1, 5, 2]
def baseStart_7741157 : Nat := 118140960795 + 7741157 * 2 ^ 59
def prefixEnd_7741157 : Nat := 4983230072969 + 3 ^ 40 * 7741157 * 2
def baseEnd_7741157 : Nat := 3974934362917074421336573

theorem tailTrace_7741157 : CollatzResearch.WordTrace tailWord_7741157 prefixEnd_7741157 3974934362917074421336573 := by
  unfold tailWord_7741157
  simp only [CollatzResearch.WordTrace]
  refine ⟨282343191216117748204197725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188228794144078498802798483 282343191216117748204197725)
  ·
    refine ⟨105878696706044155576574147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 282343191216117748204197725 105878696706044155576574147)
    ·
      refine ⟨158818045059066233364861221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105878696706044155576574147 158818045059066233364861221)
      ·
        refine ⟨29778383448574918755911479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 158818045059066233364861221 29778383448574918755911479)
        ·
          refine ⟨44667575172862378133867219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778383448574918755911479 44667575172862378133867219)
          ·
            refine ⟨67001362759293567200800829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44667575172862378133867219 67001362759293567200800829)
            ·
              refine ⟨25125511034735087700300311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67001362759293567200800829 25125511034735087700300311)
              ·
                refine ⟨37688266552102631550450467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25125511034735087700300311 37688266552102631550450467)
                ·
                  refine ⟨56532399828153947325675701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37688266552102631550450467 56532399828153947325675701)
                  ·
                    refine ⟨5299912483889432561782097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56532399828153947325675701 5299912483889432561782097)
                    ·
                      refine ⟨3974934362917074421336573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299912483889432561782097 3974934362917074421336573)
                      ·
                        rfl

theorem cell23_7741157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_7741157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741157 prefixEnd_7741157 := by exact prefixLift 7741157
  have htrace : WordTrace (prefixWord ++ tailWord_7741157) baseStart_7741157 baseEnd_7741157 := by
    simpa [prefixWord, tailWord_7741157, baseEnd_7741157] using wordTrace_append hprefix tailTrace_7741157
  have hstable : (prefixWord ++ tailWord_7741157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741157).length < 2 ^ (prefixWord ++ tailWord_7741157).sum := by decide
  have hdescent : baseEnd_7741157 < baseStart_7741157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741164 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 1, 1, 3]
def baseStart_7741164 : Nat := 118140960795 + 7741164 * 2 ^ 59
def prefixEnd_7741164 : Nat := 4983230072969 + 3 ^ 40 * 7741164 * 2
def baseEnd_7741164 : Nat := 3974937957281655893949041

theorem tailTrace_7741164 : CollatzResearch.WordTrace tailWord_7741164 prefixEnd_7741164 3974937957281655893949041 := by
  unfold tailWord_7741164
  simp only [CollatzResearch.WordTrace]
  refine ⟨141171723263546194199851273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188228964351394925599801697 141171723263546194199851273)
  ·
    refine ⟨105878792447659645649888455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141171723263546194199851273 105878792447659645649888455)
    ·
      refine ⟨158818188671489468474832683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105878792447659645649888455 158818188671489468474832683)
      ·
        refine ⟨238227283007234202712249025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158818188671489468474832683 238227283007234202712249025)
        ·
          refine ⟨178670462255425652034186769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238227283007234202712249025 178670462255425652034186769)
          ·
            refine ⟨134002846691569239025640077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178670462255425652034186769 134002846691569239025640077)
            ·
              refine ⟨50251067509338464634615029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134002846691569239025640077 50251067509338464634615029)
              ·
                refine ⟨4711037579000481059495159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50251067509338464634615029 4711037579000481059495159)
                ·
                  refine ⟨7066556368500721589242739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4711037579000481059495159 7066556368500721589242739)
                  ·
                    refine ⟨10599834552751082383864109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7066556368500721589242739 10599834552751082383864109)
                    ·
                      refine ⟨3974937957281655893949041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10599834552751082383864109 3974937957281655893949041)
                      ·
                        rfl

theorem cell23_7741164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 1, 1, 3].length) (baseStart_7741164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741164 prefixEnd_7741164 := by exact prefixLift 7741164
  have htrace : WordTrace (prefixWord ++ tailWord_7741164) baseStart_7741164 baseEnd_7741164 := by
    simpa [prefixWord, tailWord_7741164, baseEnd_7741164] using wordTrace_append hprefix tailTrace_7741164
  have hstable : (prefixWord ++ tailWord_7741164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741164).length < 2 ^ (prefixWord ++ tailWord_7741164).sum := by decide
  have hdescent : baseEnd_7741164 < baseStart_7741164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741193 : List Nat := [1, 2, 1, 1, 3, 2, 1, 12]
def baseStart_7741193 : Nat := 118140960795 + 7741193 * 2 ^ 59
def prefixEnd_7741193 : Nat := 4983230072969 + 3 ^ 40 * 7741193 * 2
def baseEnd_7741193 : Nat := 147220475860023565943941

theorem tailTrace_7741193 : CollatzResearch.WordTrace tailWord_7741193 prefixEnd_7741193 147220475860023565943941 := by
  unfold tailWord_7741193
  simp only [CollatzResearch.WordTrace]
  refine ⟨282344504243987326352508233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188229669495991550901672155 282344504243987326352508233)
  ·
    refine ⟨211758378182990494764381175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282344504243987326352508233 211758378182990494764381175)
    ·
      refine ⟨317637567274485742146571763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211758378182990494764381175 317637567274485742146571763)
      ·
        refine ⟨476456350911728613219857645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317637567274485742146571763 476456350911728613219857645)
        ·
          refine ⟨178671131591898229957446617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476456350911728613219857645 178671131591898229957446617)
          ·
            refine ⟨134003348693923672468084963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178671131591898229957446617 134003348693923672468084963)
            ·
              refine ⟨201005023040885508702127445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134003348693923672468084963 201005023040885508702127445)
              ·
                refine ⟨147220475860023565943941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 201005023040885508702127445 147220475860023565943941)
                ·
                  rfl

theorem cell23_7741193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 12].length) (baseStart_7741193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741193 prefixEnd_7741193 := by exact prefixLift 7741193
  have htrace : WordTrace (prefixWord ++ tailWord_7741193) baseStart_7741193 baseEnd_7741193 := by
    simpa [prefixWord, tailWord_7741193, baseEnd_7741193] using wordTrace_append hprefix tailTrace_7741193
  have hstable : (prefixWord ++ tailWord_7741193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741193).length < 2 ^ (prefixWord ++ tailWord_7741193).sum := by decide
  have hdescent : baseEnd_7741193 < baseStart_7741193 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741210 : List Nat := [3, 1, 1, 3, 2, 3, 1, 9]
def baseStart_7741210 : Nat := 118140960795 + 7741210 * 2 ^ 59
def prefixEnd_7741210 : Nat := 4983230072969 + 3 ^ 40 * 7741210 * 2
def baseEnd_7741210 : Nat := 147220799162657878295327

theorem tailTrace_7741210 : CollatzResearch.WordTrace tailWord_7741210 prefixEnd_7741210 147220799162657878295327 := by
  unfold tailWord_7741210
  simp only [CollatzResearch.WordTrace]
  refine ⟨70586281071231434563969271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 188230082856617158837251389 70586281071231434563969271)
  ·
    refine ⟨105879421606847151845953907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70586281071231434563969271 105879421606847151845953907)
    ·
      refine ⟨158819132410270727768930861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105879421606847151845953907 158819132410270727768930861)
      ·
        refine ⟨59557174653851522913349073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158819132410270727768930861 59557174653851522913349073)
        ·
          refine ⟨44667880990388642185011805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59557174653851522913349073 44667880990388642185011805)
          ·
            refine ⟨16750455371395740819379427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44667880990388642185011805 16750455371395740819379427)
            ·
              refine ⟨25125683057093611229069141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16750455371395740819379427 25125683057093611229069141)
              ·
                refine ⟨147220799162657878295327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25125683057093611229069141 147220799162657878295327)
                ·
                  rfl

theorem cell23_7741210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_7741210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741210 prefixEnd_7741210 := by exact prefixLift 7741210
  have htrace : WordTrace (prefixWord ++ tailWord_7741210) baseStart_7741210 baseEnd_7741210 := by
    simpa [prefixWord, tailWord_7741210, baseEnd_7741210] using wordTrace_append hprefix tailTrace_7741210
  have hstable : (prefixWord ++ tailWord_7741210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741210).length < 2 ^ (prefixWord ++ tailWord_7741210).sum := by decide
  have hdescent : baseEnd_7741210 < baseStart_7741210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741224 : List Nat := [2, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7741224 : Nat := 118140960795 + 7741224 * 2 ^ 59
def prefixEnd_7741224 : Nat := 4983230072969 + 3 ^ 40 * 7741224 * 2
def baseEnd_7741224 : Nat := 3974968766120925659198765

theorem tailTrace_7741224 : CollatzResearch.WordTrace tailWord_7741224 prefixEnd_7741224 3974968766120925659198765 := by
  unfold tailWord_7741224
  simp only [CollatzResearch.WordTrace]
  refine ⟨141172817453437509323443363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188230423271250012431257817 141172817453437509323443363)
  ·
    refine ⟨211759226180156263985165045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141172817453437509323443363 211759226180156263985165045)
    ·
      refine ⟨19852427454389649748609223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211759226180156263985165045 19852427454389649748609223)
      ·
        refine ⟨29778641181584474622913835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19852427454389649748609223 29778641181584474622913835)
        ·
          refine ⟨44667961772376711934370753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29778641181584474622913835 44667961772376711934370753)
          ·
            refine ⟨33500971329282533950778065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44667961772376711934370753 33500971329282533950778065)
            ·
              refine ⟨25125728496961900463083549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33500971329282533950778065 25125728496961900463083549)
              ·
                refine ⟨9422148186360712673656331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25125728496961900463083549 9422148186360712673656331)
                ·
                  refine ⟨14133222279541069010484497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422148186360712673656331 14133222279541069010484497)
                  ·
                    refine ⟨10599916709655801757863373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14133222279541069010484497 10599916709655801757863373)
                    ·
                      refine ⟨3974968766120925659198765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10599916709655801757863373 3974968766120925659198765)
                      ·
                        rfl

theorem cell23_7741224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7741224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741224 prefixEnd_7741224 := by exact prefixLift 7741224
  have htrace : WordTrace (prefixWord ++ tailWord_7741224) baseStart_7741224 baseEnd_7741224 := by
    simpa [prefixWord, tailWord_7741224, baseEnd_7741224] using wordTrace_append hprefix tailTrace_7741224
  have hstable : (prefixWord ++ tailWord_7741224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741224).length < 2 ^ (prefixWord ++ tailWord_7741224).sum := by decide
  have hdescent : baseEnd_7741224 < baseStart_7741224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741238 : List Nat := [5, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7741238 : Nat := 118140960795 + 7741238 * 2 ^ 59
def prefixEnd_7741238 : Nat := 4983230072969 + 3 ^ 40 * 7741238 * 2
def baseEnd_7741238 : Nat := 3974975954850088604423701

theorem tailTrace_7741238 : CollatzResearch.WordTrace tailWord_7741238 prefixEnd_7741238 3974975954850088604423701 := by
  unfold tailWord_7741238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17646634095551518689868523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 188230763685882866025264245 17646634095551518689868523)
  ·
    refine ⟨26469951143327278034802785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17646634095551518689868523 26469951143327278034802785)
    ·
      refine ⟨19852463357495458526102089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26469951143327278034802785 19852463357495458526102089)
      ·
        refine ⟨14889347518121593894576567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19852463357495458526102089 14889347518121593894576567)
        ·
          refine ⟨22334021277182390841864851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14889347518121593894576567 22334021277182390841864851)
          ·
            refine ⟨33501031915773586262797277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22334021277182390841864851 33501031915773586262797277)
            ·
              refine ⟨12562886968415094848548979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33501031915773586262797277 12562886968415094848548979)
              ·
                refine ⟨18844330452622642272823469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12562886968415094848548979 18844330452622642272823469)
                ·
                  refine ⟨7066623919733490852308801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18844330452622642272823469 7066623919733490852308801)
                  ·
                    refine ⟨5299967939800118139231601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7066623919733490852308801 5299967939800118139231601)
                    ·
                      refine ⟨3974975954850088604423701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299967939800118139231601 3974975954850088604423701)
                      ·
                        rfl

theorem cell23_7741238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7741238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741238 prefixEnd_7741238 := by exact prefixLift 7741238
  have htrace : WordTrace (prefixWord ++ tailWord_7741238) baseStart_7741238 baseEnd_7741238 := by
    simpa [prefixWord, tailWord_7741238, baseEnd_7741238] using wordTrace_append hprefix tailTrace_7741238
  have hstable : (prefixWord ++ tailWord_7741238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741238).length < 2 ^ (prefixWord ++ tailWord_7741238).sum := by decide
  have hdescent : baseEnd_7741238 < baseStart_7741238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741281 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_7741281 : Nat := 118140960795 + 7741281 * 2 ^ 59
def prefixEnd_7741281 : Nat := 4983230072969 + 3 ^ 40 * 7741281 * 2
def baseEnd_7741281 : Nat := 3974998034518231936186003

theorem tailTrace_7741281 : CollatzResearch.WordTrace tailWord_7741281 prefixEnd_7741281 3974998034518231936186003 := by
  unfold tailWord_7741281
  simp only [CollatzResearch.WordTrace]
  refine ⟨282347713867668517381711697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188231809245112344921141131 282347713867668517381711697)
  ·
    refine ⟨211760785400751388036283773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282347713867668517381711697 211760785400751388036283773)
    ·
      refine ⟨79410294525281770513606415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211760785400751388036283773 79410294525281770513606415)
      ·
        refine ⟨119115441787922655770409623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79410294525281770513606415 119115441787922655770409623)
        ·
          refine ⟨178673162681883983655614435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119115441787922655770409623 178673162681883983655614435)
          ·
            refine ⟨268009744022825975483421653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178673162681883983655614435 268009744022825975483421653)
            ·
              refine ⟨6281478375534983800392695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268009744022825975483421653 6281478375534983800392695)
              ·
                refine ⟨9422217563302475700589043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281478375534983800392695 9422217563302475700589043)
                ·
                  refine ⟨14133326344953713550883565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9422217563302475700589043 14133326344953713550883565)
                  ·
                    refine ⟨5299997379357642581581337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14133326344953713550883565 5299997379357642581581337)
                    ·
                      refine ⟨3974998034518231936186003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5299997379357642581581337 3974998034518231936186003)
                      ·
                        rfl

theorem cell23_7741281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_7741281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741281 prefixEnd_7741281 := by exact prefixLift 7741281
  have htrace : WordTrace (prefixWord ++ tailWord_7741281) baseStart_7741281 baseEnd_7741281 := by
    simpa [prefixWord, tailWord_7741281, baseEnd_7741281] using wordTrace_append hprefix tailTrace_7741281
  have hstable : (prefixWord ++ tailWord_7741281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741281).length < 2 ^ (prefixWord ++ tailWord_7741281).sum := by decide
  have hdescent : baseEnd_7741281 < baseStart_7741281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741345 : List Nat := [1, 2, 3, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_7741345 : Nat := 118140960795 + 7741345 * 2 ^ 59
def prefixEnd_7741345 : Nat := 4983230072969 + 3 ^ 40 * 7741345 * 2
def baseEnd_7741345 : Nat := 3975030897280119685785709

theorem tailTrace_7741345 : CollatzResearch.WordTrace tailWord_7741345 prefixEnd_7741345 3975030897280119685785709 := by
  unfold tailWord_7741345
  simp only [CollatzResearch.WordTrace]
  refine ⟨282350048139436656312041489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188233365426291104208027659 282350048139436656312041489)
  ·
    refine ⟨211762536104577492234031117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 282350048139436656312041489 211762536104577492234031117)
    ·
      refine ⟨79410951039216559587761669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211762536104577492234031117 79410951039216559587761669)
      ·
        refine ⟨14889553319853104922705313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79410951039216559587761669 14889553319853104922705313)
        ·
          refine ⟨11167164989889828692028985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14889553319853104922705313 11167164989889828692028985)
          ·
            refine ⟨8375373742417371519021739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11167164989889828692028985 8375373742417371519021739)
            ·
              refine ⟨12563060613626057278532609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375373742417371519021739 12563060613626057278532609)
              ·
                refine ⟨9422295460219542958899457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12563060613626057278532609 9422295460219542958899457)
                ·
                  refine ⟨7066721595164657219174593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9422295460219542958899457 7066721595164657219174593)
                  ·
                    refine ⟨5300041196373492914380945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7066721595164657219174593 5300041196373492914380945)
                    ·
                      refine ⟨3975030897280119685785709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5300041196373492914380945 3975030897280119685785709)
                      ·
                        rfl

theorem cell23_7741345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_7741345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741345 prefixEnd_7741345 := by exact prefixLift 7741345
  have htrace : WordTrace (prefixWord ++ tailWord_7741345) baseStart_7741345 baseEnd_7741345 := by
    simpa [prefixWord, tailWord_7741345, baseEnd_7741345] using wordTrace_append hprefix tailTrace_7741345
  have hstable : (prefixWord ++ tailWord_7741345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741345).length < 2 ^ (prefixWord ++ tailWord_7741345).sum := by decide
  have hdescent : baseEnd_7741345 < baseStart_7741345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741387 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3]
def baseStart_7741387 : Nat := 118140960795 + 7741387 * 2 ^ 59
def prefixEnd_7741387 : Nat := 4983230072969 + 3 ^ 40 * 7741387 * 2
def baseEnd_7741387 : Nat := 3975052463467608521460515

theorem tailTrace_7741387 : CollatzResearch.WordTrace tailWord_7741387 prefixEnd_7741387 3975052463467608521460515 := by
  unfold tailWord_7741387
  simp only [CollatzResearch.WordTrace]
  refine ⟨282351580005284497485070415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188234386670189664990046943 282351580005284497485070415)
  ·
    refine ⟨423527370007926746227605623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282351580005284497485070415 423527370007926746227605623)
    ·
      refine ⟨635291055011890119341408435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423527370007926746227605623 635291055011890119341408435)
      ·
        refine ⟨952936582517835179012112653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 635291055011890119341408435 952936582517835179012112653)
        ·
          refine ⟨357351218444188192129542245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952936582517835179012112653 357351218444188192129542245)
          ·
            refine ⟨67003353458285286024289171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 357351218444188192129542245 67003353458285286024289171)
            ·
              refine ⟨100505030187427929036433757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67003353458285286024289171 100505030187427929036433757)
              ·
                refine ⟨37689386320285473388662659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100505030187427929036433757 37689386320285473388662659)
                ·
                  refine ⟨56534079480428210082993989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37689386320285473388662659 56534079480428210082993989)
                  ·
                    refine ⟨10600139902580289390561373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56534079480428210082993989 10600139902580289390561373)
                    ·
                      refine ⟨3975052463467608521460515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10600139902580289390561373 3975052463467608521460515)
                      ·
                        rfl

theorem cell23_7741387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3].length) (baseStart_7741387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741387 prefixEnd_7741387 := by exact prefixLift 7741387
  have htrace : WordTrace (prefixWord ++ tailWord_7741387) baseStart_7741387 baseEnd_7741387 := by
    simpa [prefixWord, tailWord_7741387, baseEnd_7741387] using wordTrace_append hprefix tailTrace_7741387
  have hstable : (prefixWord ++ tailWord_7741387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741387).length < 2 ^ (prefixWord ++ tailWord_7741387).sum := by decide
  have hdescent : baseEnd_7741387 < baseStart_7741387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741407 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 8]
def baseStart_7741407 : Nat := 118140960795 + 7741407 * 2 ^ 59
def prefixEnd_7741407 : Nat := 4983230072969 + 3 ^ 40 * 7741407 * 2
def baseEnd_7741407 : Nat := 441673637008966493690047

theorem tailTrace_7741407 : CollatzResearch.WordTrace tailWord_7741407 prefixEnd_7741407 441673637008966493690047 := by
  unfold tailWord_7741407
  simp only [CollatzResearch.WordTrace]
  refine ⟨282352309465212040900798475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188234872976808027267198983 282352309465212040900798475)
  ·
    refine ⟨423528464197818061351197713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282352309465212040900798475 423528464197818061351197713)
    ·
      refine ⟨317646348148363546013398285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423528464197818061351197713 317646348148363546013398285)
      ·
        refine ⟨119117380555636329755024357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317646348148363546013398285 119117380555636329755024357)
        ·
          refine ⟨22334508854181811829067067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119117380555636329755024357 22334508854181811829067067)
          ·
            refine ⟨33501763281272717743600601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22334508854181811829067067 33501763281272717743600601)
            ·
              refine ⟨25126322460954538307700451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33501763281272717743600601 25126322460954538307700451)
              ·
                refine ⟨37689483691431807461550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25126322460954538307700451 37689483691431807461550677)
                ·
                  refine ⟨441673637008966493690047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37689483691431807461550677 441673637008966493690047)
                  ·
                    rfl

theorem cell23_7741407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 8].length) (baseStart_7741407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741407 prefixEnd_7741407 := by exact prefixLift 7741407
  have htrace : WordTrace (prefixWord ++ tailWord_7741407) baseStart_7741407 baseEnd_7741407 := by
    simpa [prefixWord, tailWord_7741407, baseEnd_7741407] using wordTrace_append hprefix tailTrace_7741407
  have hstable : (prefixWord ++ tailWord_7741407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741407).length < 2 ^ (prefixWord ++ tailWord_7741407).sum := by decide
  have hdescent : baseEnd_7741407 < baseStart_7741407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741411 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 3, 4]
def baseStart_7741411 : Nat := 118140960795 + 7741411 * 2 ^ 59
def prefixEnd_7741411 : Nat := 4983230072969 + 3 ^ 40 * 7741411 * 2
def baseEnd_7741411 : Nat := 1325021595667772142520135

theorem tailTrace_7741411 : CollatzResearch.WordTrace tailWord_7741411 prefixEnd_7741411 1325021595667772142520135 := by
  unfold tailWord_7741411
  simp only [CollatzResearch.WordTrace]
  refine ⟨282352455357197549583944087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 188234970238131699722629391 282352455357197549583944087)
  ·
    refine ⟨423528683035796324375916131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 282352455357197549583944087 423528683035796324375916131)
    ·
      refine ⟨635293024553694486563874197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 423528683035796324375916131 635293024553694486563874197)
      ·
        refine ⟨29779360525954429057681603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 635293024553694486563874197 29779360525954429057681603)
        ·
          refine ⟨44669040788931643586522405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29779360525954429057681603 44669040788931643586522405)
          ·
            refine ⟨8375445147924683172472951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44669040788931643586522405 8375445147924683172472951)
            ·
              refine ⟨12563167721887024758709427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8375445147924683172472951 12563167721887024758709427)
              ·
                refine ⟨18844751582830537138064141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12563167721887024758709427 18844751582830537138064141)
                ·
                  refine ⟨7066781843561451426774053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18844751582830537138064141 7066781843561451426774053)
                  ·
                    refine ⟨1325021595667772142520135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7066781843561451426774053 1325021595667772142520135)
                    ·
                      rfl

theorem cell23_7741411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 4].length) (baseStart_7741411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741411 prefixEnd_7741411 := by exact prefixLift 7741411
  have htrace : WordTrace (prefixWord ++ tailWord_7741411) baseStart_7741411 baseEnd_7741411 := by
    simpa [prefixWord, tailWord_7741411, baseEnd_7741411] using wordTrace_append hprefix tailTrace_7741411
  have hstable : (prefixWord ++ tailWord_7741411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741411).length < 2 ^ (prefixWord ++ tailWord_7741411).sum := by decide
  have hdescent : baseEnd_7741411 < baseStart_7741411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7741424 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 6]
def baseStart_7741424 : Nat := 118140960795 + 7741424 * 2 ^ 59
def prefixEnd_7741424 : Nat := 4983230072969 + 3 ^ 40 * 7741424 * 2
def baseEnd_7741424 : Nat := 441674606916869430744205

theorem tailTrace_7741424 : CollatzResearch.WordTrace tailWord_7741424 prefixEnd_7741424 441674606916869430744205 := by
  unfold tailWord_7741424
  simp only [CollatzResearch.WordTrace]
  refine ⟨141176464753075226402083663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 188235286337433635202778217 141176464753075226402083663)
  ·
    refine ⟨211764697129612839603125495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141176464753075226402083663 211764697129612839603125495)
    ·
      refine ⟨317647045694419259404688243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211764697129612839603125495 317647045694419259404688243)
      ·
        refine ⟨476470568541628889107032365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317647045694419259404688243 476470568541628889107032365)
        ·
          refine ⟨178676463203110833415137137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476470568541628889107032365 178676463203110833415137137)
          ·
            refine ⟨134007347402333125061352853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178676463203110833415137137 134007347402333125061352853)
            ·
              refine ⟨6281594409484365237250915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 134007347402333125061352853 6281594409484365237250915)
              ·
                refine ⟨9422391614226547855876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6281594409484365237250915 9422391614226547855876373)
                ·
                  refine ⟨441674606916869430744205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9422391614226547855876373 441674606916869430744205)
                  ·
                    rfl

theorem cell23_7741424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 6].length) (baseStart_7741424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7741424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7741424 prefixEnd_7741424 := by exact prefixLift 7741424
  have htrace : WordTrace (prefixWord ++ tailWord_7741424) baseStart_7741424 baseEnd_7741424 := by
    simpa [prefixWord, tailWord_7741424, baseEnd_7741424] using wordTrace_append hprefix tailTrace_7741424
  have hstable : (prefixWord ++ tailWord_7741424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7741424).length < 2 ^ (prefixWord ++ tailWord_7741424).sum := by decide
  have hdescent : baseEnd_7741424 < baseStart_7741424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7741424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
