import V185TrunkScan21Chunk044

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_544192 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_544192 : Nat := 118140960795 + 544192 * 2 ^ 59
def prefixEnd_544192 : Nat := 4983230072969 + 3 ^ 40 * 544192 * 2
def baseEnd_544192 : Nat := 124192028591840035554361

theorem tailTrace_544192 : CollatzResearch.WordTrace tailWord_544192 prefixEnd_544192 124192028591840035554361 := by
  unfold tailWord_544192
  simp only [CollatzResearch.WordTrace]
  refine ⟨9924156422246399719665415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13232208562995199626220553 9924156422246399719665415)
  ·
    refine ⟨14886234633369599579498123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9924156422246399719665415 14886234633369599579498123)
    ·
      refine ⟨22329351950054399369247185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14886234633369599579498123 22329351950054399369247185)
      ·
        refine ⟨16747013962540799526935389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22329351950054399369247185 16747013962540799526935389)
        ·
          refine ⟨6280130235952799822600771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16747013962540799526935389 6280130235952799822600771)
          ·
            refine ⟨9420195353929199733901157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280130235952799822600771 9420195353929199733901157)
            ·
              refine ⟨1766286628861724950106467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9420195353929199733901157 1766286628861724950106467)
              ·
                refine ⟨2649429943292587425159701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766286628861724950106467 2649429943292587425159701)
                ·
                  refine ⟨124192028591840035554361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2649429943292587425159701 124192028591840035554361)
                  ·
                    rfl

theorem cell21_544192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_544192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544192 prefixEnd_544192 := by exact prefixLift 544192
  have htrace : WordTrace (prefixWord ++ tailWord_544192) baseStart_544192 baseEnd_544192 := by
    simpa [prefixWord, tailWord_544192, baseEnd_544192] using wordTrace_append hprefix tailTrace_544192
  have hstable : (prefixWord ++ tailWord_544192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544192).length < 2 ^ (prefixWord ++ tailWord_544192).sum := by decide
  have hdescent : baseEnd_544192 < baseStart_544192 := by decide
  rcases family_descends (prefixWord ++ tailWord_544192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544257 : List Nat := [1, 2, 4, 1, 5, 1, 1, 6]
def baseStart_544257 : Nat := 118140960795 + 544257 * 2 ^ 59
def prefixEnd_544257 : Nat := 4983230072969 + 3 ^ 40 * 544257 * 2
def baseEnd_544257 : Nat := 41402287492471455656965

theorem tailTrace_544257 : CollatzResearch.WordTrace tailWord_544257 prefixEnd_544257 41402287492471455656965 := by
  unfold tailWord_544257
  simp only [CollatzResearch.WordTrace]
  refine ⟨19850683589257315540447025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13233789059504877026964683 19850683589257315540447025)
  ·
    refine ⟨14888012691942986655335269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19850683589257315540447025 14888012691942986655335269)
    ·
      refine ⟨2791502379739309997875363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14888012691942986655335269 2791502379739309997875363)
      ·
        refine ⟨4187253569608964996813045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2791502379739309997875363 4187253569608964996813045)
        ·
          refine ⟨392555022150840468451223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4187253569608964996813045 392555022150840468451223)
          ·
            refine ⟨588832533226260702676835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392555022150840468451223 588832533226260702676835)
            ·
              refine ⟨883248799839391054015253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588832533226260702676835 883248799839391054015253)
              ·
                refine ⟨41402287492471455656965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 883248799839391054015253 41402287492471455656965)
                ·
                  rfl

theorem cell21_544257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 6].length) (baseStart_544257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544257 prefixEnd_544257 := by exact prefixLift 544257
  have htrace : WordTrace (prefixWord ++ tailWord_544257) baseStart_544257 baseEnd_544257 := by
    simpa [prefixWord, tailWord_544257, baseEnd_544257] using wordTrace_append hprefix tailTrace_544257
  have hstable : (prefixWord ++ tailWord_544257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544257).length < 2 ^ (prefixWord ++ tailWord_544257).sum := by decide
  have hdescent : baseEnd_544257 < baseStart_544257 := by decide
  rcases family_descends (prefixWord ++ tailWord_544257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544288 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 3]
def baseStart_544288 : Nat := 118140960795 + 544288 * 2 ^ 59
def prefixEnd_544288 : Nat := 4983230072969 + 3 ^ 40 * 544288 * 2
def baseEnd_544288 : Nat := 124213937099765201954165

theorem tailTrace_544288 : CollatzResearch.WordTrace tailWord_544288 prefixEnd_544288 124213937099765201954165 := by
  unfold tailWord_544288
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925907126072503917412759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13234542834763338556550345 9925907126072503917412759)
  ·
    refine ⟨14888860689108755876119139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9925907126072503917412759 14888860689108755876119139)
    ·
      refine ⟨22333291033663133814178709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14888860689108755876119139 22333291033663133814178709)
      ·
        refine ⟨1046873017202959397539627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22333291033663133814178709 1046873017202959397539627)
        ·
          refine ⟨1570309525804439096309441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046873017202959397539627 1570309525804439096309441)
          ·
            refine ⟨1177732144353329322232081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1570309525804439096309441 1177732144353329322232081)
            ·
              refine ⟨883299108264996991674061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1177732144353329322232081 883299108264996991674061)
              ·
                refine ⟨331237165599373871877773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883299108264996991674061 331237165599373871877773)
                ·
                  refine ⟨124213937099765201954165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331237165599373871877773 124213937099765201954165)
                  ·
                    rfl

theorem cell21_544288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 3].length) (baseStart_544288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544288 prefixEnd_544288 := by exact prefixLift 544288
  have htrace : WordTrace (prefixWord ++ tailWord_544288) baseStart_544288 baseEnd_544288 := by
    simpa [prefixWord, tailWord_544288, baseEnd_544288] using wordTrace_append hprefix tailTrace_544288
  have hstable : (prefixWord ++ tailWord_544288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544288).length < 2 ^ (prefixWord ++ tailWord_544288).sum := by decide
  have hdescent : baseEnd_544288 < baseStart_544288 := by decide
  rcases family_descends (prefixWord ++ tailWord_544288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544302 : List Nat := [4, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_544302 : Nat := 118140960795 + 544302 * 2 ^ 59
def prefixEnd_544302 : Nat := 4983230072969 + 3 ^ 40 * 544302 * 2
def baseEnd_544302 : Nat := 124217132090504288720803

theorem tailTrace_544302 : CollatzResearch.WordTrace tailWord_544302 prefixEnd_544302 124217132090504288720803 := by
  unfold tailWord_544302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2481540609261786028229395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13234883249396192150556773 2481540609261786028229395)
  ·
    refine ⟨3722310913892679042344093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2481540609261786028229395 3722310913892679042344093)
    ·
      refine ⟨1395866592709754640879035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3722310913892679042344093 1395866592709754640879035)
      ·
        refine ⟨2093799889064631961318553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395866592709754640879035 2093799889064631961318553)
        ·
          refine ⟨1570349916798473970988915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2093799889064631961318553 1570349916798473970988915)
          ·
            refine ⟨2355524875197710956483373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1570349916798473970988915 2355524875197710956483373)
            ·
              refine ⟨883321828199141608681265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355524875197710956483373 883321828199141608681265)
              ·
                refine ⟨662491371149356206510949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883321828199141608681265 662491371149356206510949)
                ·
                  refine ⟨124217132090504288720803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 662491371149356206510949 124217132090504288720803)
                  ·
                    rfl

theorem cell21_544302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_544302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544302 prefixEnd_544302 := by exact prefixLift 544302
  have htrace : WordTrace (prefixWord ++ tailWord_544302) baseStart_544302 baseEnd_544302 := by
    simpa [prefixWord, tailWord_544302, baseEnd_544302] using wordTrace_append hprefix tailTrace_544302
  have hstable : (prefixWord ++ tailWord_544302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544302).length < 2 ^ (prefixWord ++ tailWord_544302).sum := by decide
  have hdescent : baseEnd_544302 < baseStart_544302 := by decide
  rcases family_descends (prefixWord ++ tailWord_544302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544389 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 7]
def baseStart_544389 : Nat := 118140960795 + 544389 * 2 ^ 59
def prefixEnd_544389 : Nat := 4983230072969 + 3 ^ 40 * 544389 * 2
def baseEnd_544389 : Nat := 124236986675811470770625

theorem tailTrace_544389 : CollatzResearch.WordTrace tailWord_544389 prefixEnd_544389 124236986675811470770625 := by
  unfold tailWord_544389
  simp only [CollatzResearch.WordTrace]
  refine ⟨19855498024779102084252221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13236998683186068056168147 19855498024779102084252221)
  ·
    refine ⟨7445811759292163281594583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19855498024779102084252221 7445811759292163281594583)
    ·
      refine ⟨11168717638938244922391875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7445811759292163281594583 11168717638938244922391875)
      ·
        refine ⟨16753076458407367383587813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11168717638938244922391875 16753076458407367383587813)
        ·
          refine ⟨3141201835951381384422715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16753076458407367383587813 3141201835951381384422715)
          ·
            refine ⟨4711802753927072076634073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141201835951381384422715 4711802753927072076634073)
            ·
              refine ⟨3533852065445304057475555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4711802753927072076634073 3533852065445304057475555)
              ·
                refine ⟨5300778098167956086213333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3533852065445304057475555 5300778098167956086213333)
                ·
                  refine ⟨124236986675811470770625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5300778098167956086213333 124236986675811470770625)
                  ·
                    rfl

theorem cell21_544389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_544389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544389 prefixEnd_544389 := by exact prefixLift 544389
  have htrace : WordTrace (prefixWord ++ tailWord_544389) baseStart_544389 baseEnd_544389 := by
    simpa [prefixWord, tailWord_544389, baseEnd_544389] using wordTrace_append hprefix tailTrace_544389
  have hstable : (prefixWord ++ tailWord_544389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544389).length < 2 ^ (prefixWord ++ tailWord_544389).sum := by decide
  have hdescent : baseEnd_544389 < baseStart_544389 := by decide
  rcases family_descends (prefixWord ++ tailWord_544389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544516 : List Nat := [2, 3, 2, 2, 1, 4, 1, 3, 3]
def baseStart_544516 : Nat := 118140960795 + 544516 * 2 ^ 59
def prefixEnd_544516 : Nat := 4983230072969 + 3 ^ 40 * 544516 * 2
def baseEnd_544516 : Nat := 124265969806087472153699

theorem tailTrace_544516 : CollatzResearch.WordTrace tailWord_544516 prefixEnd_544516 124265969806087472153699 := by
  unfold tailWord_544516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930065047659501387062701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13240086730212668516083601 9930065047659501387062701)
  ·
    refine ⟨3723774392872313020148513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9930065047659501387062701 3723774392872313020148513)
    ·
      refine ⟨2792830794654234765111385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3723774392872313020148513 2792830794654234765111385)
      ·
        refine ⟨2094623095990676073833539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2792830794654234765111385 2094623095990676073833539)
        ·
          refine ⟨3141934643986014110750309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094623095990676073833539 3141934643986014110750309)
          ·
            refine ⟨589112745747377645765683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3141934643986014110750309 589112745747377645765683)
            ·
              refine ⟨883669118621066468648525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589112745747377645765683 883669118621066468648525)
              ·
                refine ⟨331375919482899925743197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 883669118621066468648525 331375919482899925743197)
                ·
                  refine ⟨124265969806087472153699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331375919482899925743197 124265969806087472153699)
                  ·
                    rfl

theorem cell21_544516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_544516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544516 prefixEnd_544516 := by exact prefixLift 544516
  have htrace : WordTrace (prefixWord ++ tailWord_544516) baseStart_544516 baseEnd_544516 := by
    simpa [prefixWord, tailWord_544516, baseEnd_544516] using wordTrace_append hprefix tailTrace_544516
  have hstable : (prefixWord ++ tailWord_544516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544516).length < 2 ^ (prefixWord ++ tailWord_544516).sum := by decide
  have hdescent : baseEnd_544516 < baseStart_544516 := by decide
  rcases family_descends (prefixWord ++ tailWord_544516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544634 : List Nat := [3, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_544634 : Nat := 118140960795 + 544634 * 2 ^ 59
def prefixEnd_544634 : Nat := 4983230072969 + 3 ^ 40 * 544634 * 2
def baseEnd_544634 : Nat := 124292899013745489186791

theorem tailTrace_544634 : CollatzResearch.WordTrace tailWord_544634 prefixEnd_544634 124292899013745489186791 := by
  unfold tailWord_544634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966108477222877231730239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13242955939261005951280637 4966108477222877231730239)
  ·
    refine ⟨7449162715834315847595359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4966108477222877231730239 7449162715834315847595359)
    ·
      refine ⟨11173744073751473771393039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7449162715834315847595359 11173744073751473771393039)
      ·
        refine ⟨16760616110627210657089559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173744073751473771393039 16760616110627210657089559)
        ·
          refine ⟨25140924165940815985634339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16760616110627210657089559 25140924165940815985634339)
          ·
            refine ⟨37711386248911223978451509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25140924165940815985634339 37711386248911223978451509)
            ·
              refine ⟨3535442460835427247979829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37711386248911223978451509 3535442460835427247979829)
              ·
                refine ⟨331447730703321304498109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3535442460835427247979829 331447730703321304498109)
                ·
                  refine ⟨124292899013745489186791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331447730703321304498109 124292899013745489186791)
                  ·
                    rfl

theorem cell21_544634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_544634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544634 prefixEnd_544634 := by exact prefixLift 544634
  have htrace : WordTrace (prefixWord ++ tailWord_544634) baseStart_544634 baseEnd_544634 := by
    simpa [prefixWord, tailWord_544634, baseEnd_544634] using wordTrace_append hprefix tailTrace_544634
  have hstable : (prefixWord ++ tailWord_544634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544634).length < 2 ^ (prefixWord ++ tailWord_544634).sum := by decide
  have hdescent : baseEnd_544634 < baseStart_544634 := by decide
  rcases family_descends (prefixWord ++ tailWord_544634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544679 : List Nat := [1, 1, 6, 1, 2, 2, 1, 7]
def baseStart_544679 : Nat := 118140960795 + 544679 * 2 ^ 59
def prefixEnd_544679 : Nat := 4983230072969 + 3 ^ 40 * 544679 * 2
def baseEnd_544679 : Nat := 41434389542278470312233

theorem tailTrace_544679 : CollatzResearch.WordTrace tailWord_544679 prefixEnd_544679 41434389542278470312233 := by
  unfold tailWord_544679
  simp only [CollatzResearch.WordTrace]
  refine ⟨19866075193728481612309091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13244050129152321074872727 19866075193728481612309091)
  ·
    refine ⟨29799112790592722418463637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19866075193728481612309091 29799112790592722418463637)
    ·
      refine ⟨1396833412059033863365483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29799112790592722418463637 1396833412059033863365483)
      ·
        refine ⟨2095250118088550795048225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396833412059033863365483 2095250118088550795048225)
        ·
          refine ⟨1571437588566413096286169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2095250118088550795048225 1571437588566413096286169)
          ·
            refine ⟨1178578191424809822214627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1571437588566413096286169 1178578191424809822214627)
            ·
              refine ⟨1767867287137214733321941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178578191424809822214627 1767867287137214733321941)
              ·
                refine ⟨41434389542278470312233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1767867287137214733321941 41434389542278470312233)
                ·
                  rfl

theorem cell21_544679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 7].length) (baseStart_544679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544679 prefixEnd_544679 := by exact prefixLift 544679
  have htrace : WordTrace (prefixWord ++ tailWord_544679) baseStart_544679 baseEnd_544679 := by
    simpa [prefixWord, tailWord_544679, baseEnd_544679] using wordTrace_append hprefix tailTrace_544679
  have hstable : (prefixWord ++ tailWord_544679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544679).length < 2 ^ (prefixWord ++ tailWord_544679).sum := by decide
  have hdescent : baseEnd_544679 < baseStart_544679 := by decide
  rcases family_descends (prefixWord ++ tailWord_544679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544758 : List Nat := [5, 1, 1, 1, 4, 1, 2, 2, 4]
def baseStart_544758 : Nat := 118140960795 + 544758 * 2 ^ 59
def prefixEnd_544758 : Nat := 4983230072969 + 3 ^ 40 * 544758 * 2
def baseEnd_544758 : Nat := 124321197503148829119871

theorem tailTrace_544758 : CollatzResearch.WordTrace tailWord_544758 prefixEnd_544758 124321197503148829119871 := by
  unfold tailWord_544758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241809785027642381527183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13245971040294852069623285 1241809785027642381527183)
  ·
    refine ⟨1862714677541463572290775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241809785027642381527183 1862714677541463572290775)
    ·
      refine ⟨2794072016312195358436163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862714677541463572290775 2794072016312195358436163)
      ·
        refine ⟨4191108024468293037654245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794072016312195358436163 4191108024468293037654245)
        ·
          refine ⟨785832754587804944560171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4191108024468293037654245 785832754587804944560171)
          ·
            refine ⟨1178749131881707416840257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785832754587804944560171 1178749131881707416840257)
            ·
              refine ⟨884061848911280562630193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1178749131881707416840257 884061848911280562630193)
              ·
                refine ⟨663046386683460421972645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884061848911280562630193 663046386683460421972645)
                ·
                  refine ⟨124321197503148829119871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663046386683460421972645 124321197503148829119871)
                  ·
                    rfl

theorem cell21_544758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_544758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544758 prefixEnd_544758 := by exact prefixLift 544758
  have htrace : WordTrace (prefixWord ++ tailWord_544758) baseStart_544758 baseEnd_544758 := by
    simpa [prefixWord, tailWord_544758, baseEnd_544758] using wordTrace_append hprefix tailTrace_544758
  have hstable : (prefixWord ++ tailWord_544758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544758).length < 2 ^ (prefixWord ++ tailWord_544758).sum := by decide
  have hdescent : baseEnd_544758 < baseStart_544758 := by decide
  rcases family_descends (prefixWord ++ tailWord_544758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544769 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 5]
def baseStart_544769 : Nat := 118140960795 + 544769 * 2 ^ 59
def prefixEnd_544769 : Nat := 4983230072969 + 3 ^ 40 * 544769 * 2
def baseEnd_544769 : Nat := 124323707853015254436515

theorem tailTrace_544769 : CollatzResearch.WordTrace tailWord_544769 prefixEnd_544769 124323707853015254436515 := by
  unfold tailWord_544769
  simp only [CollatzResearch.WordTrace]
  refine ⟨19869357763402426983085361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13246238508934951322056907 19869357763402426983085361)
  ·
    refine ⟨14902018322551820237314021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19869357763402426983085361 14902018322551820237314021)
    ·
      refine ⟨2794128435478466294496379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14902018322551820237314021 2794128435478466294496379)
      ·
        refine ⟨4191192653217699441744569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2794128435478466294496379 4191192653217699441744569)
        ·
          refine ⟨3143394489913274581308427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4191192653217699441744569 3143394489913274581308427)
          ·
            refine ⟨4715091734869911871962641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143394489913274581308427 4715091734869911871962641)
            ·
              refine ⟨3536318801152433903971981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4715091734869911871962641 3536318801152433903971981)
              ·
                refine ⟨1326119550432162713989493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3536318801152433903971981 1326119550432162713989493)
                ·
                  refine ⟨124323707853015254436515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1326119550432162713989493 124323707853015254436515)
                  ·
                    rfl

theorem cell21_544769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_544769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544769 prefixEnd_544769 := by exact prefixLift 544769
  have htrace : WordTrace (prefixWord ++ tailWord_544769) baseStart_544769 baseEnd_544769 := by
    simpa [prefixWord, tailWord_544769, baseEnd_544769] using wordTrace_append hprefix tailTrace_544769
  have hstable : (prefixWord ++ tailWord_544769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544769).length < 2 ^ (prefixWord ++ tailWord_544769).sum := by decide
  have hdescent : baseEnd_544769 < baseStart_544769 := by decide
  rcases family_descends (prefixWord ++ tailWord_544769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544817 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 4]
def baseStart_544817 : Nat := 118140960795 + 544817 * 2 ^ 59
def prefixEnd_544817 : Nat := 4983230072969 + 3 ^ 40 * 544817 * 2
def baseEnd_544817 : Nat := 124334662106977837636417

theorem tailTrace_544817 : CollatzResearch.WordTrace tailWord_544817 prefixEnd_544817 124334662106977837636417 := by
  unfold tailWord_544817
  simp only [CollatzResearch.WordTrace]
  refine ⟨19871108467228531180832705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13247405644819020787221803 19871108467228531180832705)
  ·
    refine ⟨14903331350421398385624529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19871108467228531180832705 14903331350421398385624529)
    ·
      refine ⟨11177498512816048789218397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14903331350421398385624529 11177498512816048789218397)
      ·
        refine ⟨4191561942306018295956899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11177498512816048789218397 4191561942306018295956899)
        ·
          refine ⟨6287342913459027443935349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191561942306018295956899 6287342913459027443935349)
          ·
            refine ⟨589438398136783822868939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6287342913459027443935349 589438398136783822868939)
            ·
              refine ⟨884157597205175734303409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589438398136783822868939 884157597205175734303409)
              ·
                refine ⟨663118197903881800727557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884157597205175734303409 663118197903881800727557)
                ·
                  refine ⟨124334662106977837636417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663118197903881800727557 124334662106977837636417)
                  ·
                    rfl

theorem cell21_544817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_544817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544817 prefixEnd_544817 := by exact prefixLift 544817
  have htrace : WordTrace (prefixWord ++ tailWord_544817) baseStart_544817 baseEnd_544817 := by
    simpa [prefixWord, tailWord_544817, baseEnd_544817] using wordTrace_append hprefix tailTrace_544817
  have hstable : (prefixWord ++ tailWord_544817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544817).length < 2 ^ (prefixWord ++ tailWord_544817).sum := by decide
  have hdescent : baseEnd_544817 < baseStart_544817 := by decide
  rcases family_descends (prefixWord ++ tailWord_544817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544879 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 3]
def baseStart_544879 : Nat := 118140960795 + 544879 * 2 ^ 59
def prefixEnd_544879 : Nat := 4983230072969 + 3 ^ 40 * 544879 * 2
def baseEnd_544879 : Nat := 124348811351679507602957

theorem tailTrace_544879 : CollatzResearch.WordTrace tailWord_544879 prefixEnd_544879 124348811351679507602957 := by
  unfold tailWord_544879
  simp only [CollatzResearch.WordTrace]
  refine ⟨19873369793003915769589691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13248913195335943846393127 19873369793003915769589691)
  ·
    refine ⟨29810054689505873654384537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19873369793003915769589691 29810054689505873654384537)
    ·
      refine ⟨22357541017129405240788403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29810054689505873654384537 22357541017129405240788403)
      ·
        refine ⟨33536311525694107861182605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22357541017129405240788403 33536311525694107861182605)
        ·
          refine ⟨12576116822135290447943477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33536311525694107861182605 12576116822135290447943477)
          ·
            refine ⟨1179010952075183479494701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12576116822135290447943477 1179010952075183479494701)
            ·
              refine ⟨442129107028193804810513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179010952075183479494701 442129107028193804810513)
              ·
                refine ⟨331596830271145353607885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442129107028193804810513 331596830271145353607885)
                ·
                  refine ⟨124348811351679507602957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331596830271145353607885 124348811351679507602957)
                  ·
                    rfl

theorem cell21_544879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 3].length) (baseStart_544879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544879 prefixEnd_544879 := by exact prefixLift 544879
  have htrace : WordTrace (prefixWord ++ tailWord_544879) baseStart_544879 baseEnd_544879 := by
    simpa [prefixWord, tailWord_544879, baseEnd_544879] using wordTrace_append hprefix tailTrace_544879
  have hstable : (prefixWord ++ tailWord_544879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544879).length < 2 ^ (prefixWord ++ tailWord_544879).sum := by decide
  have hdescent : baseEnd_544879 < baseStart_544879 := by decide
  rcases family_descends (prefixWord ++ tailWord_544879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544893 : List Nat := [1, 4, 1, 1, 3, 2, 4, 1, 4]
def baseStart_544893 : Nat := 118140960795 + 544893 * 2 ^ 59
def prefixEnd_544893 : Nat := 4983230072969 + 3 ^ 40 * 544893 * 2
def baseEnd_544893 : Nat := 124352006342418594369595

theorem tailTrace_544893 : CollatzResearch.WordTrace tailWord_544893 prefixEnd_544893 124352006342418594369595 := by
  unfold tailWord_544893
  simp only [CollatzResearch.WordTrace]
  refine ⟨19873880414953196160599333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13249253609968797440399555 19873880414953196160599333)
  ·
    refine ⟨3726352577803724280112375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19873880414953196160599333 3726352577803724280112375)
    ·
      refine ⟨5589528866705586420168563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3726352577803724280112375 5589528866705586420168563)
      ·
        refine ⟨8384293300058379630252845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5589528866705586420168563 8384293300058379630252845)
        ·
          refine ⟨3144109987521892361344817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8384293300058379630252845 3144109987521892361344817)
          ·
            refine ⟨2358082490641419271008613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3144109987521892361344817 2358082490641419271008613)
            ·
              refine ⟨442140466995266113314115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2358082490641419271008613 442140466995266113314115)
              ·
                refine ⟨663210700492899169971173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442140466995266113314115 663210700492899169971173)
                ·
                  refine ⟨124352006342418594369595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663210700492899169971173 124352006342418594369595)
                  ·
                    rfl

theorem cell21_544893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_544893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544893 prefixEnd_544893 := by exact prefixLift 544893
  have htrace : WordTrace (prefixWord ++ tailWord_544893) baseStart_544893 baseEnd_544893 := by
    simpa [prefixWord, tailWord_544893, baseEnd_544893] using wordTrace_append hprefix tailTrace_544893
  have hstable : (prefixWord ++ tailWord_544893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544893).length < 2 ^ (prefixWord ++ tailWord_544893).sum := by decide
  have hdescent : baseEnd_544893 < baseStart_544893 := by decide
  rcases family_descends (prefixWord ++ tailWord_544893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544972 : List Nat := [2, 2, 1, 6, 1, 1, 2, 3, 3]
def baseStart_544972 : Nat := 118140960795 + 544972 * 2 ^ 59
def prefixEnd_544972 : Nat := 4983230072969 + 3 ^ 40 * 544972 * 2
def baseEnd_544972 : Nat := 124370035218732012552767

theorem tailTrace_544972 : CollatzResearch.WordTrace tailWord_544972 prefixEnd_544972 124370035218732012552767 := by
  unfold tailWord_544972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9938380890833496326362585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13251174521111328435150113 9938380890833496326362585)
  ·
    refine ⟨7453785668125122244771939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9938380890833496326362585 7453785668125122244771939)
    ·
      refine ⟨11180678502187683367157909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7453785668125122244771939 11180678502187683367157909)
      ·
        refine ⟨524094304790047657835527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11180678502187683367157909 524094304790047657835527)
        ·
          refine ⟨786141457185071486753291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524094304790047657835527 786141457185071486753291)
          ·
            refine ⟨1179212185777607230129937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786141457185071486753291 1179212185777607230129937)
            ·
              refine ⟨884409139333205422597453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179212185777607230129937 884409139333205422597453)
              ·
                refine ⟨331653427249952033474045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 884409139333205422597453 331653427249952033474045)
                ·
                  refine ⟨124370035218732012552767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331653427249952033474045 124370035218732012552767)
                  ·
                    rfl

theorem cell21_544972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3, 3].length) (baseStart_544972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544972 prefixEnd_544972 := by exact prefixLift 544972
  have htrace : WordTrace (prefixWord ++ tailWord_544972) baseStart_544972 baseEnd_544972 := by
    simpa [prefixWord, tailWord_544972, baseEnd_544972] using wordTrace_append hprefix tailTrace_544972
  have hstable : (prefixWord ++ tailWord_544972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544972).length < 2 ^ (prefixWord ++ tailWord_544972).sum := by decide
  have hdescent : baseEnd_544972 < baseStart_544972 := by decide
  rcases family_descends (prefixWord ++ tailWord_544972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_544997 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 5]
def baseStart_544997 : Nat := 118140960795 + 544997 * 2 ^ 59
def prefixEnd_544997 : Nat := 4983230072969 + 3 ^ 40 * 544997 * 2
def baseEnd_544997 : Nat := 124375740559337524636049

theorem tailTrace_544997 : CollatzResearch.WordTrace tailWord_544997 prefixEnd_544997 124375740559337524636049 := by
  unfold tailWord_544997
  simp only [CollatzResearch.WordTrace]
  refine ⟨19877673606576421922385245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13251782404384281281590163 19877673606576421922385245)
  ·
    refine ⟨7454127602466158220894467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19877673606576421922385245 7454127602466158220894467)
    ·
      refine ⟨11181191403699237331341701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7454127602466158220894467 11181191403699237331341701)
      ·
        refine ⟨2096473388193606999626569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11181191403699237331341701 2096473388193606999626569)
        ·
          refine ⟨1572355041145205249719927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2096473388193606999626569 1572355041145205249719927)
          ·
            refine ⟨2358532561717807874579891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1572355041145205249719927 2358532561717807874579891)
            ·
              refine ⟨3537798842576711811869837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2358532561717807874579891 3537798842576711811869837)
              ·
                refine ⟨1326674565966266929451189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3537798842576711811869837 1326674565966266929451189)
                ·
                  refine ⟨124375740559337524636049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1326674565966266929451189 124375740559337524636049)
                  ·
                    rfl

theorem cell21_544997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_544997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_544997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_544997 prefixEnd_544997 := by exact prefixLift 544997
  have htrace : WordTrace (prefixWord ++ tailWord_544997) baseStart_544997 baseEnd_544997 := by
    simpa [prefixWord, tailWord_544997, baseEnd_544997] using wordTrace_append hprefix tailTrace_544997
  have hstable : (prefixWord ++ tailWord_544997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_544997).length < 2 ^ (prefixWord ++ tailWord_544997).sum := by decide
  have hdescent : baseEnd_544997 < baseStart_544997 := by decide
  rcases family_descends (prefixWord ++ tailWord_544997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545104 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_545104 : Nat := 118140960795 + 545104 * 2 ^ 59
def prefixEnd_545104 : Nat := 4983230072969 + 3 ^ 40 * 545104 * 2
def baseEnd_545104 : Nat := 124400159417129116352497

theorem tailTrace_545104 : CollatzResearch.WordTrace tailWord_545104 prefixEnd_545104 124400159417129116352497 := by
  unfold tailWord_545104
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940788108594389598265183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13254384144792519464353577 9940788108594389598265183)
  ·
    refine ⟨14911182162891584397397775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9940788108594389598265183 14911182162891584397397775)
    ·
      refine ⟨22366773244337376596096663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14911182162891584397397775 22366773244337376596096663)
      ·
        refine ⟨33550159866506064894144995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22366773244337376596096663 33550159866506064894144995)
        ·
          refine ⟨50325239799759097341217493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33550159866506064894144995 50325239799759097341217493)
          ·
            refine ⟨1179497807806853843934785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50325239799759097341217493 1179497807806853843934785)
            ·
              refine ⟨884623355855140382951089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179497807806853843934785 884623355855140382951089)
              ·
                refine ⟨663467516891355287213317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884623355855140382951089 663467516891355287213317)
                ·
                  refine ⟨124400159417129116352497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663467516891355287213317 124400159417129116352497)
                  ·
                    rfl

theorem cell21_545104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_545104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545104 prefixEnd_545104 := by exact prefixLift 545104
  have htrace : WordTrace (prefixWord ++ tailWord_545104) baseStart_545104 baseEnd_545104 := by
    simpa [prefixWord, tailWord_545104, baseEnd_545104] using wordTrace_append hprefix tailTrace_545104
  have hstable : (prefixWord ++ tailWord_545104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545104).length < 2 ^ (prefixWord ++ tailWord_545104).sum := by decide
  have hdescent : baseEnd_545104 < baseStart_545104 := by decide
  rcases family_descends (prefixWord ++ tailWord_545104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545163 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 6]
def baseStart_545163 : Nat := 118140960795 + 545163 * 2 ^ 59
def prefixEnd_545163 : Nat := 4983230072969 + 3 ^ 40 * 545163 * 2
def baseEnd_545163 : Nat := 124413624020958124869043

theorem tailTrace_545163 : CollatzResearch.WordTrace tailWord_545163 prefixEnd_545163 124413624020958124869043 := by
  unfold tailWord_545163
  simp only [CollatzResearch.WordTrace]
  refine ⟨19883728123975032272928143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13255818749316688181952095 19883728123975032272928143)
  ·
    refine ⟨29825592185962548409392215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19883728123975032272928143 29825592185962548409392215)
    ·
      refine ⟨44738388278943822614088323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29825592185962548409392215 44738388278943822614088323)
      ·
        refine ⟨67107582418415733921132485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44738388278943822614088323 67107582418415733921132485)
        ·
          refine ⟨12582671703452950110212341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67107582418415733921132485 12582671703452950110212341)
          ·
            refine ⟨1179625472198714072832407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12582671703452950110212341 1179625472198714072832407)
            ·
              refine ⟨1769438208298071109248611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179625472198714072832407 1769438208298071109248611)
              ·
                refine ⟨2654157312447106663872917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1769438208298071109248611 2654157312447106663872917)
                ·
                  refine ⟨124413624020958124869043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2654157312447106663872917 124413624020958124869043)
                  ·
                    rfl

theorem cell21_545163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_545163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545163 prefixEnd_545163 := by exact prefixLift 545163
  have htrace : WordTrace (prefixWord ++ tailWord_545163) baseStart_545163 baseEnd_545163 := by
    simpa [prefixWord, tailWord_545163, baseEnd_545163] using wordTrace_append hprefix tailTrace_545163
  have hstable : (prefixWord ++ tailWord_545163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545163).length < 2 ^ (prefixWord ++ tailWord_545163).sum := by decide
  have hdescent : baseEnd_545163 < baseStart_545163 := by decide
  rcases family_descends (prefixWord ++ tailWord_545163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545166 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_545166 : Nat := 118140960795 + 545166 * 2 ^ 59
def prefixEnd_545166 : Nat := 4983230072969 + 3 ^ 40 * 545166 * 2
def baseEnd_545166 : Nat := 124414308661830786319037

theorem tailTrace_545166 : CollatzResearch.WordTrace tailWord_545166 prefixEnd_545166 124414308661830786319037 := by
  unfold tailWord_545166
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485479692870520473160919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13255891695309442523524901 2485479692870520473160919)
  ·
    refine ⟨3728219539305780709741379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485479692870520473160919 3728219539305780709741379)
    ·
      refine ⟨5592329308958671064612069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728219539305780709741379 5592329308958671064612069)
      ·
        refine ⟨1048561745429750824614763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5592329308958671064612069 1048561745429750824614763)
        ·
          refine ⟨1572842618144626236922145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048561745429750824614763 1572842618144626236922145)
          ·
            refine ⟨1179631963608469677691609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572842618144626236922145 1179631963608469677691609)
            ·
              refine ⟨884723972706352258268707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179631963608469677691609 884723972706352258268707)
              ·
                refine ⟨1327085959059528387403061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884723972706352258268707 1327085959059528387403061)
                ·
                  refine ⟨124414308661830786319037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1327085959059528387403061 124414308661830786319037)
                  ·
                    rfl

theorem cell21_545166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_545166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545166 prefixEnd_545166 := by exact prefixLift 545166
  have htrace : WordTrace (prefixWord ++ tailWord_545166) baseStart_545166 baseEnd_545166 := by
    simpa [prefixWord, tailWord_545166, baseEnd_545166] using wordTrace_append hprefix tailTrace_545166
  have hstable : (prefixWord ++ tailWord_545166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545166).length < 2 ^ (prefixWord ++ tailWord_545166).sum := by decide
  have hdescent : baseEnd_545166 < baseStart_545166 := by decide
  rcases family_descends (prefixWord ++ tailWord_545166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545177 : List Nat := [1, 2, 1, 2, 1, 4, 2, 8]
def baseStart_545177 : Nat := 118140960795 + 545177 * 2 ^ 59
def prefixEnd_545177 : Nat := 4983230072969 + 3 ^ 40 * 545177 * 2
def baseEnd_545177 : Nat := 41472273003899070545227

theorem tailTrace_545177 : CollatzResearch.WordTrace tailWord_545177 prefixEnd_545177 41472273003899070545227 := by
  unfold tailWord_545177
  simp only [CollatzResearch.WordTrace]
  refine ⟨19884238745924312663937785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13256159163949541775958523 19884238745924312663937785)
  ·
    refine ⟨14913179059443234497953339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19884238745924312663937785 14913179059443234497953339)
    ·
      refine ⟨22369768589164851746930009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14913179059443234497953339 22369768589164851746930009)
      ·
        refine ⟨16777326441873638810197507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22369768589164851746930009 16777326441873638810197507)
        ·
          refine ⟨25165989662810458215296261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16777326441873638810197507 25165989662810458215296261)
          ·
            refine ⟨4718623061776960915368049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25165989662810458215296261 4718623061776960915368049)
            ·
              refine ⟨3538967296332720686526037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4718623061776960915368049 3538967296332720686526037)
              ·
                refine ⟨41472273003899070545227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3538967296332720686526037 41472273003899070545227)
                ·
                  rfl

theorem cell21_545177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 8].length) (baseStart_545177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545177 prefixEnd_545177 := by exact prefixLift 545177
  have htrace : WordTrace (prefixWord ++ tailWord_545177) baseStart_545177 baseEnd_545177 := by
    simpa [prefixWord, tailWord_545177, baseEnd_545177] using wordTrace_append hprefix tailTrace_545177
  have hstable : (prefixWord ++ tailWord_545177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545177).length < 2 ^ (prefixWord ++ tailWord_545177).sum := by decide
  have hdescent : baseEnd_545177 < baseStart_545177 := by decide
  rcases family_descends (prefixWord ++ tailWord_545177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545217 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 5]
def baseStart_545217 : Nat := 118140960795 + 545217 * 2 ^ 59
def prefixEnd_545217 : Nat := 4983230072969 + 3 ^ 40 * 545217 * 2
def baseEnd_545217 : Nat := 124425947556666030968933

theorem tailTrace_545217 : CollatzResearch.WordTrace tailWord_545217 prefixEnd_545217 124425947556666030968933 := by
  unfold tailWord_545217
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885697665779399495393905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13257131777186266330262603 19885697665779399495393905)
  ·
    refine ⟨14914273249334549621545429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19885697665779399495393905 14914273249334549621545429)
    ·
      refine ⟨349553279281278506754971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14914273249334549621545429 349553279281278506754971)
      ·
        refine ⟨524329918921917760132457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349553279281278506754971 524329918921917760132457)
        ·
          refine ⟨393247439191438320099343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 524329918921917760132457 393247439191438320099343)
          ·
            refine ⟨589871158787157480149015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393247439191438320099343 589871158787157480149015)
            ·
              refine ⟨884806738180736220223523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589871158787157480149015 884806738180736220223523)
              ·
                refine ⟨1327210107271104330335285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884806738180736220223523 1327210107271104330335285)
                ·
                  refine ⟨124425947556666030968933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1327210107271104330335285 124425947556666030968933)
                  ·
                    rfl

theorem cell21_545217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 5].length) (baseStart_545217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545217 prefixEnd_545217 := by exact prefixLift 545217
  have htrace : WordTrace (prefixWord ++ tailWord_545217) baseStart_545217 baseEnd_545217 := by
    simpa [prefixWord, tailWord_545217, baseEnd_545217] using wordTrace_append hprefix tailTrace_545217
  have hstable : (prefixWord ++ tailWord_545217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545217).length < 2 ^ (prefixWord ++ tailWord_545217).sum := by decide
  have hdescent : baseEnd_545217 < baseStart_545217 := by decide
  rcases family_descends (prefixWord ++ tailWord_545217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545225 : List Nat := [1, 2, 1, 1, 2, 1, 4, 6, 3]
def baseStart_545225 : Nat := 118140960795 + 545225 * 2 ^ 59
def prefixEnd_545225 : Nat := 4983230072969 + 3 ^ 40 * 545225 * 2
def baseEnd_545225 : Nat := 124427773265659794835583

theorem tailTrace_545225 : CollatzResearch.WordTrace tailWord_545225 prefixEnd_545225 124427773265659794835583 := by
  unfold tailWord_545225
  simp only [CollatzResearch.WordTrace]
  refine ⟨19885989449750416861685129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13257326299833611241123419 19885989449750416861685129)
  ·
    refine ⟨14914492087312812646263847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19885989449750416861685129 14914492087312812646263847)
    ·
      refine ⟨22371738130969218969395771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14914492087312812646263847 22371738130969218969395771)
      ·
        refine ⟨33557607196453828454093657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22371738130969218969395771 33557607196453828454093657)
        ·
          refine ⟨25168205397340371340570243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33557607196453828454093657 25168205397340371340570243)
          ·
            refine ⟨37752308096010557010855365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25168205397340371340570243 37752308096010557010855365)
            ·
              refine ⟨7078557768001979439535381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37752308096010557010855365 7078557768001979439535381)
              ·
                refine ⟨331807395375092786228221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7078557768001979439535381 331807395375092786228221)
                ·
                  refine ⟨124427773265659794835583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 331807395375092786228221 124427773265659794835583)
                  ·
                    rfl

theorem cell21_545225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 6, 3].length) (baseStart_545225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545225 prefixEnd_545225 := by exact prefixLift 545225
  have htrace : WordTrace (prefixWord ++ tailWord_545225) baseStart_545225 baseEnd_545225 := by
    simpa [prefixWord, tailWord_545225, baseEnd_545225] using wordTrace_append hprefix tailTrace_545225
  have hstable : (prefixWord ++ tailWord_545225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545225).length < 2 ^ (prefixWord ++ tailWord_545225).sum := by decide
  have hdescent : baseEnd_545225 < baseStart_545225 := by decide
  rcases family_descends (prefixWord ++ tailWord_545225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545287 : List Nat := [1, 1, 4, 3, 3, 2, 1, 6]
def baseStart_545287 : Nat := 118140960795 + 545287 * 2 ^ 59
def prefixEnd_545287 : Nat := 4983230072969 + 3 ^ 40 * 545287 * 2
def baseEnd_545287 : Nat := 41480640836787154934041

theorem tailTrace_545287 : CollatzResearch.WordTrace tailWord_545287 prefixEnd_545287 41480640836787154934041 := by
  unfold tailWord_545287
  simp only [CollatzResearch.WordTrace]
  refine ⟨19888250775525801450442115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13258833850350534300294743 19888250775525801450442115)
  ·
    refine ⟨29832376163288702175663173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19888250775525801450442115 29832376163288702175663173)
    ·
      refine ⟨5593570530616631657936845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29832376163288702175663173 5593570530616631657936845)
      ·
        refine ⟨2097588948981236871726317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5593570530616631657936845 2097588948981236871726317)
        ·
          refine ⟨786595855867963826897369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2097588948981236871726317 786595855867963826897369)
          ·
            refine ⟨589946891900972870173027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786595855867963826897369 589946891900972870173027)
            ·
              refine ⟨884920337851459305259541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589946891900972870173027 884920337851459305259541)
              ·
                refine ⟨41480640836787154934041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 884920337851459305259541 41480640836787154934041)
                ·
                  rfl

theorem cell21_545287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 6].length) (baseStart_545287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545287 prefixEnd_545287 := by exact prefixLift 545287
  have htrace : WordTrace (prefixWord ++ tailWord_545287) baseStart_545287 baseEnd_545287 := by
    simpa [prefixWord, tailWord_545287, baseEnd_545287] using wordTrace_append hprefix tailTrace_545287
  have hstable : (prefixWord ++ tailWord_545287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545287).length < 2 ^ (prefixWord ++ tailWord_545287).sum := by decide
  have hdescent : baseEnd_545287 < baseStart_545287 := by decide
  rcases family_descends (prefixWord ++ tailWord_545287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545394 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 5]
def baseStart_545394 : Nat := 118140960795 + 545394 * 2 ^ 59
def prefixEnd_545394 : Nat := 4983230072969 + 3 ^ 40 * 545394 * 2
def baseEnd_545394 : Nat := 124466341368153056518571

theorem tailTrace_545394 : CollatzResearch.WordTrace tailWord_545394 prefixEnd_545394 124466341368153056518571 := by
  unfold tailWord_545394
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973038346534539681146809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13261435590758772483058157 4973038346534539681146809)
  ·
    refine ⟨3729778759900904760860107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4973038346534539681146809 3729778759900904760860107)
    ·
      refine ⟨5594668139851357141290161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3729778759900904760860107 5594668139851357141290161)
      ·
        refine ⟨4196001104888517855967621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5594668139851357141290161 4196001104888517855967621)
        ·
          refine ⟨786750207166597097993929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4196001104888517855967621 786750207166597097993929)
          ·
            refine ⟨590062655374947823495447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786750207166597097993929 590062655374947823495447)
            ·
              refine ⟨885093983062421735243171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590062655374947823495447 885093983062421735243171)
              ·
                refine ⟨1327640974593632602864757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885093983062421735243171 1327640974593632602864757)
                ·
                  refine ⟨124466341368153056518571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1327640974593632602864757 124466341368153056518571)
                  ·
                    rfl

theorem cell21_545394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_545394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545394 prefixEnd_545394 := by exact prefixLift 545394
  have htrace : WordTrace (prefixWord ++ tailWord_545394) baseStart_545394 baseEnd_545394 := by
    simpa [prefixWord, tailWord_545394, baseEnd_545394] using wordTrace_append hprefix tailTrace_545394
  have hstable : (prefixWord ++ tailWord_545394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545394).length < 2 ^ (prefixWord ++ tailWord_545394).sum := by decide
  have hdescent : baseEnd_545394 < baseStart_545394 := by decide
  rcases family_descends (prefixWord ++ tailWord_545394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545408 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 4]
def baseStart_545408 : Nat := 118140960795 + 545408 * 2 ^ 59
def prefixEnd_545408 : Nat := 4983230072969 + 3 ^ 40 * 545408 * 2
def baseEnd_545408 : Nat := 124469536358892143285209

theorem tailTrace_545408 : CollatzResearch.WordTrace tailWord_545408 prefixEnd_545408 124469536358892143285209 := by
  unfold tailWord_545408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9946332004043719557798439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13261776005391626077064585 9946332004043719557798439)
  ·
    refine ⟨14919498006065579336697659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9946332004043719557798439 14919498006065579336697659)
    ·
      refine ⟨22379247009098369005046489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14919498006065579336697659 22379247009098369005046489)
      ·
        refine ⟨16784435256823776753784867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22379247009098369005046489 16784435256823776753784867)
        ·
          refine ⟨25176652885235665130677301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16784435256823776753784867 25176652885235665130677301)
          ·
            refine ⟨2360311207990843606000997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25176652885235665130677301 2360311207990843606000997)
            ·
              refine ⟨442558351498283176125187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2360311207990843606000997 442558351498283176125187)
              ·
                refine ⟨663837527247424764187781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442558351498283176125187 663837527247424764187781)
                ·
                  refine ⟨124469536358892143285209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 663837527247424764187781 124469536358892143285209)
                  ·
                    rfl

theorem cell21_545408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 4].length) (baseStart_545408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545408 prefixEnd_545408 := by exact prefixLift 545408
  have htrace : WordTrace (prefixWord ++ tailWord_545408) baseStart_545408 baseEnd_545408 := by
    simpa [prefixWord, tailWord_545408, baseEnd_545408] using wordTrace_append hprefix tailTrace_545408
  have hstable : (prefixWord ++ tailWord_545408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545408).length < 2 ^ (prefixWord ++ tailWord_545408).sum := by decide
  have hdescent : baseEnd_545408 < baseStart_545408 := by decide
  rcases family_descends (prefixWord ++ tailWord_545408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545543 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 6]
def baseStart_545543 : Nat := 118140960795 + 545543 * 2 ^ 59
def prefixEnd_545543 : Nat := 4983230072969 + 3 ^ 40 * 545543 * 2
def baseEnd_545543 : Nat := 124500345198161908534933

theorem tailTrace_545543 : CollatzResearch.WordTrace tailWord_545543 prefixEnd_545543 124500345198161908534933 := by
  unfold tailWord_545543
  simp only [CollatzResearch.WordTrace]
  refine ⟨19897587862598357171761283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13265058575065571447840855 19897587862598357171761283)
  ·
    refine ⟨29846381793897535757641925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19897587862598357171761283 29846381793897535757641925)
    ·
      refine ⟨5596196586355787954557861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29846381793897535757641925 5596196586355787954557861)
      ·
        refine ⟨1049286859941710241479599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5596196586355787954557861 1049286859941710241479599)
        ·
          refine ⟨1573930289912565362219399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049286859941710241479599 1573930289912565362219399)
          ·
            refine ⟨2360895434868848043329099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1573930289912565362219399 2360895434868848043329099)
            ·
              refine ⟨3541343152303272064993649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2360895434868848043329099 3541343152303272064993649)
              ·
                refine ⟨2656007364227454048745237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3541343152303272064993649 2656007364227454048745237)
                ·
                  refine ⟨124500345198161908534933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2656007364227454048745237 124500345198161908534933)
                  ·
                    rfl

theorem cell21_545543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_545543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545543 prefixEnd_545543 := by exact prefixLift 545543
  have htrace : WordTrace (prefixWord ++ tailWord_545543) baseStart_545543 baseEnd_545543 := by
    simpa [prefixWord, tailWord_545543, baseEnd_545543] using wordTrace_append hprefix tailTrace_545543
  have hstable : (prefixWord ++ tailWord_545543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545543).length < 2 ^ (prefixWord ++ tailWord_545543).sum := by decide
  have hdescent : baseEnd_545543 < baseStart_545543 := by decide
  rcases family_descends (prefixWord ++ tailWord_545543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545732 : List Nat := [2, 3, 3, 3, 1, 1, 3, 2, 3]
def baseStart_545732 : Nat := 118140960795 + 545732 * 2 ^ 59
def prefixEnd_545732 : Nat := 4983230072969 + 3 ^ 40 * 545732 * 2
def baseEnd_545732 : Nat := 124543477573139579884547

theorem tailTrace_545732 : CollatzResearch.WordTrace tailWord_545732 prefixEnd_545732 124543477573139579884547 := by
  unfold tailWord_545732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9952240629456821225195725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13269654172609094966927633 9952240629456821225195725)
  ·
    refine ⟨3732090236046307959448397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9952240629456821225195725 3732090236046307959448397)
    ·
      refine ⟨1399533838517365484793149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3732090236046307959448397 1399533838517365484793149)
      ·
        refine ⟨524825189444012056797431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1399533838517365484793149 524825189444012056797431)
        ·
          refine ⟨787237784166018085196147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524825189444012056797431 787237784166018085196147)
          ·
            refine ⟨1180856676249027127794221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787237784166018085196147 1180856676249027127794221)
            ·
              refine ⟨442821253593385172922833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1180856676249027127794221 442821253593385172922833)
              ·
                refine ⟨332115940195038879692125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442821253593385172922833 332115940195038879692125)
                ·
                  refine ⟨124543477573139579884547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332115940195038879692125 124543477573139579884547)
                  ·
                    rfl

theorem cell21_545732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_545732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545732 prefixEnd_545732 := by exact prefixLift 545732
  have htrace : WordTrace (prefixWord ++ tailWord_545732) baseStart_545732 baseEnd_545732 := by
    simpa [prefixWord, tailWord_545732, baseEnd_545732] using wordTrace_append hprefix tailTrace_545732
  have hstable : (prefixWord ++ tailWord_545732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545732).length < 2 ^ (prefixWord ++ tailWord_545732).sum := by decide
  have hdescent : baseEnd_545732 < baseStart_545732 := by decide
  rcases family_descends (prefixWord ++ tailWord_545732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545802 : List Nat := [3, 1, 2, 2, 3, 3, 1, 6]
def baseStart_545802 : Nat := 118140960795 + 545802 * 2 ^ 59
def prefixEnd_545802 : Nat := 4983230072969 + 3 ^ 40 * 545802 * 2
def baseEnd_545802 : Nat := 41519817508945004572579

theorem tailTrace_545802 : CollatzResearch.WordTrace tailWord_545802 prefixEnd_545802 41519817508945004572579 := by
  unfold tailWord_545802
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976758592165011101359915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13271356245773362936959773 4976758592165011101359915)
  ·
    refine ⟨7465137888247516652039873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976758592165011101359915 7465137888247516652039873)
    ·
      refine ⟨5598853416185637489029905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7465137888247516652039873 5598853416185637489029905)
      ·
        refine ⟨4199140062139228116772429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5598853416185637489029905 4199140062139228116772429)
        ·
          refine ⟨1574677523302210543789661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4199140062139228116772429 1574677523302210543789661)
          ·
            refine ⟨590504071238328953921123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1574677523302210543789661 590504071238328953921123)
            ·
              refine ⟨885756106857493430881685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590504071238328953921123 885756106857493430881685)
              ·
                refine ⟨41519817508945004572579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 885756106857493430881685 41519817508945004572579)
                ·
                  rfl

theorem cell21_545802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_545802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545802 prefixEnd_545802 := by exact prefixLift 545802
  have htrace : WordTrace (prefixWord ++ tailWord_545802) baseStart_545802 baseEnd_545802 := by
    simpa [prefixWord, tailWord_545802, baseEnd_545802] using wordTrace_append hprefix tailTrace_545802
  have hstable : (prefixWord ++ tailWord_545802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545802).length < 2 ^ (prefixWord ++ tailWord_545802).sum := by decide
  have hdescent : baseEnd_545802 < baseStart_545802 := by decide
  rcases family_descends (prefixWord ++ tailWord_545802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545816 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 5]
def baseStart_545816 : Nat := 118140960795 + 545816 * 2 ^ 59
def prefixEnd_545816 : Nat := 4983230072969 + 3 ^ 40 * 545816 * 2
def baseEnd_545816 : Nat := 124562647517574100484375

theorem tailTrace_545816 : CollatzResearch.WordTrace tailWord_545816 prefixEnd_545816 124562647517574100484375 := by
  unfold tailWord_545816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953772495304662398224651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13271696660406216530966201 9953772495304662398224651)
  ·
    refine ⟨14930658742956993597336977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9953772495304662398224651 14930658742956993597336977)
    ·
      refine ⟨11197994057217745198002733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14930658742956993597336977 11197994057217745198002733)
      ·
        refine ⟨4199247771456654449251025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11197994057217745198002733 4199247771456654449251025)
        ·
          refine ⟨3149435828592490836938269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199247771456654449251025 3149435828592490836938269)
          ·
            refine ⟨1181038435722184063851851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3149435828592490836938269 1181038435722184063851851)
            ·
              refine ⟨1771557653583276095777777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181038435722184063851851 1771557653583276095777777)
              ·
                refine ⟨1328668240187457071833333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1771557653583276095777777 1328668240187457071833333)
                ·
                  refine ⟨124562647517574100484375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1328668240187457071833333 124562647517574100484375)
                  ·
                    rfl

theorem cell21_545816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 5].length) (baseStart_545816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545816 prefixEnd_545816 := by exact prefixLift 545816
  have htrace : WordTrace (prefixWord ++ tailWord_545816) baseStart_545816 baseEnd_545816 := by
    simpa [prefixWord, tailWord_545816, baseEnd_545816] using wordTrace_append hprefix tailTrace_545816
  have hstable : (prefixWord ++ tailWord_545816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545816).length < 2 ^ (prefixWord ++ tailWord_545816).sum := by decide
  have hdescent : baseEnd_545816 < baseStart_545816 := by decide
  rcases family_descends (prefixWord ++ tailWord_545816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545906 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_545906 : Nat := 118140960795 + 545906 * 2 ^ 59
def prefixEnd_545906 : Nat := 4983230072969 + 3 ^ 40 * 545906 * 2
def baseEnd_545906 : Nat := 124583186743753943984191

theorem tailTrace_545906 : CollatzResearch.WordTrace tailWord_545906 prefixEnd_545906 124583186743753943984191 := by
  unfold tailWord_545906
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977706890070817541806393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13273885040188846778150381 4977706890070817541806393)
  ·
    refine ⟨3733280167553113156354795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4977706890070817541806393 3733280167553113156354795)
    ·
      refine ⟨5599920251329669734532193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3733280167553113156354795 5599920251329669734532193)
      ·
        refine ⟨4199940188497252300899145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5599920251329669734532193 4199940188497252300899145)
        ·
          refine ⟨3149955141372939225674359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4199940188497252300899145 3149955141372939225674359)
          ·
            refine ⟨4724932712059408838511539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3149955141372939225674359 4724932712059408838511539)
            ·
              refine ⟨7087399068089113257767309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4724932712059408838511539 7087399068089113257767309)
              ·
                refine ⟨2657774650533417471662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7087399068089113257767309 2657774650533417471662741)
                ·
                  refine ⟨124583186743753943984191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2657774650533417471662741 124583186743753943984191)
                  ·
                    rfl

theorem cell21_545906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_545906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545906 prefixEnd_545906 := by exact prefixLift 545906
  have htrace : WordTrace (prefixWord ++ tailWord_545906) baseStart_545906 baseEnd_545906 := by
    simpa [prefixWord, tailWord_545906, baseEnd_545906] using wordTrace_append hprefix tailTrace_545906
  have hstable : (prefixWord ++ tailWord_545906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545906).length < 2 ^ (prefixWord ++ tailWord_545906).sum := by decide
  have hdescent : baseEnd_545906 < baseStart_545906 := by decide
  rcases family_descends (prefixWord ++ tailWord_545906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545920 : List Nat := [2, 1, 1, 2, 1, 3, 3, 8]
def baseStart_545920 : Nat := 118140960795 + 545920 * 2 ^ 59
def prefixEnd_545920 : Nat := 4983230072969 + 3 ^ 40 * 545920 * 2
def baseEnd_545920 : Nat := 41528793911497676916943

theorem tailTrace_545920 : CollatzResearch.WordTrace tailWord_545920 prefixEnd_545920 41528793911497676916943 := by
  unfold tailWord_545920
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955669091116275279117607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13274225454821700372156809 9955669091116275279117607)
  ·
    refine ⟨14933503636674412918676411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9955669091116275279117607 14933503636674412918676411)
    ·
      refine ⟨22400255455011619378014617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14933503636674412918676411 22400255455011619378014617)
      ·
        refine ⟨16800191591258714533510963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22400255455011619378014617 16800191591258714533510963)
        ·
          refine ⟨25200287386888071800266445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16800191591258714533510963 25200287386888071800266445)
          ·
            refine ⟨9450107770083026925099917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25200287386888071800266445 9450107770083026925099917)
            ·
              refine ⟨3543790413781135096912469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9450107770083026925099917 3543790413781135096912469)
              ·
                refine ⟨41528793911497676916943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3543790413781135096912469 41528793911497676916943)
                ·
                  rfl

theorem cell21_545920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 8].length) (baseStart_545920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545920 prefixEnd_545920 := by exact prefixLift 545920
  have htrace : WordTrace (prefixWord ++ tailWord_545920) baseStart_545920 baseEnd_545920 := by
    simpa [prefixWord, tailWord_545920, baseEnd_545920] using wordTrace_append hprefix tailTrace_545920
  have hstable : (prefixWord ++ tailWord_545920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545920).length < 2 ^ (prefixWord ++ tailWord_545920).sum := by decide
  have hdescent : baseEnd_545920 < baseStart_545920 := by decide
  rcases family_descends (prefixWord ++ tailWord_545920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545954 : List Nat := [3, 3, 1, 3, 3, 8]
def baseStart_545954 : Nat := 118140960795 + 545954 * 2 ^ 59
def prefixEnd_545954 : Nat := 4983230072969 + 3 ^ 40 * 545954 * 2
def baseEnd_545954 : Nat := 4614597814730241747559

theorem tailTrace_545954 : CollatzResearch.WordTrace tailWord_545954 prefixEnd_545954 4614597814730241747559 := by
  unfold tailWord_545954
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978144566027343591243229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13275052176072916243315277 4978144566027343591243229)
  ·
    refine ⟨1866804212260253846716211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4978144566027343591243229 1866804212260253846716211)
    ·
      refine ⟨2800206318390380770074317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866804212260253846716211 2800206318390380770074317)
      ·
        refine ⟨1050077369396392788777869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2800206318390380770074317 1050077369396392788777869)
        ·
          refine ⟨393779013523647295791701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1050077369396392788777869 393779013523647295791701)
          ·
            refine ⟨4614597814730241747559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 393779013523647295791701 4614597814730241747559)
            ·
              rfl

theorem cell21_545954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 8].length) (baseStart_545954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545954 prefixEnd_545954 := by exact prefixLift 545954
  have htrace : WordTrace (prefixWord ++ tailWord_545954) baseStart_545954 baseEnd_545954 := by
    simpa [prefixWord, tailWord_545954, baseEnd_545954] using wordTrace_append hprefix tailTrace_545954
  have hstable : (prefixWord ++ tailWord_545954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545954).length < 2 ^ (prefixWord ++ tailWord_545954).sum := by decide
  have hdescent : baseEnd_545954 < baseStart_545954 := by decide
  rcases family_descends (prefixWord ++ tailWord_545954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545968 : List Nat := [2, 1, 1, 1, 2, 1, 2, 8, 3]
def baseStart_545968 : Nat := 118140960795 + 545968 * 2 ^ 59
def prefixEnd_545968 : Nat := 4983230072969 + 3 ^ 40 * 545968 * 2
def baseEnd_545968 : Nat := 124597335988455613950731

theorem tailTrace_545968 : CollatzResearch.WordTrace tailWord_545968 prefixEnd_545968 124597335988455613950731 := by
  unfold tailWord_545968
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956544443029327377991279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13275392590705769837321705 9956544443029327377991279)
  ·
    refine ⟨14934816664543991066986919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9956544443029327377991279 14934816664543991066986919)
    ·
      refine ⟨22402224996815986600480379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14934816664543991066986919 22402224996815986600480379)
      ·
        refine ⟨33603337495223979900720569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22402224996815986600480379 33603337495223979900720569)
        ·
          refine ⟨25202503121417984925540427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33603337495223979900720569 25202503121417984925540427)
          ·
            refine ⟨37803754682126977388310641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25202503121417984925540427 37803754682126977388310641)
            ·
              refine ⟨28352816011595233041232981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37803754682126977388310641 28352816011595233041232981)
              ·
                refine ⟨332259562635881637201949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 28352816011595233041232981 332259562635881637201949)
                ·
                  refine ⟨124597335988455613950731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332259562635881637201949 124597335988455613950731)
                  ·
                    rfl

theorem cell21_545968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 8, 3].length) (baseStart_545968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545968 prefixEnd_545968 := by exact prefixLift 545968
  have htrace : WordTrace (prefixWord ++ tailWord_545968) baseStart_545968 baseEnd_545968 := by
    simpa [prefixWord, tailWord_545968, baseEnd_545968] using wordTrace_append hprefix tailTrace_545968
  have hstable : (prefixWord ++ tailWord_545968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545968).length < 2 ^ (prefixWord ++ tailWord_545968).sum := by decide
  have hdescent : baseEnd_545968 < baseStart_545968 := by decide
  rcases family_descends (prefixWord ++ tailWord_545968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_545985 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 5]
def baseStart_545985 : Nat := 118140960795 + 545985 * 2 ^ 59
def prefixEnd_545985 : Nat := 4983230072969 + 3 ^ 40 * 545985 * 2
def baseEnd_545985 : Nat := 124601215620067362167363

theorem tailTrace_545985 : CollatzResearch.WordTrace tailWord_545985 prefixEnd_545985 124601215620067362167363 := by
  unfold tailWord_545985
  simp only [CollatzResearch.WordTrace]
  refine ⟨19913708926997066659351409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13275805951331377772900939 19913708926997066659351409)
  ·
    refine ⟨14935281695247799994513557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19913708926997066659351409 14935281695247799994513557)
    ·
      refine ⟨700091329464740624742823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14935281695247799994513557 700091329464740624742823)
      ·
        refine ⟨1050136994197110937114235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700091329464740624742823 1050136994197110937114235)
        ·
          refine ⟨1575205491295666405671353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050136994197110937114235 1575205491295666405671353)
          ·
            refine ⟨1181404118471749804253515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575205491295666405671353 1181404118471749804253515)
            ·
              refine ⟨1772106177707624706380273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1181404118471749804253515 1772106177707624706380273)
              ·
                refine ⟨1329079633280718529785205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1772106177707624706380273 1329079633280718529785205)
                ·
                  refine ⟨124601215620067362167363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329079633280718529785205 124601215620067362167363)
                  ·
                    rfl

theorem cell21_545985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_545985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_545985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_545985 prefixEnd_545985 := by exact prefixLift 545985
  have htrace : WordTrace (prefixWord ++ tailWord_545985) baseStart_545985 baseEnd_545985 := by
    simpa [prefixWord, tailWord_545985, baseEnd_545985] using wordTrace_append hprefix tailTrace_545985
  have hstable : (prefixWord ++ tailWord_545985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_545985).length < 2 ^ (prefixWord ++ tailWord_545985).sum := by decide
  have hdescent : baseEnd_545985 < baseStart_545985 := by decide
  rcases family_descends (prefixWord ++ tailWord_545985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546027 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 5]
def baseStart_546027 : Nat := 118140960795 + 546027 * 2 ^ 59
def prefixEnd_546027 : Nat := 4983230072969 + 3 ^ 40 * 546027 * 2
def baseEnd_546027 : Nat := 124610800592284622467277

theorem tailTrace_546027 : CollatzResearch.WordTrace tailWord_546027 prefixEnd_546027 124610800592284622467277 := by
  unfold tailWord_546027
  simp only [CollatzResearch.WordTrace]
  refine ⟨19915240792844907832380335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13276827195229938554920223 19915240792844907832380335)
  ·
    refine ⟨29872861189267361748570503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19915240792844907832380335 29872861189267361748570503)
    ·
      refine ⟨44809291783901042622855755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29872861189267361748570503 44809291783901042622855755)
      ·
        refine ⟨67213937675851563934283633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44809291783901042622855755 67213937675851563934283633)
        ·
          refine ⟨50410453256888672950712725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67213937675851563934283633 50410453256888672950712725)
          ·
            refine ⟨2362989996416656544564659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50410453256888672950712725 2362989996416656544564659)
            ·
              refine ⟨3544484994624984816846989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2362989996416656544564659 3544484994624984816846989)
              ·
                refine ⟨1329181872984369306317621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544484994624984816846989 1329181872984369306317621)
                ·
                  refine ⟨124610800592284622467277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329181872984369306317621 124610800592284622467277)
                  ·
                    rfl

theorem cell21_546027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_546027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546027 prefixEnd_546027 := by exact prefixLift 546027
  have htrace : WordTrace (prefixWord ++ tailWord_546027) baseStart_546027 baseEnd_546027 := by
    simpa [prefixWord, tailWord_546027, baseEnd_546027] using wordTrace_append hprefix tailTrace_546027
  have hstable : (prefixWord ++ tailWord_546027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546027).length < 2 ^ (prefixWord ++ tailWord_546027).sum := by decide
  have hdescent : baseEnd_546027 < baseStart_546027 := by decide
  rcases family_descends (prefixWord ++ tailWord_546027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546072 : List Nat := [2, 1, 2, 3, 1, 3, 9]
def baseStart_546072 : Nat := 118140960795 + 546072 * 2 ^ 59
def prefixEnd_546072 : Nat := 4983230072969 + 3 ^ 40 * 546072 * 2
def baseEnd_546072 : Nat := 13846785578374949357465

theorem tailTrace_546072 : CollatzResearch.WordTrace tailWord_546072 prefixEnd_546072 13846785578374949357465 := by
  unfold tailWord_546072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9958441038840940258884235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13277921385121253678512313 9958441038840940258884235)
  ·
    refine ⟨14937661558261410388326353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9958441038840940258884235 14937661558261410388326353)
    ·
      refine ⟨11203246168696057791244765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14937661558261410388326353 11203246168696057791244765)
      ·
        refine ⟨4201217313261021671716787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11203246168696057791244765 4201217313261021671716787)
        ·
          refine ⟨6301825969891532507575181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201217313261021671716787 6301825969891532507575181)
          ·
            refine ⟨2363184738709324690340693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6301825969891532507575181 2363184738709324690340693)
            ·
              refine ⟨13846785578374949357465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2363184738709324690340693 13846785578374949357465)
              ·
                rfl

theorem cell21_546072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 9].length) (baseStart_546072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546072 prefixEnd_546072 := by exact prefixLift 546072
  have htrace : WordTrace (prefixWord ++ tailWord_546072) baseStart_546072 baseEnd_546072 := by
    simpa [prefixWord, tailWord_546072, baseEnd_546072] using wordTrace_append hprefix tailTrace_546072
  have hstable : (prefixWord ++ tailWord_546072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546072).length < 2 ^ (prefixWord ++ tailWord_546072).sum := by decide
  have hdescent : baseEnd_546072 < baseStart_546072 := by decide
  rcases family_descends (prefixWord ++ tailWord_546072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546117 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 8]
def baseStart_546117 : Nat := 118140960795 + 546117 * 2 ^ 59
def prefixEnd_546117 : Nat := 4983230072969 + 3 ^ 40 * 546117 * 2
def baseEnd_546117 : Nat := 124631339818464465967093

theorem tailTrace_546117 : CollatzResearch.WordTrace tailWord_546117 prefixEnd_546117 124631339818464465967093 := by
  unfold tailWord_546117
  simp only [CollatzResearch.WordTrace]
  refine ⟨19918523362518853203156605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13279015575012568802104403 19918523362518853203156605)
  ·
    refine ⟨7469446260944569951183727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19918523362518853203156605 7469446260944569951183727)
    ·
      refine ⟨11204169391416854926775591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7469446260944569951183727 11204169391416854926775591)
      ·
        refine ⟨16806254087125282390163387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11204169391416854926775591 16806254087125282390163387)
        ·
          refine ⟨25209381130687923585245081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16806254087125282390163387 25209381130687923585245081)
          ·
            refine ⟨18907035848015942688933811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25209381130687923585245081 18907035848015942688933811)
            ·
              refine ⟨28360553772023914033400717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18907035848015942688933811 28360553772023914033400717)
              ·
                refine ⟨10635207664508967762525269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28360553772023914033400717 10635207664508967762525269)
                ·
                  refine ⟨124631339818464465967093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10635207664508967762525269 124631339818464465967093)
                  ·
                    rfl

theorem cell21_546117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_546117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546117 prefixEnd_546117 := by exact prefixLift 546117
  have htrace : WordTrace (prefixWord ++ tailWord_546117) baseStart_546117 baseEnd_546117 := by
    simpa [prefixWord, tailWord_546117, baseEnd_546117] using wordTrace_append hprefix tailTrace_546117
  have hstable : (prefixWord ++ tailWord_546117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546117).length < 2 ^ (prefixWord ++ tailWord_546117).sum := by decide
  have hdescent : baseEnd_546117 < baseStart_546117 := by decide
  rcases family_descends (prefixWord ++ tailWord_546117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546120 : List Nat := [2, 1, 3, 1, 1, 2, 1, 7, 3]
def baseStart_546120 : Nat := 118140960795 + 546120 * 2 ^ 59
def prefixEnd_546120 : Nat := 4983230072969 + 3 ^ 40 * 546120 * 2
def baseEnd_546120 : Nat := 124632024459337127417087

theorem tailTrace_546120 : CollatzResearch.WordTrace tailWord_546120 prefixEnd_546120 124632024459337127417087 := by
  unfold tailWord_546120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9959316390753992357757907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13279088521005323143677209 9959316390753992357757907)
  ·
    refine ⟨14938974586130988536636861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9959316390753992357757907 14938974586130988536636861)
    ·
      refine ⟨5602115469799120701238823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14938974586130988536636861 5602115469799120701238823)
      ·
        refine ⟨8403173204698681051858235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602115469799120701238823 8403173204698681051858235)
        ·
          refine ⟨12604759807048021577787353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403173204698681051858235 12604759807048021577787353)
          ·
            refine ⟨9453569855286016183340515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12604759807048021577787353 9453569855286016183340515)
            ·
              refine ⟨14180354782929024275010773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9453569855286016183340515 14180354782929024275010773)
              ·
                refine ⟨332352065224899006445565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14180354782929024275010773 332352065224899006445565)
                ·
                  refine ⟨124632024459337127417087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332352065224899006445565 124632024459337127417087)
                  ·
                    rfl

theorem cell21_546120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 3].length) (baseStart_546120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546120 prefixEnd_546120 := by exact prefixLift 546120
  have htrace : WordTrace (prefixWord ++ tailWord_546120) baseStart_546120 baseEnd_546120 := by
    simpa [prefixWord, tailWord_546120, baseEnd_546120] using wordTrace_append hprefix tailTrace_546120
  have hstable : (prefixWord ++ tailWord_546120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546120).length < 2 ^ (prefixWord ++ tailWord_546120).sum := by decide
  have hdescent : baseEnd_546120 < baseStart_546120 := by decide
  rcases family_descends (prefixWord ++ tailWord_546120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546137 : List Nat := [1, 2, 1, 2, 2, 2, 6, 2, 3]
def baseStart_546137 : Nat := 118140960795 + 546137 * 2 ^ 59
def prefixEnd_546137 : Nat := 4983230072969 + 3 ^ 40 * 546137 * 2
def baseEnd_546137 : Nat := 124635904090948875633719

theorem tailTrace_546137 : CollatzResearch.WordTrace tailWord_546137 prefixEnd_546137 124635904090948875633719 := by
  unfold tailWord_546137
  simp only [CollatzResearch.WordTrace]
  refine ⟨19919252822446396618884665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13279501881630931079256443 19919252822446396618884665)
  ·
    refine ⟨14939439616834797464163499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19919252822446396618884665 14939439616834797464163499)
    ·
      refine ⟨22409159425252196196245249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14939439616834797464163499 22409159425252196196245249)
      ·
        refine ⟨16806869568939147147183937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22409159425252196196245249 16806869568939147147183937)
        ·
          refine ⟨12605152176704360360387953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16806869568939147147183937 12605152176704360360387953)
          ·
            refine ⟨9453864132528270270290965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12605152176704360360387953 9453864132528270270290965)
            ·
              refine ⟨443149881212262668919889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9453864132528270270290965 443149881212262668919889)
              ·
                refine ⟨332362410909197001689917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443149881212262668919889 332362410909197001689917)
                ·
                  refine ⟨124635904090948875633719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332362410909197001689917 124635904090948875633719)
                  ·
                    rfl

theorem cell21_546137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 2, 3].length) (baseStart_546137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546137 prefixEnd_546137 := by exact prefixLift 546137
  have htrace : WordTrace (prefixWord ++ tailWord_546137) baseStart_546137 baseEnd_546137 := by
    simpa [prefixWord, tailWord_546137, baseEnd_546137] using wordTrace_append hprefix tailTrace_546137
  have hstable : (prefixWord ++ tailWord_546137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546137).length < 2 ^ (prefixWord ++ tailWord_546137).sum := by decide
  have hdescent : baseEnd_546137 < baseStart_546137 := by decide
  rcases family_descends (prefixWord ++ tailWord_546137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546193 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 6]
def baseStart_546193 : Nat := 118140960795 + 546193 * 2 ^ 59
def prefixEnd_546193 : Nat := 4983230072969 + 3 ^ 40 * 546193 * 2
def baseEnd_546193 : Nat := 124648684053905222700271

theorem tailTrace_546193 : CollatzResearch.WordTrace tailWord_546193 prefixEnd_546193 124648684053905222700271 := by
  unfold tailWord_546193
  simp only [CollatzResearch.WordTrace]
  refine ⟨19921295310243518182923233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13280863540162345455282155 19921295310243518182923233)
  ·
    refine ⟨14940971482682638637192425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19921295310243518182923233 14940971482682638637192425)
    ·
      refine ⟨11205728612011978977894319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14940971482682638637192425 11205728612011978977894319)
      ·
        refine ⟨16808592918017968466841479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11205728612011978977894319 16808592918017968466841479)
        ·
          refine ⟨25212889377026952700262219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16808592918017968466841479 25212889377026952700262219)
          ·
            refine ⟨37819334065540429050393329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25212889377026952700262219 37819334065540429050393329)
            ·
              refine ⟨28364500549155321787794997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37819334065540429050393329 28364500549155321787794997)
              ·
                refine ⟨2659171926483311417605781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28364500549155321787794997 2659171926483311417605781)
                ·
                  refine ⟨124648684053905222700271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2659171926483311417605781 124648684053905222700271)
                  ·
                    rfl

theorem cell21_546193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_546193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546193 prefixEnd_546193 := by exact prefixLift 546193
  have htrace : WordTrace (prefixWord ++ tailWord_546193) baseStart_546193 baseEnd_546193 := by
    simpa [prefixWord, tailWord_546193, baseEnd_546193] using wordTrace_append hprefix tailTrace_546193
  have hstable : (prefixWord ++ tailWord_546193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546193).length < 2 ^ (prefixWord ++ tailWord_546193).sum := by decide
  have hdescent : baseEnd_546193 < baseStart_546193 := by decide
  rcases family_descends (prefixWord ++ tailWord_546193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546196 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 5]
def baseStart_546196 : Nat := 118140960795 + 546196 * 2 ^ 59
def prefixEnd_546196 : Nat := 4983230072969 + 3 ^ 40 * 546196 * 2
def baseEnd_546196 : Nat := 124649368694777884150265

theorem tailTrace_546196 : CollatzResearch.WordTrace tailWord_546196 prefixEnd_546196 124649368694777884150265 := by
  unfold tailWord_546196
  simp only [CollatzResearch.WordTrace]
  refine ⟨9960702364616324847641221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13280936486155099796854961 9960702364616324847641221)
  ·
    refine ⟨1867631693365560908932729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9960702364616324847641221 1867631693365560908932729)
    ·
      refine ⟨1400723770024170681699547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1867631693365560908932729 1400723770024170681699547)
      ·
        refine ⟨2101085655036256022549321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400723770024170681699547 2101085655036256022549321)
        ·
          refine ⟨1575814241277192016911991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2101085655036256022549321 1575814241277192016911991)
          ·
            refine ⟨2363721361915788025367987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1575814241277192016911991 2363721361915788025367987)
            ·
              refine ⟨3545582042873682038051981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363721361915788025367987 3545582042873682038051981)
              ·
                refine ⟨1329593266077630764269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3545582042873682038051981 1329593266077630764269493)
                ·
                  refine ⟨124649368694777884150265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329593266077630764269493 124649368694777884150265)
                  ·
                    rfl

theorem cell21_546196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_546196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546196 prefixEnd_546196 := by exact prefixLift 546196
  have htrace : WordTrace (prefixWord ++ tailWord_546196) baseStart_546196 baseEnd_546196 := by
    simpa [prefixWord, tailWord_546196, baseEnd_546196] using wordTrace_append hprefix tailTrace_546196
  have hstable : (prefixWord ++ tailWord_546196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546196).length < 2 ^ (prefixWord ++ tailWord_546196).sum := by decide
  have hdescent : baseEnd_546196 < baseStart_546196 := by decide
  rcases family_descends (prefixWord ++ tailWord_546196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546216 : List Nat := [2, 1, 6, 1, 3, 1, 2, 5]
def baseStart_546216 : Nat := 118140960795 + 546216 * 2 ^ 59
def prefixEnd_546216 : Nat := 4983230072969 + 3 ^ 40 * 546216 * 2
def baseEnd_546216 : Nat := 41551310989087431272297

theorem tailTrace_546216 : CollatzResearch.WordTrace tailWord_546216 prefixEnd_546216 41551310989087431272297 := by
  unfold tailWord_546216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9961067094580096555505251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13281422792773462074007001 9961067094580096555505251)
  ·
    refine ⟨14941600641870144833257877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9961067094580096555505251 14941600641870144833257877)
    ·
      refine ⟨700387530087663039058963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14941600641870144833257877 700387530087663039058963)
      ·
        refine ⟨1050581295131494558588445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700387530087663039058963 1050581295131494558588445)
        ·
          refine ⟨393967985674310459470667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1050581295131494558588445 393967985674310459470667)
          ·
            refine ⟨590951978511465689206001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393967985674310459470667 590951978511465689206001)
            ·
              refine ⟨443213983883599266904501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590951978511465689206001 443213983883599266904501)
              ·
                refine ⟨41551310989087431272297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443213983883599266904501 41551310989087431272297)
                ·
                  rfl

theorem cell21_546216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_546216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546216 prefixEnd_546216 := by exact prefixLift 546216
  have htrace : WordTrace (prefixWord ++ tailWord_546216) baseStart_546216 baseEnd_546216 := by
    simpa [prefixWord, tailWord_546216, baseEnd_546216] using wordTrace_append hprefix tailTrace_546216
  have hstable : (prefixWord ++ tailWord_546216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546216).length < 2 ^ (prefixWord ++ tailWord_546216).sum := by decide
  have hdescent : baseEnd_546216 < baseStart_546216 := by decide
  rcases family_descends (prefixWord ++ tailWord_546216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546255 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 5]
def baseStart_546255 : Nat := 118140960795 + 546255 * 2 ^ 59
def prefixEnd_546255 : Nat := 4983230072969 + 3 ^ 40 * 546255 * 2
def baseEnd_546255 : Nat := 124662833298606892666811

theorem tailTrace_546255 : CollatzResearch.WordTrace tailWord_546255 prefixEnd_546255 124662833298606892666811 := by
  unfold tailWord_546255
  simp only [CollatzResearch.WordTrace]
  refine ⟨19923556636018902771680219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13282371090679268514453479 19923556636018902771680219)
  ·
    refine ⟨29885334954028354157520329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19923556636018902771680219 29885334954028354157520329)
    ·
      refine ⟨22414001215521265618140247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29885334954028354157520329 22414001215521265618140247)
      ·
        refine ⟨33621001823281898427210371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22414001215521265618140247 33621001823281898427210371)
        ·
          refine ⟨50431502734922847640815557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33621001823281898427210371 50431502734922847640815557)
          ·
            refine ⟨9455906762798033932652917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50431502734922847640815557 9455906762798033932652917)
            ·
              refine ⟨886491259012315681186211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9455906762798033932652917 886491259012315681186211)
              ·
                refine ⟨1329736888518473521779317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 886491259012315681186211 1329736888518473521779317)
                ·
                  refine ⟨124662833298606892666811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329736888518473521779317 124662833298606892666811)
                  ·
                    rfl

theorem cell21_546255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 5].length) (baseStart_546255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546255 prefixEnd_546255 := by exact prefixLift 546255
  have htrace : WordTrace (prefixWord ++ tailWord_546255) baseStart_546255 baseEnd_546255 := by
    simpa [prefixWord, tailWord_546255, baseEnd_546255] using wordTrace_append hprefix tailTrace_546255
  have hstable : (prefixWord ++ tailWord_546255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546255).length < 2 ^ (prefixWord ++ tailWord_546255).sum := by decide
  have hdescent : baseEnd_546255 < baseStart_546255 := by decide
  rcases family_descends (prefixWord ++ tailWord_546255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546306 : List Nat := [3, 4, 1, 2, 1, 2, 1, 4, 3]
def baseStart_546306 : Nat := 118140960795 + 546306 * 2 ^ 59
def prefixEnd_546306 : Nat := 4983230072969 + 3 ^ 40 * 546306 * 2
def baseEnd_546306 : Nat := 124674472193442137316707

theorem tailTrace_546306 : CollatzResearch.WordTrace tailWord_546306 prefixEnd_546306 124674472193442137316707 := by
  unfold tailWord_546306
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981354189708534620446693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13283611172556092321191181 4981354189708534620446693)
  ·
    refine ⟨934003910570350241333755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4981354189708534620446693 934003910570350241333755)
    ·
      refine ⟨1401005865855525362000633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934003910570350241333755 1401005865855525362000633)
      ·
        refine ⟨1050754399391644021500475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1401005865855525362000633 1050754399391644021500475)
        ·
          refine ⟨1576131599087466032250713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050754399391644021500475 1576131599087466032250713)
          ·
            refine ⟨1182098699315599524188035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576131599087466032250713 1182098699315599524188035)
            ·
              refine ⟨1773148048973399286282053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182098699315599524188035 1773148048973399286282053)
              ·
                refine ⟨332465259182512366177885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1773148048973399286282053 332465259182512366177885)
                ·
                  refine ⟨124674472193442137316707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332465259182512366177885 124674472193442137316707)
                  ·
                    rfl

theorem cell21_546306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_546306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546306 prefixEnd_546306 := by exact prefixLift 546306
  have htrace : WordTrace (prefixWord ++ tailWord_546306) baseStart_546306 baseEnd_546306 := by
    simpa [prefixWord, tailWord_546306, baseEnd_546306] using wordTrace_append hprefix tailTrace_546306
  have hstable : (prefixWord ++ tailWord_546306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546306).length < 2 ^ (prefixWord ++ tailWord_546306).sum := by decide
  have hdescent : baseEnd_546306 < baseStart_546306 := by decide
  rcases family_descends (prefixWord ++ tailWord_546306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546486 : List Nat := [5, 1, 3, 1, 1, 1, 3, 6]
def baseStart_546486 : Nat := 118140960795 + 546486 * 2 ^ 59
def prefixEnd_546486 : Nat := 4983230072969 + 3 ^ 40 * 546486 * 2
def baseEnd_546486 : Nat := 41571850215267274772113

theorem tailTrace_546486 : CollatzResearch.WordTrace tailWord_546486 prefixEnd_546486 41571850215267274772113 := by
  unfold tailWord_546486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1245748868636376826458707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13287987932121352815559541 1245748868636376826458707)
  ·
    refine ⟨1868623302954565239688061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1245748868636376826458707 1868623302954565239688061)
    ·
      refine ⟨700733738607961964883023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1868623302954565239688061 700733738607961964883023)
      ·
        refine ⟨1051100607911942947324535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700733738607961964883023 1051100607911942947324535)
        ·
          refine ⟨1576650911867914420986803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051100607911942947324535 1576650911867914420986803)
          ·
            refine ⟨2364976367801871631480205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1576650911867914420986803 2364976367801871631480205)
            ·
              refine ⟨886866137925701861805077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2364976367801871631480205 886866137925701861805077)
              ·
                refine ⟨41571850215267274772113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 886866137925701861805077 41571850215267274772113)
                ·
                  rfl

theorem cell21_546486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_546486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546486 prefixEnd_546486 := by exact prefixLift 546486
  have htrace : WordTrace (prefixWord ++ tailWord_546486) baseStart_546486 baseEnd_546486 := by
    simpa [prefixWord, tailWord_546486, baseEnd_546486] using wordTrace_append hprefix tailTrace_546486
  have hstable : (prefixWord ++ tailWord_546486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546486).length < 2 ^ (prefixWord ++ tailWord_546486).sum := by decide
  have hdescent : baseEnd_546486 < baseStart_546486 := by decide
  rcases family_descends (prefixWord ++ tailWord_546486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546511 : List Nat := [1, 1, 2, 1, 1, 3, 1, 11]
def baseStart_546511 : Nat := 118140960795 + 546511 * 2 ^ 59
def prefixEnd_546511 : Nat := 4983230072969 + 3 ^ 40 * 546511 * 2
def baseEnd_546511 : Nat := 41573751995469112133207

theorem tailTrace_546511 : CollatzResearch.WordTrace tailWord_546511 prefixEnd_546511 41573751995469112133207 := by
  unfold tailWord_546511
  simp only [CollatzResearch.WordTrace]
  refine ⟨19932893723091458492999387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13288595815394305661999591 19932893723091458492999387)
  ·
    refine ⟨29899340584637187739499081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19932893723091458492999387 29899340584637187739499081)
    ·
      refine ⟨22424505438477890804624311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29899340584637187739499081 22424505438477890804624311)
      ·
        refine ⟨33636758157716836206936467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22424505438477890804624311 33636758157716836206936467)
        ·
          refine ⟨50455137236575254310404701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33636758157716836206936467 50455137236575254310404701)
          ·
            refine ⟨18920676463715720366401763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50455137236575254310404701 18920676463715720366401763)
            ·
              refine ⟨28381014695573580549602645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18920676463715720366401763 28381014695573580549602645)
              ·
                refine ⟨41573751995469112133207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 28381014695573580549602645 41573751995469112133207)
                ·
                  rfl

theorem cell21_546511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 11].length) (baseStart_546511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546511 prefixEnd_546511 := by exact prefixLift 546511
  have htrace : WordTrace (prefixWord ++ tailWord_546511) baseStart_546511 baseEnd_546511 := by
    simpa [prefixWord, tailWord_546511, baseEnd_546511] using wordTrace_append hprefix tailTrace_546511
  have hstable : (prefixWord ++ tailWord_546511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546511).length < 2 ^ (prefixWord ++ tailWord_546511).sum := by decide
  have hdescent : baseEnd_546511 < baseStart_546511 := by decide
  rcases family_descends (prefixWord ++ tailWord_546511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546593 : List Nat := [1, 2, 3, 2, 1, 4, 3, 2, 3]
def baseStart_546593 : Nat := 118140960795 + 546593 * 2 ^ 59
def prefixEnd_546593 : Nat := 4983230072969 + 3 ^ 40 * 546593 * 2
def baseEnd_546593 : Nat := 124739969503593416032787

theorem tailTrace_546593 : CollatzResearch.WordTrace tailWord_546593 prefixEnd_546593 124739969503593416032787 := by
  unfold tailWord_546593
  simp only [CollatzResearch.WordTrace]
  refine ⟨19935884508794386497484433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13290589672529590998322955 19935884508794386497484433)
  ·
    refine ⟨14951913381595789873113325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19935884508794386497484433 14951913381595789873113325)
    ·
      refine ⟨5606967518098421202417497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14951913381595789873113325 5606967518098421202417497)
      ·
        refine ⟨4205225638573815901813123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5606967518098421202417497 4205225638573815901813123)
        ·
          refine ⟨6307838457860723852719685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4205225638573815901813123 6307838457860723852719685)
          ·
            refine ⟨1182719710848885722384941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6307838457860723852719685 1182719710848885722384941)
            ·
              refine ⟨443519891568332145894353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1182719710848885722384941 443519891568332145894353)
              ·
                refine ⟨332639918676249109420765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443519891568332145894353 332639918676249109420765)
                ·
                  refine ⟨124739969503593416032787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332639918676249109420765 124739969503593416032787)
                  ·
                    rfl

theorem cell21_546593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2, 3].length) (baseStart_546593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546593 prefixEnd_546593 := by exact prefixLift 546593
  have htrace : WordTrace (prefixWord ++ tailWord_546593) baseStart_546593 baseEnd_546593 := by
    simpa [prefixWord, tailWord_546593, baseEnd_546593] using wordTrace_append hprefix tailTrace_546593
  have hstable : (prefixWord ++ tailWord_546593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546593).length < 2 ^ (prefixWord ++ tailWord_546593).sum := by decide
  have hdescent : baseEnd_546593 < baseStart_546593 := by decide
  rcases family_descends (prefixWord ++ tailWord_546593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546604 : List Nat := [2, 2, 1, 1, 1, 6, 2, 6]
def baseStart_546604 : Nat := 118140960795 + 546604 * 2 ^ 59
def prefixEnd_546604 : Nat := 4983230072969 + 3 ^ 40 * 546604 * 2
def baseEnd_546604 : Nat := 41580826617819947116477

theorem tailTrace_546604 : CollatzResearch.WordTrace tailWord_546604 prefixEnd_546604 41580826617819947116477 := by
  unfold tailWord_546604
  simp only [CollatzResearch.WordTrace]
  refine ⟨9968142855877267688067433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13290857141169690250756577 9968142855877267688067433)
  ·
    refine ⟨7476107141907950766050575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9968142855877267688067433 7476107141907950766050575)
    ·
      refine ⟨11214160712861926149075863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7476107141907950766050575 11214160712861926149075863)
      ·
        refine ⟨16821241069292889223613795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11214160712861926149075863 16821241069292889223613795)
        ·
          refine ⟨25231861603939333835420693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16821241069292889223613795 25231861603939333835420693)
          ·
            refine ⟨1182743512684656273535345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25231861603939333835420693 1182743512684656273535345)
            ·
              refine ⟨887057634513492205151509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182743512684656273535345 887057634513492205151509)
              ·
                refine ⟨41580826617819947116477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 887057634513492205151509 41580826617819947116477)
                ·
                  rfl

theorem cell21_546604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 6].length) (baseStart_546604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546604 prefixEnd_546604 := by exact prefixLift 546604
  have htrace : WordTrace (prefixWord ++ tailWord_546604) baseStart_546604 baseEnd_546604 := by
    simpa [prefixWord, tailWord_546604, baseEnd_546604] using wordTrace_append hprefix tailTrace_546604
  have hstable : (prefixWord ++ tailWord_546604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546604).length < 2 ^ (prefixWord ++ tailWord_546604).sum := by decide
  have hdescent : baseEnd_546604 < baseStart_546604 := by decide
  rcases family_descends (prefixWord ++ tailWord_546604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546686 : List Nat := [4, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_546686 : Nat := 118140960795 + 546686 * 2 ^ 59
def prefixEnd_546686 : Nat := 4983230072969 + 3 ^ 40 * 546686 * 2
def baseEnd_546686 : Nat := 124761193370645920982597

theorem tailTrace_546686 : CollatzResearch.WordTrace tailWord_546686 prefixEnd_546686 124761193370645920982597 := by
  unfold tailWord_546686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492409562182182922577489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13292850998304975587079941 2492409562182182922577489)
  ·
    refine ⟨1869307171636637191933117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2492409562182182922577489 1869307171636637191933117)
    ·
      refine ⟨700990189363738946974919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1869307171636637191933117 700990189363738946974919)
      ·
        refine ⟨1051485284045608420462379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700990189363738946974919 1051485284045608420462379)
        ·
          refine ⟨1577227926068412630693569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051485284045608420462379 1577227926068412630693569)
          ·
            refine ⟨1182920944551309473020177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1577227926068412630693569 1182920944551309473020177)
            ·
              refine ⟨887190708413482104765133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182920944551309473020177 887190708413482104765133)
              ·
                refine ⟨332696515655055789286925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887190708413482104765133 332696515655055789286925)
                ·
                  refine ⟨124761193370645920982597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332696515655055789286925 124761193370645920982597)
                  ·
                    rfl

theorem cell21_546686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_546686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546686 prefixEnd_546686 := by exact prefixLift 546686
  have htrace : WordTrace (prefixWord ++ tailWord_546686) baseStart_546686 baseEnd_546686 := by
    simpa [prefixWord, tailWord_546686, baseEnd_546686] using wordTrace_append hprefix tailTrace_546686
  have hstable : (prefixWord ++ tailWord_546686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546686).length < 2 ^ (prefixWord ++ tailWord_546686).sum := by decide
  have hdescent : baseEnd_546686 < baseStart_546686 := by decide
  rcases family_descends (prefixWord ++ tailWord_546686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546711 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 5]
def baseStart_546711 : Nat := 118140960795 + 546711 * 2 ^ 59
def prefixEnd_546711 : Nat := 4983230072969 + 3 ^ 40 * 546711 * 2
def baseEnd_546711 : Nat := 124766898711251433065879

theorem tailTrace_546711 : CollatzResearch.WordTrace tailWord_546711 prefixEnd_546711 124766898711251433065879 := by
  unfold tailWord_546711
  simp only [CollatzResearch.WordTrace]
  refine ⟨19940188322366892650279987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13293458881577928433519991 19940188322366892650279987)
  ·
    refine ⟨29910282483550338975419981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19940188322366892650279987 29910282483550338975419981)
    ·
      refine ⟨11216355931331377115782493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29910282483550338975419981 11216355931331377115782493)
      ·
        refine ⟨4206133474249266418418435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11216355931331377115782493 4206133474249266418418435)
        ·
          refine ⟨6309200211373899627627653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206133474249266418418435 6309200211373899627627653)
          ·
            refine ⟨1182975039632606180180185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6309200211373899627627653 1182975039632606180180185)
            ·
              refine ⟨887231279724454635135139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1182975039632606180180185 887231279724454635135139)
              ·
                refine ⟨1330846919586681952702709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 887231279724454635135139 1330846919586681952702709)
                ·
                  refine ⟨124766898711251433065879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1330846919586681952702709 124766898711251433065879)
                  ·
                    rfl

theorem cell21_546711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 5].length) (baseStart_546711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546711 prefixEnd_546711 := by exact prefixLift 546711
  have htrace : WordTrace (prefixWord ++ tailWord_546711) baseStart_546711 baseEnd_546711 := by
    simpa [prefixWord, tailWord_546711, baseEnd_546711] using wordTrace_append hprefix tailTrace_546711
  have hstable : (prefixWord ++ tailWord_546711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546711).length < 2 ^ (prefixWord ++ tailWord_546711).sum := by decide
  have hdescent : baseEnd_546711 < baseStart_546711 := by decide
  rcases family_descends (prefixWord ++ tailWord_546711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546725 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 4]
def baseStart_546725 : Nat := 118140960795 + 546725 * 2 ^ 59
def prefixEnd_546725 : Nat := 4983230072969 + 3 ^ 40 * 546725 * 2
def baseEnd_546725 : Nat := 124770093701990519832517

theorem tailTrace_546725 : CollatzResearch.WordTrace tailWord_546725 prefixEnd_546725 124770093701990519832517 := by
  unfold tailWord_546725
  simp only [CollatzResearch.WordTrace]
  refine ⟨19940698944316173041289629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13293799296210782027526419 19940698944316173041289629)
  ·
    refine ⟨7477762104118564890483611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19940698944316173041289629 7477762104118564890483611)
    ·
      refine ⟨11216643156177847335725417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7477762104118564890483611 11216643156177847335725417)
      ·
        refine ⟨8412482367133385501794063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11216643156177847335725417 8412482367133385501794063)
        ·
          refine ⟨12618723550700078252691095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8412482367133385501794063 12618723550700078252691095)
          ·
            refine ⟨18928085326050117379036643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12618723550700078252691095 18928085326050117379036643)
            ·
              refine ⟨28392127989075176068554965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18928085326050117379036643 28392127989075176068554965)
              ·
                refine ⟨665440499743949439106757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28392127989075176068554965 665440499743949439106757)
                ·
                  refine ⟨124770093701990519832517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665440499743949439106757 124770093701990519832517)
                  ·
                    rfl

theorem cell21_546725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_546725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546725 prefixEnd_546725 := by exact prefixLift 546725
  have htrace : WordTrace (prefixWord ++ tailWord_546725) baseStart_546725 baseEnd_546725 := by
    simpa [prefixWord, tailWord_546725, baseEnd_546725] using wordTrace_append hprefix tailTrace_546725
  have hstable : (prefixWord ++ tailWord_546725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546725).length < 2 ^ (prefixWord ++ tailWord_546725).sum := by decide
  have hdescent : baseEnd_546725 < baseStart_546725 := by decide
  rcases family_descends (prefixWord ++ tailWord_546725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546739 : List Nat := [1, 1, 1, 2, 3, 1, 5, 7]
def baseStart_546739 : Nat := 118140960795 + 546739 * 2 ^ 59
def prefixEnd_546739 : Nat := 4983230072969 + 3 ^ 40 * 546739 * 2
def baseEnd_546739 : Nat := 41591096230909868866385

theorem tailTrace_546739 : CollatzResearch.WordTrace tailWord_546739 prefixEnd_546739 41591096230909868866385 := by
  unfold tailWord_546739
  simp only [CollatzResearch.WordTrace]
  refine ⟨19941209566265453432299271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13294139710843635621532847 19941209566265453432299271)
  ·
    refine ⟨29911814349398180148448907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19941209566265453432299271 29911814349398180148448907)
    ·
      refine ⟨44867721524097270222673361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29911814349398180148448907 44867721524097270222673361)
      ·
        refine ⟨33650791143072952667005021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44867721524097270222673361 33650791143072952667005021)
        ·
          refine ⟨12619046678652357250126883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33650791143072952667005021 12619046678652357250126883)
          ·
            refine ⟨18928570017978535875190325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12619046678652357250126883 18928570017978535875190325)
            ·
              refine ⟨1774553439185487738299093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18928570017978535875190325 1774553439185487738299093)
              ·
                refine ⟨41591096230909868866385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1774553439185487738299093 41591096230909868866385)
                ·
                  rfl

theorem cell21_546739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 7].length) (baseStart_546739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546739 prefixEnd_546739 := by exact prefixLift 546739
  have htrace : WordTrace (prefixWord ++ tailWord_546739) baseStart_546739 baseEnd_546739 := by
    simpa [prefixWord, tailWord_546739, baseEnd_546739] using wordTrace_append hprefix tailTrace_546739
  have hstable : (prefixWord ++ tailWord_546739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546739).length < 2 ^ (prefixWord ++ tailWord_546739).sum := by decide
  have hdescent : baseEnd_546739 < baseStart_546739 := by decide
  rcases family_descends (prefixWord ++ tailWord_546739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546821 : List Nat := [1, 3, 1, 1, 2, 6, 2, 2, 3]
def baseStart_546821 : Nat := 118140960795 + 546821 * 2 ^ 59
def prefixEnd_546821 : Nat := 4983230072969 + 3 ^ 40 * 546821 * 2
def baseEnd_546821 : Nat := 124792002209915686232321

theorem tailTrace_546821 : CollatzResearch.WordTrace tailWord_546821 prefixEnd_546821 124792002209915686232321 := by
  unfold tailWord_546821
  simp only [CollatzResearch.WordTrace]
  refine ⟨19944200351968381436784317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296133567978920957856211 19944200351968381436784317)
  ·
    refine ⟨7479075131988143038794119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19944200351968381436784317 7479075131988143038794119)
    ·
      refine ⟨11218612697982214558191179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7479075131988143038794119 11218612697982214558191179)
      ·
        refine ⟨16827919046973321837286769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11218612697982214558191179 16827919046973321837286769)
        ·
          refine ⟨12620939285229991377965077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16827919046973321837286769 12620939285229991377965077)
          ·
            refine ⟨591606528995155845842113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12620939285229991377965077 591606528995155845842113)
            ·
              refine ⟨443704896746366884381585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591606528995155845842113 443704896746366884381585)
              ·
                refine ⟨332778672559775163286189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443704896746366884381585 332778672559775163286189)
                ·
                  refine ⟨124792002209915686232321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332778672559775163286189 124792002209915686232321)
                  ·
                    rfl

theorem cell21_546821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 2, 2, 3].length) (baseStart_546821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546821 prefixEnd_546821 := by exact prefixLift 546821
  have htrace : WordTrace (prefixWord ++ tailWord_546821) baseStart_546821 baseEnd_546821 := by
    simpa [prefixWord, tailWord_546821, baseEnd_546821] using wordTrace_append hprefix tailTrace_546821
  have hstable : (prefixWord ++ tailWord_546821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546821).length < 2 ^ (prefixWord ++ tailWord_546821).sum := by decide
  have hdescent : baseEnd_546821 < baseStart_546821 := by decide
  rcases family_descends (prefixWord ++ tailWord_546821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546849 : List Nat := [1, 2, 3, 2, 4, 1, 3, 5]
def baseStart_546849 : Nat := 118140960795 + 546849 * 2 ^ 59
def prefixEnd_546849 : Nat := 4983230072969 + 3 ^ 40 * 546849 * 2
def baseEnd_546849 : Nat := 41599464063797953255199

theorem tailTrace_546849 : CollatzResearch.WordTrace tailWord_546849 prefixEnd_546849 41599464063797953255199 := by
  unfold tailWord_546849
  simp only [CollatzResearch.WordTrace]
  refine ⟨19945221595866942218803601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13296814397244628145869067 19945221595866942218803601)
  ·
    refine ⟨14958916196900206664102701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19945221595866942218803601 14958916196900206664102701)
    ·
      refine ⟨5609593573837577499038513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14958916196900206664102701 5609593573837577499038513)
      ·
        refine ⟨4207195180378183124278885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5609593573837577499038513 4207195180378183124278885)
        ·
          refine ⟨788849096320909335802291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4207195180378183124278885 788849096320909335802291)
          ·
            refine ⟨1183273644481364003703437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788849096320909335802291 1183273644481364003703437)
            ·
              refine ⟨443727616680511501388789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1183273644481364003703437 443727616680511501388789)
              ·
                refine ⟨41599464063797953255199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 443727616680511501388789 41599464063797953255199)
                ·
                  rfl

theorem cell21_546849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 5].length) (baseStart_546849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546849 prefixEnd_546849 := by exact prefixLift 546849
  have htrace : WordTrace (prefixWord ++ tailWord_546849) baseStart_546849 baseEnd_546849 := by
    simpa [prefixWord, tailWord_546849, baseEnd_546849] using wordTrace_append hprefix tailTrace_546849
  have hstable : (prefixWord ++ tailWord_546849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546849).length < 2 ^ (prefixWord ++ tailWord_546849).sum := by decide
  have hdescent : baseEnd_546849 < baseStart_546849 := by decide
  rcases family_descends (prefixWord ++ tailWord_546849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546877 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 6]
def baseStart_546877 : Nat := 118140960795 + 546877 * 2 ^ 59
def prefixEnd_546877 : Nat := 4983230072969 + 3 ^ 40 * 546877 * 2
def baseEnd_546877 : Nat := 124804782172872033298873

theorem tailTrace_546877 : CollatzResearch.WordTrace tailWord_546877 prefixEnd_546877 124804782172872033298873 := by
  unfold tailWord_546877
  simp only [CollatzResearch.WordTrace]
  refine ⟨19946242839765503000822885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13297495226510335333881923 19946242839765503000822885)
  ·
    refine ⟨3739920532456031812654291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19946242839765503000822885 3739920532456031812654291)
    ·
      refine ⟨5609880798684047718981437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3739920532456031812654291 5609880798684047718981437)
      ·
        refine ⟨2103705299506517894618039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5609880798684047718981437 2103705299506517894618039)
        ·
          refine ⟨3155557949259776841927059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103705299506517894618039 3155557949259776841927059)
          ·
            refine ⟨4733336923889665262890589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3155557949259776841927059 4733336923889665262890589)
            ·
              refine ⟨1775001346458624473583971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4733336923889665262890589 1775001346458624473583971)
              ·
                refine ⟨2662502019687936710375957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1775001346458624473583971 2662502019687936710375957)
                ·
                  refine ⟨124804782172872033298873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2662502019687936710375957 124804782172872033298873)
                  ·
                    rfl

theorem cell21_546877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_546877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546877 prefixEnd_546877 := by exact prefixLift 546877
  have htrace : WordTrace (prefixWord ++ tailWord_546877) baseStart_546877 baseEnd_546877 := by
    simpa [prefixWord, tailWord_546877, baseEnd_546877] using wordTrace_append hprefix tailTrace_546877
  have hstable : (prefixWord ++ tailWord_546877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546877).length < 2 ^ (prefixWord ++ tailWord_546877).sum := by decide
  have hdescent : baseEnd_546877 < baseStart_546877 := by decide
  rcases family_descends (prefixWord ++ tailWord_546877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546908 : List Nat := [2, 2, 4, 1, 1, 3, 1, 7]
def baseStart_546908 : Nat := 118140960795 + 546908 * 2 ^ 59
def prefixEnd_546908 : Nat := 4983230072969 + 3 ^ 40 * 546908 * 2
def baseEnd_546908 : Nat := 41603952265074289427381

theorem tailTrace_546908 : CollatzResearch.WordTrace tailWord_546908 prefixEnd_546908 41603952265074289427381 := by
  unfold tailWord_546908
  simp only [CollatzResearch.WordTrace]
  refine ⟨9973686751326597647600689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13298249001768796863467585 9973686751326597647600689)
  ·
    refine ⟨7480265063494948235700517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9973686751326597647600689 7480265063494948235700517)
    ·
      refine ⟨1402549699405302794193847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7480265063494948235700517 1402549699405302794193847)
      ·
        refine ⟨2103824549107954191290771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1402549699405302794193847 2103824549107954191290771)
        ·
          refine ⟨3155736823661931286936157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2103824549107954191290771 3155736823661931286936157)
          ·
            refine ⟨1183401308873224232601059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3155736823661931286936157 1183401308873224232601059)
            ·
              refine ⟨1775101963309836348901589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183401308873224232601059 1775101963309836348901589)
              ·
                refine ⟨41603952265074289427381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1775101963309836348901589 41603952265074289427381)
                ·
                  rfl

theorem cell21_546908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_546908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546908 prefixEnd_546908 := by exact prefixLift 546908
  have htrace : WordTrace (prefixWord ++ tailWord_546908) baseStart_546908 baseEnd_546908 := by
    simpa [prefixWord, tailWord_546908, baseEnd_546908] using wordTrace_append hprefix tailTrace_546908
  have hstable : (prefixWord ++ tailWord_546908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546908).length < 2 ^ (prefixWord ++ tailWord_546908).sum := by decide
  have hdescent : baseEnd_546908 < baseStart_546908 := by decide
  rcases family_descends (prefixWord ++ tailWord_546908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546914 : List Nat := [3, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_546914 : Nat := 118140960795 + 546914 * 2 ^ 59
def prefixEnd_546914 : Nat := 4983230072969 + 3 ^ 40 * 546914 * 2
def baseEnd_546914 : Nat := 124813226076968191182131

theorem tailTrace_546914 : CollatzResearch.WordTrace tailWord_546914 prefixEnd_546914 124813226076968191182131 := by
  unfold tailWord_546914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986898085157864579979949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13298394893754305546613197 4986898085157864579979949)
  ·
    refine ⟨1870086781934199217492481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4986898085157864579979949 1870086781934199217492481)
    ·
      refine ⟨1402565086450649413119361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1870086781934199217492481 1402565086450649413119361)
      ·
        refine ⟨1051923814837987059839521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1402565086450649413119361 1051923814837987059839521)
        ·
          refine ⟨788942861128490294879641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051923814837987059839521 788942861128490294879641)
          ·
            refine ⟨591707145846367721159731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788942861128490294879641 591707145846367721159731)
            ·
              refine ⟨887560718769551581739597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591707145846367721159731 887560718769551581739597)
              ·
                refine ⟨332835269538581843152349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887560718769551581739597 332835269538581843152349)
                ·
                  refine ⟨124813226076968191182131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332835269538581843152349 124813226076968191182131)
                  ·
                    rfl

theorem cell21_546914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_546914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546914 prefixEnd_546914 := by exact prefixLift 546914
  have htrace : WordTrace (prefixWord ++ tailWord_546914) baseStart_546914 baseEnd_546914 := by
    simpa [prefixWord, tailWord_546914, baseEnd_546914] using wordTrace_append hprefix tailTrace_546914
  have hstable : (prefixWord ++ tailWord_546914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546914).length < 2 ^ (prefixWord ++ tailWord_546914).sum := by decide
  have hdescent : baseEnd_546914 < baseStart_546914 := by decide
  rcases family_descends (prefixWord ++ tailWord_546914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546953 : List Nat := [1, 2, 1, 1, 4, 2, 3, 3, 4]
def baseStart_546953 : Nat := 118140960795 + 546953 * 2 ^ 59
def prefixEnd_546953 : Nat := 4983230072969 + 3 ^ 40 * 546953 * 2
def baseEnd_546953 : Nat := 124822126408312790032051

theorem tailTrace_546953 : CollatzResearch.WordTrace tailWord_546953 prefixEnd_546953 124822126408312790032051 := by
  unfold tailWord_546953
  simp only [CollatzResearch.WordTrace]
  refine ⟨19949014787490167980589513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13299343191660111987059675 19949014787490167980589513)
  ·
    refine ⟨14961761090617625985442135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19949014787490167980589513 14961761090617625985442135)
    ·
      refine ⟨22442641635926438978163203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14961761090617625985442135 22442641635926438978163203)
      ·
        refine ⟨33663962453889658467244805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22442641635926438978163203 33663962453889658467244805)
        ·
          refine ⟨6311992960104310962608401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33663962453889658467244805 6311992960104310962608401)
          ·
            refine ⟨4733994720078233221956301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6311992960104310962608401 4733994720078233221956301)
            ·
              refine ⟨1775248020029337458233613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4733994720078233221956301 1775248020029337458233613)
              ·
                refine ⟨665718007511001546837605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775248020029337458233613 665718007511001546837605)
                ·
                  refine ⟨124822126408312790032051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665718007511001546837605 124822126408312790032051)
                  ·
                    rfl

theorem cell21_546953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 3, 4].length) (baseStart_546953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546953 prefixEnd_546953 := by exact prefixLift 546953
  have htrace : WordTrace (prefixWord ++ tailWord_546953) baseStart_546953 baseEnd_546953 := by
    simpa [prefixWord, tailWord_546953, baseEnd_546953] using wordTrace_append hprefix tailTrace_546953
  have hstable : (prefixWord ++ tailWord_546953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546953).length < 2 ^ (prefixWord ++ tailWord_546953).sum := by decide
  have hdescent : baseEnd_546953 < baseStart_546953 := by decide
  rcases family_descends (prefixWord ++ tailWord_546953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_546990 : List Nat := [4, 1, 4, 2, 1, 1, 1, 4, 3]
def baseStart_546990 : Nat := 118140960795 + 546990 * 2 ^ 59
def prefixEnd_546990 : Nat := 4983230072969 + 3 ^ 40 * 546990 * 2
def baseEnd_546990 : Nat := 124830570312408947915309

theorem tailTrace_546990 : CollatzResearch.WordTrace tailWord_546990 prefixEnd_546990 124830570312408947915309 := by
  unfold tailWord_546990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493795536044515412460803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13300242858904082199790949 2493795536044515412460803)
  ·
    refine ⟨3740693304066773118691205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2493795536044515412460803 3740693304066773118691205)
    ·
      refine ⟨701379994512519959754601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3740693304066773118691205 701379994512519959754601)
      ·
        refine ⟨526034995884389969815951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 701379994512519959754601 526034995884389969815951)
        ·
          refine ⟨789052493826584954723927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526034995884389969815951 789052493826584954723927)
          ·
            refine ⟨1183578740739877432085891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789052493826584954723927 1183578740739877432085891)
            ·
              refine ⟨1775368111109816148128837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183578740739877432085891 1775368111109816148128837)
              ·
                refine ⟨332881520833090527774157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1775368111109816148128837 332881520833090527774157)
                ·
                  refine ⟨124830570312408947915309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332881520833090527774157 124830570312408947915309)
                  ·
                    rfl

theorem cell21_546990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_546990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_546990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_546990 prefixEnd_546990 := by exact prefixLift 546990
  have htrace : WordTrace (prefixWord ++ tailWord_546990) baseStart_546990 baseEnd_546990 := by
    simpa [prefixWord, tailWord_546990, baseEnd_546990] using wordTrace_append hprefix tailTrace_546990
  have hstable : (prefixWord ++ tailWord_546990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_546990).length < 2 ^ (prefixWord ++ tailWord_546990).sum := by decide
  have hdescent : baseEnd_546990 < baseStart_546990 := by decide
  rcases family_descends (prefixWord ++ tailWord_546990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547032 : List Nat := [2, 1, 2, 2, 4, 2, 2, 3, 3]
def baseStart_547032 : Nat := 118140960795 + 547032 * 2 ^ 59
def prefixEnd_547032 : Nat := 4983230072969 + 3 ^ 40 * 547032 * 2
def baseEnd_547032 : Nat := 124840155284626208215223

theorem tailTrace_547032 : CollatzResearch.WordTrace tailWord_547032 prefixEnd_547032 124840155284626208215223 := by
  unfold tailWord_547032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9975948077101982236357675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13301264102802642981810233 9975948077101982236357675)
  ·
    refine ⟨14963922115652973354536513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9975948077101982236357675 14963922115652973354536513)
    ·
      refine ⟨11222941586739730015902385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14963922115652973354536513 11222941586739730015902385)
      ·
        refine ⟨8417206190054797511926789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11222941586739730015902385 8417206190054797511926789)
        ·
          refine ⟨1578226160635274533486273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8417206190054797511926789 1578226160635274533486273)
          ·
            refine ⟨1183669620476455900114705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578226160635274533486273 1183669620476455900114705)
            ·
              refine ⟨887752215357341925086029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1183669620476455900114705 887752215357341925086029)
              ·
                refine ⟨332907080759003221907261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 887752215357341925086029 332907080759003221907261)
                ·
                  refine ⟨124840155284626208215223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 332907080759003221907261 124840155284626208215223)
                  ·
                    rfl

theorem cell21_547032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 3].length) (baseStart_547032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547032 prefixEnd_547032 := by exact prefixLift 547032
  have htrace : WordTrace (prefixWord ++ tailWord_547032) baseStart_547032 baseEnd_547032 := by
    simpa [prefixWord, tailWord_547032, baseEnd_547032] using wordTrace_append hprefix tailTrace_547032
  have hstable : (prefixWord ++ tailWord_547032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547032).length < 2 ^ (prefixWord ++ tailWord_547032).sum := by decide
  have hdescent : baseEnd_547032 < baseStart_547032 := by decide
  rcases family_descends (prefixWord ++ tailWord_547032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547122 : List Nat := [3, 2, 1, 1, 5, 1, 1, 3, 4]
def baseStart_547122 : Nat := 118140960795 + 547122 * 2 ^ 59
def prefixEnd_547122 : Nat := 4983230072969 + 3 ^ 40 * 547122 * 2
def baseEnd_547122 : Nat := 124860694510806051715039

theorem tailTrace_547122 : CollatzResearch.WordTrace tailWord_547122 prefixEnd_547122 124860694510806051715039 := by
  unfold tailWord_547122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988794680969477460872905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13303452482585273228994413 4988794680969477460872905)
  ·
    refine ⟨3741596010727108095654679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4988794680969477460872905 3741596010727108095654679)
    ·
      refine ⟨5612394016090662143482019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3741596010727108095654679 5612394016090662143482019)
      ·
        refine ⟨8418591024135993215223029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5612394016090662143482019 8418591024135993215223029)
        ·
          refine ⟨789242908512749363927159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8418591024135993215223029 789242908512749363927159)
          ·
            refine ⟨1183864362769124045890739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 789242908512749363927159 1183864362769124045890739)
            ·
              refine ⟨1775796544153686068836109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183864362769124045890739 1775796544153686068836109)
              ·
                refine ⟨665923704057632275813541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775796544153686068836109 665923704057632275813541)
                ·
                  refine ⟨124860694510806051715039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665923704057632275813541 124860694510806051715039)
                  ·
                    rfl

theorem cell21_547122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_547122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547122 prefixEnd_547122 := by exact prefixLift 547122
  have htrace : WordTrace (prefixWord ++ tailWord_547122) baseStart_547122 baseEnd_547122 := by
    simpa [prefixWord, tailWord_547122, baseEnd_547122] using wordTrace_append hprefix tailTrace_547122
  have hstable : (prefixWord ++ tailWord_547122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547122).length < 2 ^ (prefixWord ++ tailWord_547122).sum := by decide
  have hdescent : baseEnd_547122 < baseStart_547122 := by decide
  rcases family_descends (prefixWord ++ tailWord_547122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547181 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 4]
def baseStart_547181 : Nat := 118140960795 + 547181 * 2 ^ 59
def prefixEnd_547181 : Nat := 4983230072969 + 3 ^ 40 * 547181 * 2
def baseEnd_547181 : Nat := 124874159114635060231585

theorem tailTrace_547181 : CollatzResearch.WordTrace tailWord_547181 prefixEnd_547181 124874159114635060231585 := by
  unfold tailWord_547181
  simp only [CollatzResearch.WordTrace]
  refine ⟨19957330630664162919889397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13304887087109441946592931 19957330630664162919889397)
  ·
    refine ⟨1870999746624765273739631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19957330630664162919889397 1870999746624765273739631)
    ·
      refine ⟨2806499619937147910609447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870999746624765273739631 2806499619937147910609447)
      ·
        refine ⟨4209749429905721865914171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2806499619937147910609447 4209749429905721865914171)
        ·
          refine ⟨6314624144858582798871257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209749429905721865914171 6314624144858582798871257)
          ·
            refine ⟨4735968108643937099153443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6314624144858582798871257 4735968108643937099153443)
            ·
              refine ⟨7103952162965905648730165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4735968108643937099153443 7103952162965905648730165)
              ·
                refine ⟨665995515278053654568453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7103952162965905648730165 665995515278053654568453)
                ·
                  refine ⟨124874159114635060231585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 665995515278053654568453 124874159114635060231585)
                  ·
                    rfl

theorem cell21_547181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_547181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547181 prefixEnd_547181 := by exact prefixLift 547181
  have htrace : WordTrace (prefixWord ++ tailWord_547181) baseStart_547181 baseEnd_547181 := by
    simpa [prefixWord, tailWord_547181, baseEnd_547181] using wordTrace_append hprefix tailTrace_547181
  have hstable : (prefixWord ++ tailWord_547181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547181).length < 2 ^ (prefixWord ++ tailWord_547181).sum := by decide
  have hdescent : baseEnd_547181 < baseStart_547181 := by decide
  rcases family_descends (prefixWord ++ tailWord_547181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547226 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_547226 : Nat := 118140960795 + 547226 * 2 ^ 59
def prefixEnd_547226 : Nat := 4983230072969 + 3 ^ 40 * 547226 * 2
def baseEnd_547226 : Nat := 124884428727724981981493

theorem tailTrace_547226 : CollatzResearch.WordTrace tailWord_547226 prefixEnd_547226 124884428727724981981493 := by
  unfold tailWord_547226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4989742978875283901319383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13305981277000757070185021 4989742978875283901319383)
  ·
    refine ⟨7484614468312925851979075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4989742978875283901319383 7484614468312925851979075)
    ·
      refine ⟨11226921702469388777968613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7484614468312925851979075 11226921702469388777968613)
      ·
        refine ⟨2105047819213010395869115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11226921702469388777968613 2105047819213010395869115)
        ·
          refine ⟨3157571728819515593803673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105047819213010395869115 3157571728819515593803673)
          ·
            refine ⟨2368178796614636695352755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157571728819515593803673 2368178796614636695352755)
            ·
              refine ⟨3552268194921955043029133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368178796614636695352755 3552268194921955043029133)
              ·
                refine ⟨1332100573095733141135925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3552268194921955043029133 1332100573095733141135925)
                ·
                  refine ⟨124884428727724981981493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1332100573095733141135925 124884428727724981981493)
                  ·
                    rfl

theorem cell21_547226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_547226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547226 prefixEnd_547226 := by exact prefixLift 547226
  have htrace : WordTrace (prefixWord ++ tailWord_547226) baseStart_547226 baseEnd_547226 := by
    simpa [prefixWord, tailWord_547226, baseEnd_547226] using wordTrace_append hprefix tailTrace_547226
  have hstable : (prefixWord ++ tailWord_547226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547226).length < 2 ^ (prefixWord ++ tailWord_547226).sum := by decide
  have hdescent : baseEnd_547226 < baseStart_547226 := by decide
  rcases family_descends (prefixWord ++ tailWord_547226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547260 : List Nat := [2, 2, 2, 4, 1, 1, 3, 3, 3]
def baseStart_547260 : Nat := 118140960795 + 547260 * 2 ^ 59
def prefixEnd_547260 : Nat := 4983230072969 + 3 ^ 40 * 547260 * 2
def baseEnd_547260 : Nat := 124892187990948478414757

theorem tailTrace_547260 : CollatzResearch.WordTrace tailWord_547260 prefixEnd_547260 124892187990948478414757 := by
  unfold tailWord_547260
  simp only [CollatzResearch.WordTrace]
  refine ⟨9980105998688979706007617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13306807998251972941343489 9980105998688979706007617)
  ·
    refine ⟨7485079499016734779505713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9980105998688979706007617 7485079499016734779505713)
    ·
      refine ⟨5613809624262551084629285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7485079499016734779505713 5613809624262551084629285)
      ·
        refine ⟨1052589304549228328367991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5613809624262551084629285 1052589304549228328367991)
        ·
          refine ⟨1578883956823842492551987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1052589304549228328367991 1578883956823842492551987)
          ·
            refine ⟨2368325935235763738827981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1578883956823842492551987 2368325935235763738827981)
            ·
              refine ⟨888122225713411402060493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2368325935235763738827981 888122225713411402060493)
              ·
                refine ⟨333045834642529275772685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888122225713411402060493 333045834642529275772685)
                ·
                  refine ⟨124892187990948478414757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333045834642529275772685 124892187990948478414757)
                  ·
                    rfl

theorem cell21_547260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_547260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547260 prefixEnd_547260 := by exact prefixLift 547260
  have htrace : WordTrace (prefixWord ++ tailWord_547260) baseStart_547260 baseEnd_547260 := by
    simpa [prefixWord, tailWord_547260, baseEnd_547260] using wordTrace_append hprefix tailTrace_547260
  have hstable : (prefixWord ++ tailWord_547260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547260).length < 2 ^ (prefixWord ++ tailWord_547260).sum := by decide
  have hdescent : baseEnd_547260 < baseStart_547260 := by decide
  rcases family_descends (prefixWord ++ tailWord_547260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547271 : List Nat := [1, 1, 4, 1, 1, 6, 7]
def baseStart_547271 : Nat := 118140960795 + 547271 * 2 ^ 59
def prefixEnd_547271 : Nat := 4983230072969 + 3 ^ 40 * 547271 * 2
def baseEnd_547271 : Nat := 13877188704534989303489

theorem tailTrace_547271 : CollatzResearch.WordTrace tailWord_547271 prefixEnd_547271 13877188704534989303489 := by
  unfold tailWord_547271
  simp only [CollatzResearch.WordTrace]
  refine ⟨19960613200338108290665667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13307075466892072193777111 19960613200338108290665667)
  ·
    refine ⟨29940919800507162435998501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19960613200338108290665667 29940919800507162435998501)
    ·
      refine ⟨5613922462595092956749719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29940919800507162435998501 5613922462595092956749719)
      ·
        refine ⟨8420883693892639435124579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613922462595092956749719 8420883693892639435124579)
        ·
          refine ⟨12631325540838959152686869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8420883693892639435124579 12631325540838959152686869)
          ·
            refine ⟨592093384726826210282197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12631325540838959152686869 592093384726826210282197)
            ·
              refine ⟨13877188704534989303489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 592093384726826210282197 13877188704534989303489)
              ·
                rfl

theorem cell21_547271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 7].length) (baseStart_547271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547271 prefixEnd_547271 := by exact prefixLift 547271
  have htrace : WordTrace (prefixWord ++ tailWord_547271) baseStart_547271 baseEnd_547271 := by
    simpa [prefixWord, tailWord_547271, baseEnd_547271] using wordTrace_append hprefix tailTrace_547271
  have hstable : (prefixWord ++ tailWord_547271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547271).length < 2 ^ (prefixWord ++ tailWord_547271).sum := by decide
  have hdescent : baseEnd_547271 < baseStart_547271 := by decide
  rcases family_descends (prefixWord ++ tailWord_547271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547429 : List Nat := [1, 3, 1, 3, 5, 1, 1, 3, 3]
def baseStart_547429 : Nat := 118140960795 + 547429 * 2 ^ 59
def prefixEnd_547429 : Nat := 4983230072969 + 3 ^ 40 * 547429 * 2
def baseEnd_547429 : Nat := 124930756093441740097745

theorem tailTrace_547429 : CollatzResearch.WordTrace tailWord_547429 prefixEnd_547429 124930756093441740097745 := by
  unfold tailWord_547429
  simp only [CollatzResearch.WordTrace]
  refine ⟨19966375933765701274917341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13310917289177134183278227 19966375933765701274917341)
  ·
    refine ⟨7487390975162137978094003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19966375933765701274917341 7487390975162137978094003)
    ·
      refine ⟨11231086462743206967141005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7487390975162137978094003 11231086462743206967141005)
      ·
        refine ⟨4211657423528702612677877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11231086462743206967141005 4211657423528702612677877)
        ·
          refine ⟨394842883455815869938551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4211657423528702612677877 394842883455815869938551)
          ·
            refine ⟨592264325183723804907827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394842883455815869938551 592264325183723804907827)
            ·
              refine ⟨888396487775585707361741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592264325183723804907827 888396487775585707361741)
              ·
                refine ⟨333148682915844640260653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888396487775585707361741 333148682915844640260653)
                ·
                  refine ⟨124930756093441740097745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333148682915844640260653 124930756093441740097745)
                  ·
                    rfl

theorem cell21_547429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 3, 3].length) (baseStart_547429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547429 prefixEnd_547429 := by exact prefixLift 547429
  have htrace : WordTrace (prefixWord ++ tailWord_547429) baseStart_547429 baseEnd_547429 := by
    simpa [prefixWord, tailWord_547429, baseEnd_547429] using wordTrace_append hprefix tailTrace_547429
  have hstable : (prefixWord ++ tailWord_547429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547429).length < 2 ^ (prefixWord ++ tailWord_547429).sum := by decide
  have hdescent : baseEnd_547429 < baseStart_547429 := by decide
  rcases family_descends (prefixWord ++ tailWord_547429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547440 : List Nat := [2, 1, 1, 1, 8, 1, 7]
def baseStart_547440 : Nat := 118140960795 + 547440 * 2 ^ 59
def prefixEnd_547440 : Nat := 4983230072969 + 3 ^ 40 * 547440 * 2
def baseEnd_547440 : Nat := 13881474049256462823821

theorem tailTrace_547440 : CollatzResearch.WordTrace tailWord_547440 prefixEnd_547440 13881474049256462823821 := by
  unfold tailWord_547440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9983388568362925076783887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13311184757817233435711849 9983388568362925076783887)
  ·
    refine ⟨14975082852544387615175831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9983388568362925076783887 14975082852544387615175831)
    ·
      refine ⟨22462624278816581422763747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14975082852544387615175831 22462624278816581422763747)
      ·
        refine ⟨33693936418224872134145621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22462624278816581422763747 33693936418224872134145621)
        ·
          refine ⟨394850817401072720322019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 33693936418224872134145621 394850817401072720322019)
          ·
            refine ⟨592276226101609080483029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394850817401072720322019 592276226101609080483029)
            ·
              refine ⟨13881474049256462823821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 592276226101609080483029 13881474049256462823821)
              ·
                rfl

theorem cell21_547440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 7].length) (baseStart_547440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547440 prefixEnd_547440 := by exact prefixLift 547440
  have htrace : WordTrace (prefixWord ++ tailWord_547440) baseStart_547440 baseEnd_547440 := by
    simpa [prefixWord, tailWord_547440, baseEnd_547440] using wordTrace_append hprefix tailTrace_547440
  have hstable : (prefixWord ++ tailWord_547440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547440).length < 2 ^ (prefixWord ++ tailWord_547440).sum := by decide
  have hdescent : baseEnd_547440 < baseStart_547440 := by decide
  rcases family_descends (prefixWord ++ tailWord_547440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547502 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_547502 : Nat := 118140960795 + 547502 * 2 ^ 59
def prefixEnd_547502 : Nat := 4983230072969 + 3 ^ 40 * 547502 * 2
def baseEnd_547502 : Nat := 124947415688009835380929

theorem tailTrace_547502 : CollatzResearch.WordTrace tailWord_547502 prefixEnd_547502 124947415688009835380929 := by
  unfold tailWord_547502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496129807812654342790595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13312692308334156494883173 2496129807812654342790595)
  ·
    refine ⟨3744194711718981514185893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2496129807812654342790595 3744194711718981514185893)
    ·
      refine ⟨702036508447309033909855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3744194711718981514185893 702036508447309033909855)
      ·
        refine ⟨1053054762670963550864783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702036508447309033909855 1053054762670963550864783)
        ·
          refine ⟨1579582144006445326297175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053054762670963550864783 1579582144006445326297175)
          ·
            refine ⟨2369373216009667989445763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579582144006445326297175 2369373216009667989445763)
            ·
              refine ⟨3554059824014501984168645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369373216009667989445763 3554059824014501984168645)
              ·
                refine ⟨666386217002719122031621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3554059824014501984168645 666386217002719122031621)
                ·
                  refine ⟨124947415688009835380929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666386217002719122031621 124947415688009835380929)
                  ·
                    rfl

theorem cell21_547502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_547502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547502 prefixEnd_547502 := by exact prefixLift 547502
  have htrace : WordTrace (prefixWord ++ tailWord_547502) baseStart_547502 baseEnd_547502 := by
    simpa [prefixWord, tailWord_547502, baseEnd_547502] using wordTrace_append hprefix tailTrace_547502
  have hstable : (prefixWord ++ tailWord_547502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547502).length < 2 ^ (prefixWord ++ tailWord_547502).sum := by decide
  have hdescent : baseEnd_547502 < baseStart_547502 := by decide
  rcases family_descends (prefixWord ++ tailWord_547502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547513 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 5]
def baseStart_547513 : Nat := 118140960795 + 547513 * 2 ^ 59
def prefixEnd_547513 : Nat := 4983230072969 + 3 ^ 40 * 547513 * 2
def baseEnd_547513 : Nat := 124949926037876260697573

theorem tailTrace_547513 : CollatzResearch.WordTrace tailWord_547513 prefixEnd_547513 124949926037876260697573 := by
  unfold tailWord_547513
  simp only [CollatzResearch.WordTrace]
  refine ⟨19969439665461383620975193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13312959776974255747316795 19969439665461383620975193)
  ·
    refine ⟨14977079749096037715731395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19969439665461383620975193 14977079749096037715731395)
    ·
      refine ⟨22465619623644056573597093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14977079749096037715731395 22465619623644056573597093)
      ·
        refine ⟨4212303679433260607549455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22465619623644056573597093 4212303679433260607549455)
        ·
          refine ⟨6318455519149890911324183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4212303679433260607549455 6318455519149890911324183)
          ·
            refine ⟨9477683278724836366986275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6318455519149890911324183 9477683278724836366986275)
            ·
              refine ⟨14216524918087254550479413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9477683278724836366986275 14216524918087254550479413)
              ·
                refine ⟨1332799211070680114107445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14216524918087254550479413 1332799211070680114107445)
                ·
                  refine ⟨124949926037876260697573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1332799211070680114107445 124949926037876260697573)
                  ·
                    rfl

theorem cell21_547513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_547513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547513 prefixEnd_547513 := by exact prefixLift 547513
  have htrace : WordTrace (prefixWord ++ tailWord_547513) baseStart_547513 baseEnd_547513 := by
    simpa [prefixWord, tailWord_547513, baseEnd_547513] using wordTrace_append hprefix tailTrace_547513
  have hstable : (prefixWord ++ tailWord_547513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547513).length < 2 ^ (prefixWord ++ tailWord_547513).sum := by decide
  have hdescent : baseEnd_547513 < baseStart_547513 := by decide
  rcases family_descends (prefixWord ++ tailWord_547513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547530 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 5]
def baseStart_547530 : Nat := 118140960795 + 547530 * 2 ^ 59
def prefixEnd_547530 : Nat := 4983230072969 + 3 ^ 40 * 547530 * 2
def baseEnd_547530 : Nat := 124953805669488008914205

theorem tailTrace_547530 : CollatzResearch.WordTrace tailWord_547530 prefixEnd_547530 124953805669488008914205 := by
  unfold tailWord_547530
  simp only [CollatzResearch.WordTrace]
  refine ⟨4992514926599948881086011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13313373137599863682896029 4992514926599948881086011)
  ·
    refine ⟨7488772389899923321629017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4992514926599948881086011 7488772389899923321629017)
    ·
      refine ⟨5616579292424942491221763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7488772389899923321629017 5616579292424942491221763)
      ·
        refine ⟨8424868938637413736832645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5616579292424942491221763 8424868938637413736832645)
        ·
          refine ⟨1579662925994515075656121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8424868938637413736832645 1579662925994515075656121)
          ·
            refine ⟨1184747194495886306742091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579662925994515075656121 1184747194495886306742091)
            ·
              refine ⟨1777120791743829460113137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184747194495886306742091 1777120791743829460113137)
              ·
                refine ⟨1332840593807872095084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1777120791743829460113137 1332840593807872095084853)
                ·
                  refine ⟨124953805669488008914205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1332840593807872095084853 124953805669488008914205)
                  ·
                    rfl

theorem cell21_547530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 5].length) (baseStart_547530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547530 prefixEnd_547530 := by exact prefixLift 547530
  have htrace : WordTrace (prefixWord ++ tailWord_547530) baseStart_547530 baseEnd_547530 := by
    simpa [prefixWord, tailWord_547530, baseEnd_547530] using wordTrace_append hprefix tailTrace_547530
  have hstable : (prefixWord ++ tailWord_547530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547530).length < 2 ^ (prefixWord ++ tailWord_547530).sum := by decide
  have hdescent : baseEnd_547530 < baseStart_547530 := by decide
  rcases family_descends (prefixWord ++ tailWord_547530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547592 : List Nat := [2, 1, 3, 2, 2, 4, 2, 5]
def baseStart_547592 : Nat := 118140960795 + 547592 * 2 ^ 59
def prefixEnd_547592 : Nat := 4983230072969 + 3 ^ 40 * 547592 * 2
def baseEnd_547592 : Nat := 41655984971396559626915

theorem tailTrace_547592 : CollatzResearch.WordTrace tailWord_547592 prefixEnd_547592 41655984971396559626915 := by
  unfold tailWord_547592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9986160516087590056550515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13314880688116786742067353 9986160516087590056550515)
  ·
    refine ⟨14979240774131385084825773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9986160516087590056550515 14979240774131385084825773)
    ·
      refine ⟨5617215290299269406809665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14979240774131385084825773 5617215290299269406809665)
      ·
        refine ⟨4212911467724452055107249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5617215290299269406809665 4212911467724452055107249)
        ·
          refine ⟨3159683600793339041330437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4212911467724452055107249 3159683600793339041330437)
          ·
            refine ⟨592440675148751070249457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3159683600793339041330437 592440675148751070249457)
            ·
              refine ⟨444330506361563302687093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592440675148751070249457 444330506361563302687093)
              ·
                refine ⟨41655984971396559626915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 444330506361563302687093 41655984971396559626915)
                ·
                  rfl

theorem cell21_547592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_547592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547592 prefixEnd_547592 := by exact prefixLift 547592
  have htrace : WordTrace (prefixWord ++ tailWord_547592) baseStart_547592 baseEnd_547592 := by
    simpa [prefixWord, tailWord_547592, baseEnd_547592] using wordTrace_append hprefix tailTrace_547592
  have hstable : (prefixWord ++ tailWord_547592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547592).length < 2 ^ (prefixWord ++ tailWord_547592).sum := by decide
  have hdescent : baseEnd_547592 < baseStart_547592 := by decide
  rcases family_descends (prefixWord ++ tailWord_547592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547603 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 8]
def baseStart_547603 : Nat := 118140960795 + 547603 * 2 ^ 59
def prefixEnd_547603 : Nat := 4983230072969 + 3 ^ 40 * 547603 * 2
def baseEnd_547603 : Nat := 124970465264056104197389

theorem tailTrace_547603 : CollatzResearch.WordTrace tailWord_547603 prefixEnd_547603 124970465264056104197389 := by
  unfold tailWord_547603
  simp only [CollatzResearch.WordTrace]
  refine ⟨19972722235135328991751463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13315148156756885994500975 19972722235135328991751463)
  ·
    refine ⟨29959083352702993487627195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19972722235135328991751463 29959083352702993487627195)
    ·
      refine ⟨44938625029054490231440793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29959083352702993487627195 44938625029054490231440793)
      ·
        refine ⟨33703968771790867673580595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44938625029054490231440793 33703968771790867673580595)
        ·
          refine ⟨50555953157686301510370893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33703968771790867673580595 50555953157686301510370893)
          ·
            refine ⟨18958482434132363066389085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50555953157686301510370893 18958482434132363066389085)
            ·
              refine ⟨7109430912799636149895907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18958482434132363066389085 7109430912799636149895907)
              ·
                refine ⟨10664146369199454224843861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7109430912799636149895907 10664146369199454224843861)
                ·
                  refine ⟨124970465264056104197389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10664146369199454224843861 124970465264056104197389)
                  ·
                    rfl

theorem cell21_547603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 8].length) (baseStart_547603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547603 prefixEnd_547603 := by exact prefixLift 547603
  have htrace : WordTrace (prefixWord ++ tailWord_547603) baseStart_547603 baseEnd_547603 := by
    simpa [prefixWord, tailWord_547603, baseEnd_547603] using wordTrace_append hprefix tailTrace_547603
  have hstable : (prefixWord ++ tailWord_547603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547603).length < 2 ^ (prefixWord ++ tailWord_547603).sum := by decide
  have hdescent : baseEnd_547603 < baseStart_547603 := by decide
  rcases family_descends (prefixWord ++ tailWord_547603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547629 : List Nat := [1, 5, 3, 2, 2, 1, 2, 1, 4]
def baseStart_547629 : Nat := 118140960795 + 547629 * 2 ^ 59
def prefixEnd_547629 : Nat := 4983230072969 + 3 ^ 40 * 547629 * 2
def baseEnd_547629 : Nat := 124976398818285836764003

theorem tailTrace_547629 : CollatzResearch.WordTrace tailWord_547629 prefixEnd_547629 124976398818285836764003 := by
  unfold tailWord_547629
  simp only [CollatzResearch.WordTrace]
  refine ⟨19973670533041135432197941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13315780355360756954798627 19973670533041135432197941)
  ·
    refine ⟨1872531612472606446768557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19973670533041135432197941 1872531612472606446768557)
    ·
      refine ⟨702199354677227417538209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1872531612472606446768557 702199354677227417538209)
      ·
        refine ⟨526649516007920563153657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 702199354677227417538209 526649516007920563153657)
        ·
          refine ⟨394987137005940422365243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526649516007920563153657 394987137005940422365243)
          ·
            refine ⟨592480705508910633547865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394987137005940422365243 592480705508910633547865)
            ·
              refine ⟨444360529131682975160899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592480705508910633547865 444360529131682975160899)
              ·
                refine ⟨666540793697524462741349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444360529131682975160899 666540793697524462741349)
                ·
                  refine ⟨124976398818285836764003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666540793697524462741349 124976398818285836764003)
                  ·
                    rfl

theorem cell21_547629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_547629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547629 prefixEnd_547629 := by exact prefixLift 547629
  have htrace : WordTrace (prefixWord ++ tailWord_547629) baseStart_547629 baseEnd_547629 := by
    simpa [prefixWord, tailWord_547629, baseEnd_547629] using wordTrace_append hprefix tailTrace_547629
  have hstable : (prefixWord ++ tailWord_547629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547629).length < 2 ^ (prefixWord ++ tailWord_547629).sum := by decide
  have hdescent : baseEnd_547629 < baseStart_547629 := by decide
  rcases family_descends (prefixWord ++ tailWord_547629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547637 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 4]
def baseStart_547637 : Nat := 118140960795 + 547637 * 2 ^ 59
def prefixEnd_547637 : Nat := 4983230072969 + 3 ^ 40 * 547637 * 2
def baseEnd_547637 : Nat := 124978224527279600630653

theorem tailTrace_547637 : CollatzResearch.WordTrace tailWord_547637 prefixEnd_547637 124978224527279600630653 := by
  unfold tailWord_547637
  simp only [CollatzResearch.WordTrace]
  refine ⟨19973962317012152798489165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13315974878008101865659443 19973962317012152798489165)
  ·
    refine ⟨7490235868879557299433437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19973962317012152798489165 7490235868879557299433437)
    ·
      refine ⟨2808838450829833987287539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7490235868879557299433437 2808838450829833987287539)
      ·
        refine ⟨4213257676244750980931309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2808838450829833987287539 4213257676244750980931309)
        ·
          refine ⟨1579971628591781617849241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4213257676244750980931309 1579971628591781617849241)
          ·
            refine ⟨1184978721443836213386931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1579971628591781617849241 1184978721443836213386931)
            ·
              refine ⟨1777468082165754320080397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184978721443836213386931 1777468082165754320080397)
              ·
                refine ⟨666550530812157870030149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777468082165754320080397 666550530812157870030149)
                ·
                  refine ⟨124978224527279600630653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666550530812157870030149 124978224527279600630653)
                  ·
                    rfl

theorem cell21_547637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 4].length) (baseStart_547637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547637 prefixEnd_547637 := by exact prefixLift 547637
  have htrace : WordTrace (prefixWord ++ tailWord_547637) baseStart_547637 baseEnd_547637 := by
    simpa [prefixWord, tailWord_547637, baseEnd_547637] using wordTrace_append hprefix tailTrace_547637
  have hstable : (prefixWord ++ tailWord_547637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547637).length < 2 ^ (prefixWord ++ tailWord_547637).sum := by decide
  have hdescent : baseEnd_547637 < baseStart_547637 := by decide
  rcases family_descends (prefixWord ++ tailWord_547637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547696 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 4]
def baseStart_547696 : Nat := 118140960795 + 547696 * 2 ^ 59
def prefixEnd_547696 : Nat := 4983230072969 + 3 ^ 40 * 547696 * 2
def baseEnd_547696 : Nat := 124991689131108609147199

theorem tailTrace_547696 : CollatzResearch.WordTrace tailWord_547696 prefixEnd_547696 124991689131108609147199 := by
  unfold tailWord_547696
  simp only [CollatzResearch.WordTrace]
  refine ⟨9988057111899202937443471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13317409482532270583257961 9988057111899202937443471)
  ·
    refine ⟨14982085667848804406165207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9988057111899202937443471 14982085667848804406165207)
    ·
      refine ⟨22473128501773206609247811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14982085667848804406165207 22473128501773206609247811)
      ·
        refine ⟨33709692752659809913871717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22473128501773206609247811 33709692752659809913871717)
        ·
          refine ⟨6320567391123714358850947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33709692752659809913871717 6320567391123714358850947)
          ·
            refine ⟨9480851086685571538276421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6320567391123714358850947 9480851086685571538276421)
            ·
              refine ⟨1777659578753544663426829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9480851086685571538276421 1777659578753544663426829)
              ·
                refine ⟨666622342032579248785061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1777659578753544663426829 666622342032579248785061)
                ·
                  refine ⟨124991689131108609147199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666622342032579248785061 124991689131108609147199)
                  ·
                    rfl

theorem cell21_547696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_547696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547696 prefixEnd_547696 := by exact prefixLift 547696
  have htrace : WordTrace (prefixWord ++ tailWord_547696) baseStart_547696 baseEnd_547696 := by
    simpa [prefixWord, tailWord_547696, baseEnd_547696] using wordTrace_append hprefix tailTrace_547696
  have hstable : (prefixWord ++ tailWord_547696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547696).length < 2 ^ (prefixWord ++ tailWord_547696).sum := by decide
  have hdescent : baseEnd_547696 < baseStart_547696 := by decide
  rcases family_descends (prefixWord ++ tailWord_547696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547761 : List Nat := [1, 2, 2, 4, 4, 1, 2, 5]
def baseStart_547761 : Nat := 118140960795 + 547761 * 2 ^ 59
def prefixEnd_547761 : Nat := 4983230072969 + 3 ^ 40 * 547761 * 2
def baseEnd_547761 : Nat := 41668841005560980187911

theorem tailTrace_547761 : CollatzResearch.WordTrace tailWord_547761 prefixEnd_547761 41668841005560980187911 := by
  unfold tailWord_547761
  simp only [CollatzResearch.WordTrace]
  refine ⟨19978484968562921976003137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13318989979041947984002091 19978484968562921976003137)
  ·
    refine ⟨14983863726422191482002353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19978484968562921976003137 14983863726422191482002353)
    ·
      refine ⟨11237897794816643611501765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14983863726422191482002353 11237897794816643611501765)
      ·
        refine ⟨2107105836528120677156581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11237897794816643611501765 2107105836528120677156581)
        ·
          refine ⟨395082344349022626966859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2107105836528120677156581 395082344349022626966859)
          ·
            refine ⟨592623516523533940450289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395082344349022626966859 592623516523533940450289)
            ·
              refine ⟨444467637392650455337717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592623516523533940450289 444467637392650455337717)
              ·
                refine ⟨41668841005560980187911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 444467637392650455337717 41668841005560980187911)
                ·
                  rfl

theorem cell21_547761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 5].length) (baseStart_547761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547761 prefixEnd_547761 := by exact prefixLift 547761
  have htrace : WordTrace (prefixWord ++ tailWord_547761) baseStart_547761 baseEnd_547761 := by
    simpa [prefixWord, tailWord_547761, baseEnd_547761] using wordTrace_append hprefix tailTrace_547761
  have hstable : (prefixWord ++ tailWord_547761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547761).length < 2 ^ (prefixWord ++ tailWord_547761).sum := by decide
  have hdescent : baseEnd_547761 < baseStart_547761 := by decide
  rcases family_descends (prefixWord ++ tailWord_547761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547848 : List Nat := [2, 1, 3, 2, 1, 3, 1, 4, 4]
def baseStart_547848 : Nat := 118140960795 + 547848 * 2 ^ 59
def prefixEnd_547848 : Nat := 4983230072969 + 3 ^ 40 * 547848 * 2
def baseEnd_547848 : Nat := 125026377601990122613555

theorem tailTrace_547848 : CollatzResearch.WordTrace tailWord_547848 prefixEnd_547848 125026377601990122613555 := by
  unfold tailWord_547848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990829059623867917210099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13321105412831823889613465 9990829059623867917210099)
  ·
    refine ⟨14986243589435801875815149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9990829059623867917210099 14986243589435801875815149)
    ·
      refine ⟨5619841346038425703430681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14986243589435801875815149 5619841346038425703430681)
      ·
        refine ⟨4214881009528819277573011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5619841346038425703430681 4214881009528819277573011)
        ·
          refine ⟨6322321514293228916359517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214881009528819277573011 6322321514293228916359517)
          ·
            refine ⟨2370870567859960843634819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6322321514293228916359517 2370870567859960843634819)
            ·
              refine ⟨3556305851789941265452229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2370870567859960843634819 3556305851789941265452229)
              ·
                refine ⟨666807347210613987272293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3556305851789941265452229 666807347210613987272293)
                ·
                  refine ⟨125026377601990122613555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666807347210613987272293 125026377601990122613555)
                  ·
                    rfl

theorem cell21_547848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 4].length) (baseStart_547848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547848 prefixEnd_547848 := by exact prefixLift 547848
  have htrace : WordTrace (prefixWord ++ tailWord_547848) baseStart_547848 baseEnd_547848 := by
    simpa [prefixWord, tailWord_547848, baseEnd_547848] using wordTrace_append hprefix tailTrace_547848
  have hstable : (prefixWord ++ tailWord_547848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547848).length < 2 ^ (prefixWord ++ tailWord_547848).sum := by decide
  have hdescent : baseEnd_547848 < baseStart_547848 := by decide
  rcases family_descends (prefixWord ++ tailWord_547848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547851 : List Nat := [1, 1, 1, 1, 6, 2, 4, 2, 3]
def baseStart_547851 : Nat := 118140960795 + 547851 * 2 ^ 59
def prefixEnd_547851 : Nat := 4983230072969 + 3 ^ 40 * 547851 * 2
def baseEnd_547851 : Nat := 125027062242862784063549

theorem tailTrace_547851 : CollatzResearch.WordTrace tailWord_547851 prefixEnd_547851 125027062242862784063549 := by
  unfold tailWord_547851
  simp only [CollatzResearch.WordTrace]
  refine ⟨19981767538236867346779407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13321178358824578231186271 19981767538236867346779407)
  ·
    refine ⟨29972651307355301020169111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19981767538236867346779407 29972651307355301020169111)
    ·
      refine ⟨44958976961032951530253667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29972651307355301020169111 44958976961032951530253667)
      ·
        refine ⟨67438465441549427295380501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44958976961032951530253667 67438465441549427295380501)
        ·
          refine ⟨3161178067572629404470961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67438465441549427295380501 3161178067572629404470961)
          ·
            refine ⟨2370883550679472053353221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3161178067572629404470961 2370883550679472053353221)
            ·
              refine ⟨444540665752401010003729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2370883550679472053353221 444540665752401010003729)
              ·
                refine ⟨333405499314300757502797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444540665752401010003729 333405499314300757502797)
                ·
                  refine ⟨125027062242862784063549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333405499314300757502797 125027062242862784063549)
                  ·
                    rfl

theorem cell21_547851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 2, 3].length) (baseStart_547851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547851 prefixEnd_547851 := by exact prefixLift 547851
  have htrace : WordTrace (prefixWord ++ tailWord_547851) baseStart_547851 baseEnd_547851 := by
    simpa [prefixWord, tailWord_547851, baseEnd_547851] using wordTrace_append hprefix tailTrace_547851
  have hstable : (prefixWord ++ tailWord_547851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547851).length < 2 ^ (prefixWord ++ tailWord_547851).sum := by decide
  have hdescent : baseEnd_547851 < baseStart_547851 := by decide
  rcases family_descends (prefixWord ++ tailWord_547851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547907 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 6]
def baseStart_547907 : Nat := 118140960795 + 547907 * 2 ^ 59
def prefixEnd_547907 : Nat := 4983230072969 + 3 ^ 40 * 547907 * 2
def baseEnd_547907 : Nat := 125039842205819131130101

theorem tailTrace_547907 : CollatzResearch.WordTrace tailWord_547907 prefixEnd_547907 125039842205819131130101 := by
  unfold tailWord_547907
  simp only [CollatzResearch.WordTrace]
  refine ⟨19983810026033988910817975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13322540017355992607211983 19983810026033988910817975)
  ·
    refine ⟨29975715039050983366226963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19983810026033988910817975 29975715039050983366226963)
    ·
      refine ⟨44963572558576475049340445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29975715039050983366226963 44963572558576475049340445)
      ·
        refine ⟨16861339709466178143502667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44963572558576475049340445 16861339709466178143502667)
        ·
          refine ⟨25292009564199267215254001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16861339709466178143502667 25292009564199267215254001)
          ·
            refine ⟨18969007173149450411440501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25292009564199267215254001 18969007173149450411440501)
            ·
              refine ⟨1778344422482760976072547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18969007173149450411440501 1778344422482760976072547)
              ·
                refine ⟨2667516633724141464108821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1778344422482760976072547 2667516633724141464108821)
                ·
                  refine ⟨125039842205819131130101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2667516633724141464108821 125039842205819131130101)
                  ·
                    rfl

theorem cell21_547907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 6].length) (baseStart_547907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547907 prefixEnd_547907 := by exact prefixLift 547907
  have htrace : WordTrace (prefixWord ++ tailWord_547907) baseStart_547907 baseEnd_547907 := by
    simpa [prefixWord, tailWord_547907, baseEnd_547907] using wordTrace_append hprefix tailTrace_547907
  have hstable : (prefixWord ++ tailWord_547907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547907).length < 2 ^ (prefixWord ++ tailWord_547907).sum := by decide
  have hdescent : baseEnd_547907 < baseStart_547907 := by decide
  rcases family_descends (prefixWord ++ tailWord_547907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_547924 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 4]
def baseStart_547924 : Nat := 118140960795 + 547924 * 2 ^ 59
def prefixEnd_547924 : Nat := 4983230072969 + 3 ^ 40 * 547924 * 2
def baseEnd_547924 : Nat := 125043721837430879346733

theorem tailTrace_547924 : CollatzResearch.WordTrace tailWord_547924 prefixEnd_547924 125043721837430879346733 := by
  unfold tailWord_547924
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992215033486200407093413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13322953377981600542791217 9992215033486200407093413)
  ·
    refine ⟨1873540318778662576330015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9992215033486200407093413 1873540318778662576330015)
    ·
      refine ⟨2810310478167993864495023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873540318778662576330015 2810310478167993864495023)
      ·
        refine ⟨4215465717251990796742535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810310478167993864495023 4215465717251990796742535)
        ·
          refine ⟨6323198575877986195113803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4215465717251990796742535 6323198575877986195113803)
          ·
            refine ⟨9484797863816979292670705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323198575877986195113803 9484797863816979292670705)
            ·
              refine ⟨7113598397862734469503029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9484797863816979292670705 7113598397862734469503029)
              ·
                refine ⟨666899849799631356515909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7113598397862734469503029 666899849799631356515909)
                ·
                  refine ⟨125043721837430879346733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 666899849799631356515909 125043721837430879346733)
                  ·
                    rfl

theorem cell21_547924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_547924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_547924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_547924 prefixEnd_547924 := by exact prefixLift 547924
  have htrace : WordTrace (prefixWord ++ tailWord_547924) baseStart_547924 baseEnd_547924 := by
    simpa [prefixWord, tailWord_547924, baseEnd_547924] using wordTrace_append hprefix tailTrace_547924
  have hstable : (prefixWord ++ tailWord_547924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_547924).length < 2 ^ (prefixWord ++ tailWord_547924).sum := by decide
  have hdescent : baseEnd_547924 < baseStart_547924 := by decide
  rcases family_descends (prefixWord ++ tailWord_547924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548014 : List Nat := [4, 1, 4, 12]
def baseStart_548014 : Nat := 118140960795 + 548014 * 2 ^ 59
def prefixEnd_548014 : Nat := 4983230072969 + 3 ^ 40 * 548014 * 2
def baseEnd_548014 : Nat := 514667741002513262743

theorem tailTrace_548014 : CollatzResearch.WordTrace tailWord_548014 prefixEnd_548014 514667741002513262743 := by
  unfold tailWord_548014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498464079580793273120387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13325141757764230789975397 2498464079580793273120387)
  ·
    refine ⟨3747696119371189909680581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2498464079580793273120387 3747696119371189909680581)
    ·
      refine ⟨702693022382098108065109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3747696119371189909680581 702693022382098108065109)
      ·
        refine ⟨514667741002513262743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 702693022382098108065109 514667741002513262743)
        ·
          rfl

theorem cell21_548014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 12].length) (baseStart_548014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548014 prefixEnd_548014 := by exact prefixLift 548014
  have htrace : WordTrace (prefixWord ++ tailWord_548014) baseStart_548014 baseEnd_548014 := by
    simpa [prefixWord, tailWord_548014, baseEnd_548014] using wordTrace_append hprefix tailTrace_548014
  have hstable : (prefixWord ++ tailWord_548014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548014).length < 2 ^ (prefixWord ++ tailWord_548014).sum := by decide
  have hdescent : baseEnd_548014 < baseStart_548014 := by decide
  rcases family_descends (prefixWord ++ tailWord_548014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548017 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 4]
def baseStart_548017 : Nat := 118140960795 + 548017 * 2 ^ 59
def prefixEnd_548017 : Nat := 4983230072969 + 3 ^ 40 * 548017 * 2
def baseEnd_548017 : Nat := 125064945704483384296543

theorem tailTrace_548017 : CollatzResearch.WordTrace tailWord_548017 prefixEnd_548017 125064945704483384296543 := by
  unfold tailWord_548017
  simp only [CollatzResearch.WordTrace]
  refine ⟨19987822055635477697322305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13325214703756985131548203 19987822055635477697322305)
  ·
    refine ⟨14990866541726608272991729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19987822055635477697322305 14990866541726608272991729)
    ·
      refine ⟨11243149906294956204743797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14990866541726608272991729 11243149906294956204743797)
      ·
        refine ⟨1054045303715152144194731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11243149906294956204743797 1054045303715152144194731)
        ·
          refine ⟨1581067955572728216292097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054045303715152144194731 1581067955572728216292097)
          ·
            refine ⟨1185800966679546162219073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1581067955572728216292097 1185800966679546162219073)
            ·
              refine ⟨889350725009659621664305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1185800966679546162219073 889350725009659621664305)
              ·
                refine ⟨667013043757244716248229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889350725009659621664305 667013043757244716248229)
                ·
                  refine ⟨125064945704483384296543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667013043757244716248229 125064945704483384296543)
                  ·
                    rfl

theorem cell21_548017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 4].length) (baseStart_548017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548017 prefixEnd_548017 := by exact prefixLift 548017
  have htrace : WordTrace (prefixWord ++ tailWord_548017) baseStart_548017 baseEnd_548017 := by
    simpa [prefixWord, tailWord_548017, baseEnd_548017] using wordTrace_append hprefix tailTrace_548017
  have hstable : (prefixWord ++ tailWord_548017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548017).length < 2 ^ (prefixWord ++ tailWord_548017).sum := by decide
  have hdescent : baseEnd_548017 < baseStart_548017 := by decide
  rcases family_descends (prefixWord ++ tailWord_548017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548076 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 4]
def baseStart_548076 : Nat := 118140960795 + 548076 * 2 ^ 59
def prefixEnd_548076 : Nat := 4983230072969 + 3 ^ 40 * 548076 * 2
def baseEnd_548076 : Nat := 125078410308312392813089

theorem tailTrace_548076 : CollatzResearch.WordTrace tailWord_548076 prefixEnd_548076 125078410308312392813089 := by
  unfold tailWord_548076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994986981210865386860041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13326649308281153849146721 9994986981210865386860041)
  ·
    refine ⟨7496240235908149040145031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9994986981210865386860041 7496240235908149040145031)
    ·
      refine ⟨11244360353862223560217547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7496240235908149040145031 11244360353862223560217547)
      ·
        refine ⟨16866540530793335340326321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244360353862223560217547 16866540530793335340326321)
        ·
          refine ⟨12649905398095001505244741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16866540530793335340326321 12649905398095001505244741)
          ·
            refine ⟨2371857262142812782233389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12649905398095001505244741 2371857262142812782233389)
            ·
              refine ⟨889446473303554793337521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371857262142812782233389 889446473303554793337521)
              ·
                refine ⟨667084854977666095003141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889446473303554793337521 667084854977666095003141)
                ·
                  refine ⟨125078410308312392813089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667084854977666095003141 125078410308312392813089)
                  ·
                    rfl

theorem cell21_548076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_548076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548076 prefixEnd_548076 := by exact prefixLift 548076
  have htrace : WordTrace (prefixWord ++ tailWord_548076) baseStart_548076 baseEnd_548076 := by
    simpa [prefixWord, tailWord_548076, baseEnd_548076] using wordTrace_append hprefix tailTrace_548076
  have hstable : (prefixWord ++ tailWord_548076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548076).length < 2 ^ (prefixWord ++ tailWord_548076).sum := by decide
  have hdescent : baseEnd_548076 < baseStart_548076 := by decide
  rcases family_descends (prefixWord ++ tailWord_548076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548107 : List Nat := [1, 1, 1, 1, 5, 5, 2, 5]
def baseStart_548107 : Nat := 118140960795 + 548107 * 2 ^ 59
def prefixEnd_548107 : Nat := 4983230072969 + 3 ^ 40 * 548107 * 2
def baseEnd_548107 : Nat := 41695161643554409265453

theorem tailTrace_548107 : CollatzResearch.WordTrace tailWord_548107 prefixEnd_548107 41695161643554409265453 := by
  unfold tailWord_548107
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991104625309423068098575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13327403083539615378732383 19991104625309423068098575)
  ·
    refine ⟨29986656937964134602147863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19991104625309423068098575 29986656937964134602147863)
    ·
      refine ⟨44979985406946201903221795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29986656937964134602147863 44979985406946201903221795)
      ·
        refine ⟨67469978110419302854832693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44979985406946201903221795 67469978110419302854832693)
        ·
          refine ⟨6325310447851809642640565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67469978110419302854832693 6325310447851809642640565)
          ·
            refine ⟨592997854486107153997553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6325310447851809642640565 592997854486107153997553)
            ·
              refine ⟨444748390864580365498165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592997854486107153997553 444748390864580365498165)
              ·
                refine ⟨41695161643554409265453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 444748390864580365498165 41695161643554409265453)
                ·
                  rfl

theorem cell21_548107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 5].length) (baseStart_548107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548107 prefixEnd_548107 := by exact prefixLift 548107
  have htrace : WordTrace (prefixWord ++ tailWord_548107) baseStart_548107 baseEnd_548107 := by
    simpa [prefixWord, tailWord_548107, baseEnd_548107] using wordTrace_append hprefix tailTrace_548107
  have hstable : (prefixWord ++ tailWord_548107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548107).length < 2 ^ (prefixWord ++ tailWord_548107).sum := by decide
  have hdescent : baseEnd_548107 < baseStart_548107 := by decide
  rcases family_descends (prefixWord ++ tailWord_548107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548138 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_548138 : Nat := 118140960795 + 548138 * 2 ^ 59
def prefixEnd_548138 : Nat := 4983230072969 + 3 ^ 40 * 548138 * 2
def baseEnd_548138 : Nat := 125092559553014062779629

theorem tailTrace_548138 : CollatzResearch.WordTrace tailWord_548138 prefixEnd_548138 125092559553014062779629 := by
  unfold tailWord_548138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998058822049278840619267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13328156858798076908318045 4998058822049278840619267)
  ·
    refine ⟨7497088233073918260928901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4998058822049278840619267 7497088233073918260928901)
    ·
      refine ⟨1405704043701359673924169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7497088233073918260928901 1405704043701359673924169)
      ·
        refine ⟨1054278032776019755443127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1405704043701359673924169 1054278032776019755443127)
        ·
          refine ⟨1581417049164029633164691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054278032776019755443127 1581417049164029633164691)
          ·
            refine ⟨2372125573746044449747037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581417049164029633164691 2372125573746044449747037)
            ·
              refine ⟨889547090154766668655139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2372125573746044449747037 889547090154766668655139)
              ·
                refine ⟨1334320635232150002982709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889547090154766668655139 1334320635232150002982709)
                ·
                  refine ⟨125092559553014062779629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1334320635232150002982709 125092559553014062779629)
                  ·
                    rfl

theorem cell21_548138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_548138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548138 prefixEnd_548138 := by exact prefixLift 548138
  have htrace : WordTrace (prefixWord ++ tailWord_548138) baseStart_548138 baseEnd_548138 := by
    simpa [prefixWord, tailWord_548138, baseEnd_548138] using wordTrace_append hprefix tailTrace_548138
  have hstable : (prefixWord ++ tailWord_548138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548138).length < 2 ^ (prefixWord ++ tailWord_548138).sum := by decide
  have hdescent : baseEnd_548138 < baseStart_548138 := by decide
  rcases family_descends (prefixWord ++ tailWord_548138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548189 : List Nat := [1, 4, 5, 1, 1, 1, 1, 4, 3]
def baseStart_548189 : Nat := 118140960795 + 548189 * 2 ^ 59
def prefixEnd_548189 : Nat := 4983230072969 + 3 ^ 40 * 548189 * 2
def baseEnd_548189 : Nat := 125104198447849307429525

theorem tailTrace_548189 : CollatzResearch.WordTrace tailWord_548189 prefixEnd_548189 125104198447849307429525 := by
  unfold tailWord_548189
  simp only [CollatzResearch.WordTrace]
  refine ⟨19994095411012351072583621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13329396940674900715055747 19994095411012351072583621)
  ·
    refine ⟨3748892889564815826109429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19994095411012351072583621 3748892889564815826109429)
    ·
      refine ⟨351458708396701483697759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3748892889564815826109429 351458708396701483697759)
      ·
        refine ⟨527188062595052225546639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351458708396701483697759 527188062595052225546639)
        ·
          refine ⟨790782093892578338319959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527188062595052225546639 790782093892578338319959)
          ·
            refine ⟨1186173140838867507479939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790782093892578338319959 1186173140838867507479939)
            ·
              refine ⟨1779259711258301261219909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186173140838867507479939 1779259711258301261219909)
              ·
                refine ⟨333611195860931486478733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1779259711258301261219909 333611195860931486478733)
                ·
                  refine ⟨125104198447849307429525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333611195860931486478733 125104198447849307429525)
                  ·
                    rfl

theorem cell21_548189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_548189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548189 prefixEnd_548189 := by exact prefixLift 548189
  have htrace : WordTrace (prefixWord ++ tailWord_548189) baseStart_548189 baseEnd_548189 := by
    simpa [prefixWord, tailWord_548189, baseEnd_548189] using wordTrace_append hprefix tailTrace_548189
  have hstable : (prefixWord ++ tailWord_548189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548189).length < 2 ^ (prefixWord ++ tailWord_548189).sum := by decide
  have hdescent : baseEnd_548189 < baseStart_548189 := by decide
  rcases family_descends (prefixWord ++ tailWord_548189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548200 : List Nat := [2, 1, 4, 2, 4, 1, 1, 6]
def baseStart_548200 : Nat := 118140960795 + 548200 * 2 ^ 59
def prefixEnd_548200 : Nat := 4983230072969 + 3 ^ 40 * 548200 * 2
def baseEnd_548200 : Nat := 41702236265905244248723

theorem tailTrace_548200 : CollatzResearch.WordTrace tailWord_548200 prefixEnd_548200 41702236265905244248723 := by
  unfold tailWord_548200
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997248306986249975617027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13329664409314999967489369 9997248306986249975617027)
  ·
    refine ⟨14995872460479374963425541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9997248306986249975617027 14995872460479374963425541)
    ·
      refine ⟨2811726086339882805642289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14995872460479374963425541 2811726086339882805642289)
      ·
        refine ⟨2108794564754912104231717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2811726086339882805642289 2108794564754912104231717)
        ·
          refine ⟨395398980891546019543447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2108794564754912104231717 395398980891546019543447)
          ·
            refine ⟨593098471337319029315171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395398980891546019543447 593098471337319029315171)
            ·
              refine ⟨889647707005978543972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593098471337319029315171 889647707005978543972757)
              ·
                refine ⟨41702236265905244248723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 889647707005978543972757 41702236265905244248723)
                ·
                  rfl

theorem cell21_548200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 6].length) (baseStart_548200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548200 prefixEnd_548200 := by exact prefixLift 548200
  have htrace : WordTrace (prefixWord ++ tailWord_548200) baseStart_548200 baseEnd_548200 := by
    simpa [prefixWord, tailWord_548200, baseEnd_548200] using wordTrace_append hprefix tailTrace_548200
  have hstable : (prefixWord ++ tailWord_548200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548200).length < 2 ^ (prefixWord ++ tailWord_548200).sum := by decide
  have hdescent : baseEnd_548200 < baseStart_548200 := by decide
  rcases family_descends (prefixWord ++ tailWord_548200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548321 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 4]
def baseStart_548321 : Nat := 118140960795 + 548321 * 2 ^ 59
def prefixEnd_548321 : Nat := 4983230072969 + 3 ^ 40 * 548321 * 2
def baseEnd_548321 : Nat := 125134322646246411229255

theorem tailTrace_548321 : CollatzResearch.WordTrace tailWord_548321 prefixEnd_548321 125134322646246411229255 := by
  unfold tailWord_548321
  simp only [CollatzResearch.WordTrace]
  refine ⟨19998909846534137616388817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13332606564356091744259211 19998909846534137616388817)
  ·
    refine ⟨14999182384900603212291613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19998909846534137616388817 14999182384900603212291613)
    ·
      refine ⟨5624693394337726204609355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14999182384900603212291613 5624693394337726204609355)
      ·
        refine ⟨8437040091506589306914033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5624693394337726204609355 8437040091506589306914033)
        ·
          refine ⟨6327780068629941980185525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437040091506589306914033 6327780068629941980185525)
          ·
            refine ⟨593229381434057060642393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6327780068629941980185525 593229381434057060642393)
            ·
              refine ⟨444922036075542795481795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593229381434057060642393 444922036075542795481795)
              ·
                refine ⟨667383054113314193222693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444922036075542795481795 667383054113314193222693)
                ·
                  refine ⟨125134322646246411229255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667383054113314193222693 125134322646246411229255)
                  ·
                    rfl

theorem cell21_548321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 4].length) (baseStart_548321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548321 prefixEnd_548321 := by exact prefixLift 548321
  have htrace : WordTrace (prefixWord ++ tailWord_548321) baseStart_548321 baseEnd_548321 := by
    simpa [prefixWord, tailWord_548321, baseEnd_548321] using wordTrace_append hprefix tailTrace_548321
  have hstable : (prefixWord ++ tailWord_548321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548321).length < 2 ^ (prefixWord ++ tailWord_548321).sum := by decide
  have hdescent : baseEnd_548321 < baseStart_548321 := by decide
  rcases family_descends (prefixWord ++ tailWord_548321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548445 : List Nat := [1, 4, 4, 2, 1, 2, 2, 5]
def baseStart_548445 : Nat := 118140960795 + 548445 * 2 ^ 59
def prefixEnd_548445 : Nat := 4983230072969 + 3 ^ 40 * 548445 * 2
def baseEnd_548445 : Nat := 41720873711883250387445

theorem tailTrace_548445 : CollatzResearch.WordTrace tailWord_548445 prefixEnd_548445 41720873711883250387445 := by
  unfold tailWord_548445
  simp only [CollatzResearch.WordTrace]
  refine ⟨20003432498084906793902789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13335621665389937862601859 20003432498084906793902789)
  ·
    refine ⟨3750643593390920023856773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20003432498084906793902789 3750643593390920023856773)
    ·
      refine ⟨703245673760797504473145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3750643593390920023856773 703245673760797504473145)
      ·
        refine ⟨527434255320598128354859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 703245673760797504473145 527434255320598128354859)
        ·
          refine ⟨791151382980897192532289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527434255320598128354859 791151382980897192532289)
          ·
            refine ⟨593363537235672894399217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791151382980897192532289 593363537235672894399217)
            ·
              refine ⟨445022652926754670799413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593363537235672894399217 445022652926754670799413)
              ·
                refine ⟨41720873711883250387445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445022652926754670799413 41720873711883250387445)
                ·
                  rfl

theorem cell21_548445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 5].length) (baseStart_548445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548445 prefixEnd_548445 := by exact prefixLift 548445
  have htrace : WordTrace (prefixWord ++ tailWord_548445) baseStart_548445 baseEnd_548445 := by
    simpa [prefixWord, tailWord_548445, baseEnd_548445] using wordTrace_append hprefix tailTrace_548445
  have hstable : (prefixWord ++ tailWord_548445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548445).length < 2 ^ (prefixWord ++ tailWord_548445).sum := by decide
  have hdescent : baseEnd_548445 < baseStart_548445 := by decide
  rcases family_descends (prefixWord ++ tailWord_548445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548470 : List Nat := [5, 1, 1, 2, 2, 1, 9]
def baseStart_548470 : Nat := 118140960795 + 548470 * 2 ^ 59
def prefixEnd_548470 : Nat := 4983230072969 + 3 ^ 40 * 548470 * 2
def baseEnd_548470 : Nat := 13907591830695029249513

theorem tailTrace_548470 : CollatzResearch.WordTrace tailWord_548470 prefixEnd_548470 13907591830695029249513 := by
  unfold tailWord_548470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250271520187146003972679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13336229548662890709041909 1250271520187146003972679)
  ·
    refine ⟨1875407280280719005959019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1250271520187146003972679 1875407280280719005959019)
    ·
      refine ⟨2813110920421078508938529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875407280280719005959019 2813110920421078508938529)
      ·
        refine ⟨2109833190315808881703897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813110920421078508938529 2109833190315808881703897)
        ·
          refine ⟨1582374892736856661277923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2109833190315808881703897 1582374892736856661277923)
          ·
            refine ⟨2373562339105284991916885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582374892736856661277923 2373562339105284991916885)
            ·
              refine ⟨13907591830695029249513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2373562339105284991916885 13907591830695029249513)
              ·
                rfl

theorem cell21_548470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 9].length) (baseStart_548470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548470 prefixEnd_548470 := by exact prefixLift 548470
  have htrace : WordTrace (prefixWord ++ tailWord_548470) baseStart_548470 baseEnd_548470 := by
    simpa [prefixWord, tailWord_548470, baseEnd_548470] using wordTrace_append hprefix tailTrace_548470
  have hstable : (prefixWord ++ tailWord_548470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548470).length < 2 ^ (prefixWord ++ tailWord_548470).sum := by decide
  have hdescent : baseEnd_548470 < baseStart_548470 := by decide
  rcases family_descends (prefixWord ++ tailWord_548470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548535 : List Nat := [1, 1, 3, 1, 5, 3, 2, 2, 3]
def baseStart_548535 : Nat := 118140960795 + 548535 * 2 ^ 59
def prefixEnd_548535 : Nat := 4983230072969 + 3 ^ 40 * 548535 * 2
def baseEnd_548535 : Nat := 125183160361829594662151

theorem tailTrace_548535 : CollatzResearch.WordTrace tailWord_548535 prefixEnd_548535 125183160361829594662151 := by
  unfold tailWord_548535
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006715067758852164679059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13337810045172568109786039 20006715067758852164679059)
  ·
    refine ⟨30010072601638278247018589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20006715067758852164679059 30010072601638278247018589)
    ·
      refine ⟨11253777225614354342631971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30010072601638278247018589 11253777225614354342631971)
      ·
        refine ⟨16880665838421531513947957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253777225614354342631971 16880665838421531513947957)
        ·
          refine ⟨1582562422352018579432621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16880665838421531513947957 1582562422352018579432621)
          ·
            refine ⟨593460908382006967287233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1582562422352018579432621 593460908382006967287233)
            ·
              refine ⟨445095681286505225465425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593460908382006967287233 445095681286505225465425)
              ·
                refine ⟨333821760964878919099069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445095681286505225465425 333821760964878919099069)
                ·
                  refine ⟨125183160361829594662151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333821760964878919099069 125183160361829594662151)
                  ·
                    rfl

theorem cell21_548535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 3].length) (baseStart_548535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548535 prefixEnd_548535 := by exact prefixLift 548535
  have htrace : WordTrace (prefixWord ++ tailWord_548535) baseStart_548535 baseEnd_548535 := by
    simpa [prefixWord, tailWord_548535, baseEnd_548535] using wordTrace_append hprefix tailTrace_548535
  have hstable : (prefixWord ++ tailWord_548535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548535).length < 2 ^ (prefixWord ++ tailWord_548535).sum := by decide
  have hdescent : baseEnd_548535 < baseStart_548535 := by decide
  rcases family_descends (prefixWord ++ tailWord_548535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548614 : List Nat := [6, 2, 2, 1, 1, 1, 1, 7]
def baseStart_548614 : Nat := 118140960795 + 548614 * 2 ^ 59
def prefixEnd_548614 : Nat := 4983230072969 + 3 ^ 40 * 548614 * 2
def baseEnd_548614 : Nat := 41733729746047670948441

theorem tailTrace_548614 : CollatzResearch.WordTrace tailWord_548614 prefixEnd_548614 41733729746047670948441 := by
  unfold tailWord_548614
  simp only [CollatzResearch.WordTrace]
  refine ⟨625299888577270270525153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13339730956315099104536597 625299888577270270525153)
  ·
    refine ⟨468974916432952702893865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 625299888577270270525153 468974916432952702893865)
    ·
      refine ⟨351731187324714527170399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 468974916432952702893865 351731187324714527170399)
      ·
        refine ⟨527596780987071790755599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351731187324714527170399 527596780987071790755599)
        ·
          refine ⟨791395171480607686133399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527596780987071790755599 791395171480607686133399)
          ·
            refine ⟨1187092757220911529200099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791395171480607686133399 1187092757220911529200099)
            ·
              refine ⟨1780639135831367293800149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187092757220911529200099 1780639135831367293800149)
              ·
                refine ⟨41733729746047670948441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1780639135831367293800149 41733729746047670948441)
                ·
                  rfl

theorem cell21_548614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_548614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548614 prefixEnd_548614 := by exact prefixLift 548614
  have htrace : WordTrace (prefixWord ++ tailWord_548614) baseStart_548614 baseEnd_548614 := by
    simpa [prefixWord, tailWord_548614, baseEnd_548614] using wordTrace_append hprefix tailTrace_548614
  have hstable : (prefixWord ++ tailWord_548614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548614).length < 2 ^ (prefixWord ++ tailWord_548614).sum := by decide
  have hdescent : baseEnd_548614 < baseStart_548614 := by decide
  rcases family_descends (prefixWord ++ tailWord_548614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548622 : List Nat := [4, 1, 1, 2, 1, 1, 6, 5]
def baseStart_548622 : Nat := 118140960795 + 548622 * 2 ^ 59
def prefixEnd_548622 : Nat := 4983230072969 + 3 ^ 40 * 548622 * 2
def baseEnd_548622 : Nat := 41734338315712258903991

theorem tailTrace_548622 : CollatzResearch.WordTrace tailWord_548622 prefixEnd_548622 41734338315712258903991 := by
  unfold tailWord_548622
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501236027305458252887015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13339925478962444015397413 2501236027305458252887015)
  ·
    refine ⟨3751854040958187379330523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2501236027305458252887015 3751854040958187379330523)
    ·
      refine ⟨5627781061437281068995785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3751854040958187379330523 5627781061437281068995785)
      ·
        refine ⟨4220835796077960801746839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5627781061437281068995785 4220835796077960801746839)
        ·
          refine ⟨6331253694116941202620259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220835796077960801746839 6331253694116941202620259)
          ·
            refine ⟨9496880541175411803930389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6331253694116941202620259 9496880541175411803930389)
            ·
              refine ⟨445166275367597428309237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9496880541175411803930389 445166275367597428309237)
              ·
                refine ⟨41734338315712258903991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445166275367597428309237 41734338315712258903991)
                ·
                  rfl

theorem cell21_548622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_548622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548622 prefixEnd_548622 := by exact prefixLift 548622
  have htrace : WordTrace (prefixWord ++ tailWord_548622) baseStart_548622 baseEnd_548622 := by
    simpa [prefixWord, tailWord_548622, baseEnd_548622] using wordTrace_append hprefix tailTrace_548622
  have hstable : (prefixWord ++ tailWord_548622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548622).length < 2 ^ (prefixWord ++ tailWord_548622).sum := by decide
  have hdescent : baseEnd_548622 < baseStart_548622 := by decide
  rcases family_descends (prefixWord ++ tailWord_548622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548712 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 5]
def baseStart_548712 : Nat := 118140960795 + 548712 * 2 ^ 59
def prefixEnd_548712 : Nat := 4983230072969 + 3 ^ 40 * 548712 * 2
def baseEnd_548712 : Nat := 125223554173316620211789

theorem tailTrace_548712 : CollatzResearch.WordTrace tailWord_548712 prefixEnd_548712 125223554173316620211789 := by
  unfold tailWord_548712
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006585394058805696936195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13342113858745074262581593 10006585394058805696936195)
  ·
    refine ⟨15009878091088208545404293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10006585394058805696936195 15009878091088208545404293)
    ·
      refine ⟨2814352142079039102263305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15009878091088208545404293 2814352142079039102263305)
      ·
        refine ⟨2110764106559279326697479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2814352142079039102263305 2110764106559279326697479)
        ·
          refine ⟨3166146159838918990046219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110764106559279326697479 3166146159838918990046219)
          ·
            refine ⟨4749219239758378485069329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166146159838918990046219 4749219239758378485069329)
            ·
              refine ⟨3561914429818783863801997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4749219239758378485069329 3561914429818783863801997)
              ·
                refine ⟨1335717911182043948925749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3561914429818783863801997 1335717911182043948925749)
                ·
                  refine ⟨125223554173316620211789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1335717911182043948925749 125223554173316620211789)
                  ·
                    rfl

theorem cell21_548712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 5].length) (baseStart_548712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548712 prefixEnd_548712 := by exact prefixLift 548712
  have htrace : WordTrace (prefixWord ++ tailWord_548712) baseStart_548712 baseEnd_548712 := by
    simpa [prefixWord, tailWord_548712, baseEnd_548712] using wordTrace_append hprefix tailTrace_548712
  have hstable : (prefixWord ++ tailWord_548712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548712).length < 2 ^ (prefixWord ++ tailWord_548712).sum := by decide
  have hdescent : baseEnd_548712 < baseStart_548712 := by decide
  rcases family_descends (prefixWord ++ tailWord_548712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548760 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 6]
def baseStart_548760 : Nat := 118140960795 + 548760 * 2 ^ 59
def prefixEnd_548760 : Nat := 4983230072969 + 3 ^ 40 * 548760 * 2
def baseEnd_548760 : Nat := 125234508427279203411691

theorem tailTrace_548760 : CollatzResearch.WordTrace tailWord_548760 prefixEnd_548760 125234508427279203411691 := by
  unfold tailWord_548760
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007460745971857795809867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13343280994629143727746489 10007460745971857795809867)
  ·
    refine ⟨15011191118957786693714801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007460745971857795809867 15011191118957786693714801)
    ·
      refine ⟨11258393339218340020286101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15011191118957786693714801 11258393339218340020286101)
      ·
        refine ⟨527737187775859688450911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11258393339218340020286101 527737187775859688450911)
        ·
          refine ⟨791605781663789532676367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527737187775859688450911 791605781663789532676367)
          ·
            refine ⟨1187408672495684299014551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791605781663789532676367 1187408672495684299014551)
            ·
              refine ⟨1781113008743526448521827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187408672495684299014551 1781113008743526448521827)
              ·
                refine ⟨2671669513115289672782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781113008743526448521827 2671669513115289672782741)
                ·
                  refine ⟨125234508427279203411691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2671669513115289672782741 125234508427279203411691)
                  ·
                    rfl

theorem cell21_548760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 6].length) (baseStart_548760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548760 prefixEnd_548760 := by exact prefixLift 548760
  have htrace : WordTrace (prefixWord ++ tailWord_548760) baseStart_548760 baseEnd_548760 := by
    simpa [prefixWord, tailWord_548760, baseEnd_548760] using wordTrace_append hprefix tailTrace_548760
  have hstable : (prefixWord ++ tailWord_548760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548760).length < 2 ^ (prefixWord ++ tailWord_548760).sum := by decide
  have hdescent : baseEnd_548760 < baseStart_548760 := by decide
  rcases family_descends (prefixWord ++ tailWord_548760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548816 : List Nat := [2, 1, 1, 1, 1, 2, 13]
def baseStart_548816 : Nat := 118140960795 + 548816 * 2 ^ 59
def prefixEnd_548816 : Nat := 4983230072969 + 3 ^ 40 * 548816 * 2
def baseEnd_548816 : Nat := 13916365376692838942027

theorem tailTrace_548816 : CollatzResearch.WordTrace tailWord_548816 prefixEnd_548816 13916365376692838942027 := by
  unfold tailWord_548816
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008481989870418577829151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13344642653160558103772201 10008481989870418577829151)
  ·
    refine ⟨15012722984805627866743727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10008481989870418577829151 15012722984805627866743727)
    ·
      refine ⟨22519084477208441800115591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15012722984805627866743727 22519084477208441800115591)
      ·
        refine ⟨33778626715812662700173387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22519084477208441800115591 33778626715812662700173387)
        ·
          refine ⟨50667940073718994050260081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33778626715812662700173387 50667940073718994050260081)
          ·
            refine ⟨38000955055289245537695061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50667940073718994050260081 38000955055289245537695061)
            ·
              refine ⟨13916365376692838942027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 38000955055289245537695061 13916365376692838942027)
              ·
                rfl

theorem cell21_548816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 13].length) (baseStart_548816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548816 prefixEnd_548816 := by exact prefixLift 548816
  have htrace : WordTrace (prefixWord ++ tailWord_548816) baseStart_548816 baseEnd_548816 := by
    simpa [prefixWord, tailWord_548816, baseEnd_548816] using wordTrace_append hprefix tailTrace_548816
  have hstable : (prefixWord ++ tailWord_548816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548816).length < 2 ^ (prefixWord ++ tailWord_548816).sum := by decide
  have hdescent : baseEnd_548816 < baseStart_548816 := by decide
  rcases family_descends (prefixWord ++ tailWord_548816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548828 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 4]
def baseStart_548828 : Nat := 118140960795 + 548828 * 2 ^ 59
def prefixEnd_548828 : Nat := 4983230072969 + 3 ^ 40 * 548828 * 2
def baseEnd_548828 : Nat := 125250026953726196278219

theorem tailTrace_548828 : CollatzResearch.WordTrace tailWord_548828 prefixEnd_548828 125250026953726196278219 := by
  unfold tailWord_548828
  simp only [CollatzResearch.WordTrace]
  refine ⟨10008700827848681602547569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13344934437131575470063425 10008700827848681602547569)
  ·
    refine ⟨7506525620886511201910677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10008700827848681602547569 7506525620886511201910677)
    ·
      refine ⟨351868388479055212589563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7506525620886511201910677 351868388479055212589563)
      ·
        refine ⟨527802582718582818884345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351868388479055212589563 527802582718582818884345)
        ·
          refine ⟨395851937038937114163259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527802582718582818884345 395851937038937114163259)
          ·
            refine ⟨593777905558405671244889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395851937038937114163259 593777905558405671244889)
            ·
              refine ⟨445333429168804253433667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593777905558405671244889 445333429168804253433667)
              ·
                refine ⟨668000143753206380150501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445333429168804253433667 668000143753206380150501)
                ·
                  refine ⟨125250026953726196278219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668000143753206380150501 125250026953726196278219)
                  ·
                    rfl

theorem cell21_548828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 4].length) (baseStart_548828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548828 prefixEnd_548828 := by exact prefixLift 548828
  have htrace : WordTrace (prefixWord ++ tailWord_548828) baseStart_548828 baseEnd_548828 := by
    simpa [prefixWord, tailWord_548828, baseEnd_548828] using wordTrace_append hprefix tailTrace_548828
  have hstable : (prefixWord ++ tailWord_548828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548828).length < 2 ^ (prefixWord ++ tailWord_548828).sum := by decide
  have hdescent : baseEnd_548828 < baseStart_548828 := by decide
  rcases family_descends (prefixWord ++ tailWord_548828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548847 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 7]
def baseStart_548847 : Nat := 118140960795 + 548847 * 2 ^ 59
def prefixEnd_548847 : Nat := 4983230072969 + 3 ^ 40 * 548847 * 2
def baseEnd_548847 : Nat := 125254363012586385461513

theorem tailTrace_548847 : CollatzResearch.WordTrace tailWord_548847 prefixEnd_548847 125254363012586385461513 := by
  unfold tailWord_548847
  simp only [CollatzResearch.WordTrace]
  refine ⟨20018094642628529450036795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13345396428419019633357863 20018094642628529450036795)
  ·
    refine ⟨30027141963942794175055193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20018094642628529450036795 30027141963942794175055193)
    ·
      refine ⟨22520356472957095631291395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30027141963942794175055193 22520356472957095631291395)
      ·
        refine ⟨33780534709435643446937093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22520356472957095631291395 33780534709435643446937093)
        ·
          refine ⟨6333850258019183146300705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33780534709435643446937093 6333850258019183146300705)
          ·
            refine ⟨4750387693514387359725529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6333850258019183146300705 4750387693514387359725529)
            ·
              refine ⟨3562790770135790519794147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4750387693514387359725529 3562790770135790519794147)
              ·
                refine ⟨5344186155203685779691221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562790770135790519794147 5344186155203685779691221)
                ·
                  refine ⟨125254363012586385461513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5344186155203685779691221 125254363012586385461513)
                  ·
                    rfl

theorem cell21_548847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 7].length) (baseStart_548847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548847 prefixEnd_548847 := by exact prefixLift 548847
  have htrace : WordTrace (prefixWord ++ tailWord_548847) baseStart_548847 baseEnd_548847 := by
    simpa [prefixWord, tailWord_548847, baseEnd_548847] using wordTrace_append hprefix tailTrace_548847
  have hstable : (prefixWord ++ tailWord_548847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548847).length < 2 ^ (prefixWord ++ tailWord_548847).sum := by decide
  have hdescent : baseEnd_548847 < baseStart_548847 := by decide
  rcases family_descends (prefixWord ++ tailWord_548847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548884 : List Nat := [2, 4, 3, 2, 1, 2, 1, 6]
def baseStart_548884 : Nat := 118140960795 + 548884 * 2 ^ 59
def prefixEnd_548884 : Nat := 4983230072969 + 3 ^ 40 * 548884 * 2
def baseEnd_548884 : Nat := 41754268972227514448257

theorem tailTrace_548884 : CollatzResearch.WordTrace tailWord_548884 prefixEnd_548884 41754268972227514448257 := by
  unfold tailWord_548884
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009722071747242384566853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13346296095662989846089137 10009722071747242384566853)
  ·
    refine ⟨1876822888452607947106285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10009722071747242384566853 1876822888452607947106285)
    ·
      refine ⟨703808583169727980164857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1876822888452607947106285 703808583169727980164857)
      ·
        refine ⟨527856437377295985123643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 703808583169727980164857 527856437377295985123643)
        ·
          refine ⟨791784656065943977685465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527856437377295985123643 791784656065943977685465)
          ·
            refine ⟨593838492049457983264099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 791784656065943977685465 593838492049457983264099)
            ·
              refine ⟨890757738074186974896149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593838492049457983264099 890757738074186974896149)
              ·
                refine ⟨41754268972227514448257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 890757738074186974896149 41754268972227514448257)
                ·
                  rfl

theorem cell21_548884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 6].length) (baseStart_548884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548884 prefixEnd_548884 := by exact prefixLift 548884
  have htrace : WordTrace (prefixWord ++ tailWord_548884) baseStart_548884 baseEnd_548884 := by
    simpa [prefixWord, tailWord_548884, baseEnd_548884] using wordTrace_append hprefix tailTrace_548884
  have hstable : (prefixWord ++ tailWord_548884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548884).length < 2 ^ (prefixWord ++ tailWord_548884).sum := by decide
  have hdescent : baseEnd_548884 < baseStart_548884 := by decide
  rcases family_descends (prefixWord ++ tailWord_548884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548926 : List Nat := [4, 2, 1, 3, 2, 1, 8]
def baseStart_548926 : Nat := 118140960795 + 548926 * 2 ^ 59
def prefixEnd_548926 : Nat := 4983230072969 + 3 ^ 40 * 548926 * 2
def baseEnd_548926 : Nat := 13919154654322200404965

theorem tailTrace_548926 : CollatzResearch.WordTrace tailWord_548926 prefixEnd_548926 13919154654322200404965 := by
  unfold tailWord_548926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2502622001167790742770329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13347317339561550628108421 2502622001167790742770329)
  ·
    refine ⟨1876966500875843057077747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2502622001167790742770329 1876966500875843057077747)
    ·
      refine ⟨2815449751313764585616621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876966500875843057077747 2815449751313764585616621)
      ·
        refine ⟨1055793656742661719606233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2815449751313764585616621 1055793656742661719606233)
        ·
          refine ⟨791845242556996289704675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1055793656742661719606233 791845242556996289704675)
          ·
            refine ⟨1187767863835494434557013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791845242556996289704675 1187767863835494434557013)
            ·
              refine ⟨13919154654322200404965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1187767863835494434557013 13919154654322200404965)
              ·
                rfl

theorem cell21_548926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 8].length) (baseStart_548926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548926 prefixEnd_548926 := by exact prefixLift 548926
  have htrace : WordTrace (prefixWord ++ tailWord_548926) baseStart_548926 baseEnd_548926 := by
    simpa [prefixWord, tailWord_548926, baseEnd_548926] using wordTrace_append hprefix tailTrace_548926
  have hstable : (prefixWord ++ tailWord_548926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548926).length < 2 ^ (prefixWord ++ tailWord_548926).sum := by decide
  have hdescent : baseEnd_548926 < baseStart_548926 := by decide
  rcases family_descends (prefixWord ++ tailWord_548926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548957 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 5]
def baseStart_548957 : Nat := 118140960795 + 548957 * 2 ^ 59
def prefixEnd_548957 : Nat := 4983230072969 + 3 ^ 40 * 548957 * 2
def baseEnd_548957 : Nat := 125279466511250638627955

theorem tailTrace_548957 : CollatzResearch.WordTrace tailWord_548957 prefixEnd_548957 125279466511250638627955 := by
  unfold tailWord_548957
  simp only [CollatzResearch.WordTrace]
  refine ⟨20022106672230018236541125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13348071114820012157694083 20022106672230018236541125)
  ·
    refine ⟨3754145001043128419351461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20022106672230018236541125 3754145001043128419351461)
    ·
      refine ⟨703902187695586578628399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3754145001043128419351461 703902187695586578628399)
      ·
        refine ⟨1055853281543379867942599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703902187695586578628399 1055853281543379867942599)
        ·
          refine ⟨1583779922315069801913899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055853281543379867942599 1583779922315069801913899)
          ·
            refine ⟨2375669883472604702870849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583779922315069801913899 2375669883472604702870849)
            ·
              refine ⟨1781752412604453527153137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375669883472604702870849 1781752412604453527153137)
              ·
                refine ⟨1336314309453340145364853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781752412604453527153137 1336314309453340145364853)
                ·
                  refine ⟨125279466511250638627955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336314309453340145364853 125279466511250638627955)
                  ·
                    rfl

theorem cell21_548957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_548957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548957 prefixEnd_548957 := by exact prefixLift 548957
  have htrace : WordTrace (prefixWord ++ tailWord_548957) baseStart_548957 baseEnd_548957 := by
    simpa [prefixWord, tailWord_548957, baseEnd_548957] using wordTrace_append hprefix tailTrace_548957
  have hstable : (prefixWord ++ tailWord_548957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548957).length < 2 ^ (prefixWord ++ tailWord_548957).sum := by decide
  have hdescent : baseEnd_548957 < baseStart_548957 := by decide
  rcases family_descends (prefixWord ++ tailWord_548957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_548985 : List Nat := [1, 2, 1, 3, 4, 3, 7]
def baseStart_548985 : Nat := 118140960795 + 548985 * 2 ^ 59
def prefixEnd_548985 : Nat := 4983230072969 + 3 ^ 40 * 548985 * 2
def baseEnd_548985 : Nat := 13920650721414312462359

theorem tailTrace_548985 : CollatzResearch.WordTrace tailWord_548985 prefixEnd_548985 13920650721414312462359 := by
  unfold tailWord_548985
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023127916128579018560409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13348751944085719345706939 20023127916128579018560409)
  ·
    refine ⟨15017345937096434263920307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20023127916128579018560409 15017345937096434263920307)
    ·
      refine ⟨22526018905644651395880461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15017345937096434263920307 22526018905644651395880461)
      ·
        refine ⟨8447257089616744273455173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22526018905644651395880461 8447257089616744273455173)
        ·
          refine ⟨1583860704303139551272845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8447257089616744273455173 1583860704303139551272845)
          ·
            refine ⟨593947764113677331727317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1583860704303139551272845 593947764113677331727317)
            ·
              refine ⟨13920650721414312462359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 593947764113677331727317 13920650721414312462359)
              ·
                rfl

theorem cell21_548985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 7].length) (baseStart_548985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_548985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_548985 prefixEnd_548985 := by exact prefixLift 548985
  have htrace : WordTrace (prefixWord ++ tailWord_548985) baseStart_548985 baseEnd_548985 := by
    simpa [prefixWord, tailWord_548985, baseEnd_548985] using wordTrace_append hprefix tailTrace_548985
  have hstable : (prefixWord ++ tailWord_548985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_548985).length < 2 ^ (prefixWord ++ tailWord_548985).sum := by decide
  have hdescent : baseEnd_548985 < baseStart_548985 := by decide
  rcases family_descends (prefixWord ++ tailWord_548985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549047 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_549047 : Nat := 118140960795 + 549047 * 2 ^ 59
def prefixEnd_549047 : Nat := 4983230072969 + 3 ^ 40 * 549047 * 2
def baseEnd_549047 : Nat := 125300005737430482127771

theorem tailTrace_549047 : CollatzResearch.WordTrace tailWord_549047 prefixEnd_549047 125300005737430482127771 := by
  unfold tailWord_549047
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025389241903963607317395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13350259494602642404878263 20025389241903963607317395)
  ·
    refine ⟨30038083862855945410976093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20025389241903963607317395 30038083862855945410976093)
    ·
      refine ⟨11264281448570979529116035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30038083862855945410976093 11264281448570979529116035)
      ·
        refine ⟨16896422172856469293674053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264281448570979529116035 16896422172856469293674053)
        ·
          refine ⟨3168079157410587992563885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16896422172856469293674053 3168079157410587992563885)
          ·
            refine ⟨1188029684028970497211457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3168079157410587992563885 1188029684028970497211457)
            ·
              refine ⟨891022263021727872908593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188029684028970497211457 891022263021727872908593)
              ·
                refine ⟨668266697266295904681445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891022263021727872908593 668266697266295904681445)
                ·
                  refine ⟨125300005737430482127771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668266697266295904681445 125300005737430482127771)
                  ·
                    rfl

theorem cell21_549047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_549047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549047 prefixEnd_549047 := by exact prefixLift 549047
  have htrace : WordTrace (prefixWord ++ tailWord_549047) baseStart_549047 baseEnd_549047 := by
    simpa [prefixWord, tailWord_549047, baseEnd_549047] using wordTrace_append hprefix tailTrace_549047
  have hstable : (prefixWord ++ tailWord_549047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549047).length < 2 ^ (prefixWord ++ tailWord_549047).sum := by decide
  have hdescent : baseEnd_549047 < baseStart_549047 := by decide
  rcases family_descends (prefixWord ++ tailWord_549047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549123 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 4]
def baseStart_549123 : Nat := 118140960795 + 549123 * 2 ^ 59
def prefixEnd_549123 : Nat := 4983230072969 + 3 ^ 40 * 549123 * 2
def baseEnd_549123 : Nat := 125317349972871238860949

theorem tailTrace_549123 : CollatzResearch.WordTrace tailWord_549123 prefixEnd_549123 125317349972871238860949 := by
  unfold tailWord_549123
  simp only [CollatzResearch.WordTrace]
  refine ⟨20028161189628628587084023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13352107459752419058056015 20028161189628628587084023)
  ·
    refine ⟨30042241784442942880626035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20028161189628628587084023 30042241784442942880626035)
    ·
      refine ⟨45063362676664414320939053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30042241784442942880626035 45063362676664414320939053)
      ·
        refine ⟨16898761003749155370352145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45063362676664414320939053 16898761003749155370352145)
        ·
          refine ⟨12674070752811866527764109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16898761003749155370352145 12674070752811866527764109)
          ·
            refine ⟨4752776532304449947911541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12674070752811866527764109 4752776532304449947911541)
            ·
              refine ⟨445572799903542182616707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4752776532304449947911541 445572799903542182616707)
              ·
                refine ⟨668359199855313273925061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445572799903542182616707 668359199855313273925061)
                ·
                  refine ⟨125317349972871238860949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668359199855313273925061 125317349972871238860949)
                  ·
                    rfl

theorem cell21_549123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 4].length) (baseStart_549123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549123 prefixEnd_549123 := by exact prefixLift 549123
  have htrace : WordTrace (prefixWord ++ tailWord_549123) baseStart_549123 baseEnd_549123 := by
    simpa [prefixWord, tailWord_549123, baseEnd_549123] using wordTrace_append hprefix tailTrace_549123
  have hstable : (prefixWord ++ tailWord_549123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549123).length < 2 ^ (prefixWord ++ tailWord_549123).sum := by decide
  have hdescent : baseEnd_549123 < baseStart_549123 := by decide
  rcases family_descends (prefixWord ++ tailWord_549123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549137 : List Nat := [1, 2, 2, 1, 1, 5, 4, 5]
def baseStart_549137 : Nat := 118140960795 + 549137 * 2 ^ 59
def prefixEnd_549137 : Nat := 4983230072969 + 3 ^ 40 * 549137 * 2
def baseEnd_549137 : Nat := 41773514987870108542529

theorem tailTrace_549137 : CollatzResearch.WordTrace tailWord_549137 prefixEnd_549137 41773514987870108542529 := by
  unfold tailWord_549137
  simp only [CollatzResearch.WordTrace]
  refine ⟨20028671811577908978093665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13352447874385272652062443 20028671811577908978093665)
  ·
    refine ⟨15021503858683431733570249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20028671811577908978093665 15021503858683431733570249)
    ·
      refine ⟨11266127894012573800177687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15021503858683431733570249 11266127894012573800177687)
      ·
        refine ⟨16899191841018860700266531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11266127894012573800177687 16899191841018860700266531)
        ·
          refine ⟨25348787761528291050399797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16899191841018860700266531 25348787761528291050399797)
          ·
            refine ⟨2376448852643277285974981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25348787761528291050399797 2376448852643277285974981)
            ·
              refine ⟨445584159870614491120309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2376448852643277285974981 445584159870614491120309)
              ·
                refine ⟨41773514987870108542529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 445584159870614491120309 41773514987870108542529)
                ·
                  rfl

theorem cell21_549137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 5].length) (baseStart_549137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549137 prefixEnd_549137 := by exact prefixLift 549137
  have htrace : WordTrace (prefixWord ++ tailWord_549137) baseStart_549137 baseEnd_549137 := by
    simpa [prefixWord, tailWord_549137, baseEnd_549137] using wordTrace_append hprefix tailTrace_549137
  have hstable : (prefixWord ++ tailWord_549137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549137).length < 2 ^ (prefixWord ++ tailWord_549137).sum := by decide
  have hdescent : baseEnd_549137 < baseStart_549137 := by decide
  rcases family_descends (prefixWord ++ tailWord_549137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549196 : List Nat := [2, 2, 1, 3, 2, 1, 1, 9]
def baseStart_549196 : Nat := 118140960795 + 549196 * 2 ^ 59
def prefixEnd_549196 : Nat := 4983230072969 + 3 ^ 40 * 549196 * 2
def baseEnd_549196 : Nat := 41778003189146444714711

theorem tailTrace_549196 : CollatzResearch.WordTrace tailWord_549196 prefixEnd_549196 41778003189146444714711 := by
  unfold tailWord_549196
  simp only [CollatzResearch.WordTrace]
  refine ⟨10015411859182081027245721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13353882478909441369660961 10015411859182081027245721)
  ·
    refine ⟨7511558894386560770434291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10015411859182081027245721 7511558894386560770434291)
    ·
      refine ⟨11267338341579841155651437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511558894386560770434291 11267338341579841155651437)
      ·
        refine ⟨4225251878092440433369289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11267338341579841155651437 4225251878092440433369289)
        ·
          refine ⟨3168938908569330325026967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4225251878092440433369289 3168938908569330325026967)
          ·
            refine ⟨4753408362853995487540451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168938908569330325026967 4753408362853995487540451)
            ·
              refine ⟨7130112544280993231310677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753408362853995487540451 7130112544280993231310677)
              ·
                refine ⟨41778003189146444714711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7130112544280993231310677 41778003189146444714711)
                ·
                  rfl

theorem cell21_549196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 9].length) (baseStart_549196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549196 prefixEnd_549196 := by exact prefixLift 549196
  have htrace : WordTrace (prefixWord ++ tailWord_549196) baseStart_549196 baseEnd_549196 := by
    simpa [prefixWord, tailWord_549196, baseEnd_549196] using wordTrace_append hprefix tailTrace_549196
  have hstable : (prefixWord ++ tailWord_549196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549196).length < 2 ^ (prefixWord ++ tailWord_549196).sum := by decide
  have hdescent : baseEnd_549196 < baseStart_549196 := by decide
  rcases family_descends (prefixWord ++ tailWord_549196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549213 : List Nat := [1, 4, 5, 11]
def baseStart_549213 : Nat := 118140960795 + 549213 * 2 ^ 59
def prefixEnd_549213 : Nat := 4983230072969 + 3 ^ 40 * 549213 * 2
def baseEnd_549213 : Nat := 515793782712144371855

theorem tailTrace_549213 : CollatzResearch.WordTrace tailWord_549213 prefixEnd_549213 515793782712144371855 := by
  unfold tailWord_549213
  simp only [CollatzResearch.WordTrace]
  refine ⟨20031443759302573957860293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354295839535049305240195 20031443759302573957860293)
  ·
    refine ⟨3755895704869232617098805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20031443759302573957860293 3755895704869232617098805)
    ·
      refine ⟨352115222331490557853013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3755895704869232617098805 352115222331490557853013)
      ·
        refine ⟨515793782712144371855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 352115222331490557853013 515793782712144371855)
        ·
          rfl

theorem cell21_549213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 11].length) (baseStart_549213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549213 prefixEnd_549213 := by exact prefixLift 549213
  have htrace : WordTrace (prefixWord ++ tailWord_549213) baseStart_549213 baseEnd_549213 := by
    simpa [prefixWord, tailWord_549213, baseEnd_549213] using wordTrace_append hprefix tailTrace_549213
  have hstable : (prefixWord ++ tailWord_549213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549213).length < 2 ^ (prefixWord ++ tailWord_549213).sum := by decide
  have hdescent : baseEnd_549213 < baseStart_549213 := by decide
  rcases family_descends (prefixWord ++ tailWord_549213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549241 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_549241 : Nat := 118140960795 + 549241 * 2 ^ 59
def prefixEnd_549241 : Nat := 4983230072969 + 3 ^ 40 * 549241 * 2
def baseEnd_549241 : Nat := 125344279180529255894041

theorem tailTrace_549241 : CollatzResearch.WordTrace tailWord_549241 prefixEnd_549241 125344279180529255894041 := by
  unfold tailWord_549241
  simp only [CollatzResearch.WordTrace]
  refine ⟨20032465003201134739879577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13354976668800756493253051 20032465003201134739879577)
  ·
    refine ⟨15024348752400851054909683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20032465003201134739879577 15024348752400851054909683)
    ·
      refine ⟨22536523128601276582364525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15024348752400851054909683 22536523128601276582364525)
      ·
        refine ⟨8451196173225478718386697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22536523128601276582364525 8451196173225478718386697)
        ·
          refine ⟨6338397129919109038790023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8451196173225478718386697 6338397129919109038790023)
          ·
            refine ⟨9507595694878663558185035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6338397129919109038790023 9507595694878663558185035)
            ·
              refine ⟨14261393542317995337277553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9507595694878663558185035 14261393542317995337277553)
              ·
                refine ⟨10696045156738496502958165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14261393542317995337277553 10696045156738496502958165)
                ·
                  refine ⟨125344279180529255894041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10696045156738496502958165 125344279180529255894041)
                  ·
                    rfl

theorem cell21_549241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_549241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549241 prefixEnd_549241 := by exact prefixLift 549241
  have htrace : WordTrace (prefixWord ++ tailWord_549241) baseStart_549241 baseEnd_549241 := by
    simpa [prefixWord, tailWord_549241, baseEnd_549241] using wordTrace_append hprefix tailTrace_549241
  have hstable : (prefixWord ++ tailWord_549241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549241).length < 2 ^ (prefixWord ++ tailWord_549241).sum := by decide
  have hdescent : baseEnd_549241 < baseStart_549241 := by decide
  rcases family_descends (prefixWord ++ tailWord_549241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549278 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_549278 : Nat := 118140960795 + 549278 * 2 ^ 59
def prefixEnd_549278 : Nat := 4983230072969 + 3 ^ 40 * 549278 * 2
def baseEnd_549278 : Nat := 125352723084625413777299

theorem tailTrace_549278 : CollatzResearch.WordTrace tailWord_549278 prefixEnd_549278 125352723084625413777299 := by
  unfold tailWord_549278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504226813008386257372061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13355876336044726705984325 2504226813008386257372061)
  ·
    refine ⟨939085054878144846514523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2504226813008386257372061 939085054878144846514523)
    ·
      refine ⟨1408627582317217269771785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939085054878144846514523 1408627582317217269771785)
      ·
        refine ⟨1056470686737912952328839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1408627582317217269771785 1056470686737912952328839)
        ·
          refine ⟨1584706030106869428493259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056470686737912952328839 1584706030106869428493259)
          ·
            refine ⟨2377059045160304142739889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584706030106869428493259 2377059045160304142739889)
            ·
              refine ⟨1782794283870228107054917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377059045160304142739889 1782794283870228107054917)
              ·
                refine ⟨334273928225667770072797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1782794283870228107054917 334273928225667770072797)
                ·
                  refine ⟨125352723084625413777299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334273928225667770072797 125352723084625413777299)
                  ·
                    rfl

theorem cell21_549278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_549278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549278 prefixEnd_549278 := by exact prefixLift 549278
  have htrace : WordTrace (prefixWord ++ tailWord_549278) baseStart_549278 baseEnd_549278 := by
    simpa [prefixWord, tailWord_549278, baseEnd_549278] using wordTrace_append hprefix tailTrace_549278
  have hstable : (prefixWord ++ tailWord_549278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549278).length < 2 ^ (prefixWord ++ tailWord_549278).sum := by decide
  have hdescent : baseEnd_549278 < baseStart_549278 := by decide
  rcases family_descends (prefixWord ++ tailWord_549278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549303 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_549303 : Nat := 118140960795 + 549303 * 2 ^ 59
def prefixEnd_549303 : Nat := 4983230072969 + 3 ^ 40 * 549303 * 2
def baseEnd_549303 : Nat := 125358428425230925860581

theorem tailTrace_549303 : CollatzResearch.WordTrace tailWord_549303 prefixEnd_549303 125358428425230925860581 := by
  unfold tailWord_549303
  simp only [CollatzResearch.WordTrace]
  refine ⟨20034726328976519328636563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13356484219317679552424375 20034726328976519328636563)
  ·
    refine ⟨30052089493464778992954845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20034726328976519328636563 30052089493464778992954845)
    ·
      refine ⟨11269533560049292122358067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30052089493464778992954845 11269533560049292122358067)
      ·
        refine ⟨16904300340073938183537101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11269533560049292122358067 16904300340073938183537101)
        ·
          refine ⟨6339112627527726818826413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16904300340073938183537101 6339112627527726818826413)
          ·
            refine ⟨2377167235322897557059905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6339112627527726818826413 2377167235322897557059905)
            ·
              refine ⟨1782875426492173167794929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377167235322897557059905 1782875426492173167794929)
              ·
                refine ⟨1337156569869129875846197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782875426492173167794929 1337156569869129875846197)
                ·
                  refine ⟨125358428425230925860581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1337156569869129875846197 125358428425230925860581)
                  ·
                    rfl

theorem cell21_549303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_549303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549303 prefixEnd_549303 := by exact prefixLift 549303
  have htrace : WordTrace (prefixWord ++ tailWord_549303) baseStart_549303 baseEnd_549303 := by
    simpa [prefixWord, tailWord_549303, baseEnd_549303] using wordTrace_append hprefix tailTrace_549303
  have hstable : (prefixWord ++ tailWord_549303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549303).length < 2 ^ (prefixWord ++ tailWord_549303).sum := by decide
  have hdescent : baseEnd_549303 < baseStart_549303 := by decide
  rcases family_descends (prefixWord ++ tailWord_549303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549337 : List Nat := [1, 2, 1, 2, 4, 1, 5, 2, 3]
def baseStart_549337 : Nat := 118140960795 + 549337 * 2 ^ 59
def prefixEnd_549337 : Nat := 4983230072969 + 3 ^ 40 * 549337 * 2
def baseEnd_549337 : Nat := 125366187688454422293845

theorem tailTrace_549337 : CollatzResearch.WordTrace tailWord_549337 prefixEnd_549337 125366187688454422293845 := by
  unfold tailWord_549337
  simp only [CollatzResearch.WordTrace]
  refine ⟨20035966410853343135374265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13357310940568895423582843 20035966410853343135374265)
  ·
    refine ⟨15026974808140007351530699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20035966410853343135374265 15026974808140007351530699)
    ·
      refine ⟨22540462212210011027296049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15026974808140007351530699 22540462212210011027296049)
      ·
        refine ⟨16905346659157508270472037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22540462212210011027296049 16905346659157508270472037)
        ·
          refine ⟨3169752498592032800713507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16905346659157508270472037 3169752498592032800713507)
          ·
            refine ⟨4754628747888049201070261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169752498592032800713507 4754628747888049201070261)
            ·
              refine ⟨445746445114504612600337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4754628747888049201070261 445746445114504612600337)
              ·
                refine ⟨334309833835878459450253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445746445114504612600337 334309833835878459450253)
                ·
                  refine ⟨125366187688454422293845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334309833835878459450253 125366187688454422293845)
                  ·
                    rfl

theorem cell21_549337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 2, 3].length) (baseStart_549337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549337 prefixEnd_549337 := by exact prefixLift 549337
  have htrace : WordTrace (prefixWord ++ tailWord_549337) baseStart_549337 baseEnd_549337 := by
    simpa [prefixWord, tailWord_549337, baseEnd_549337] using wordTrace_append hprefix tailTrace_549337
  have hstable : (prefixWord ++ tailWord_549337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549337).length < 2 ^ (prefixWord ++ tailWord_549337).sum := by decide
  have hdescent : baseEnd_549337 < baseStart_549337 := by decide
  rcases family_descends (prefixWord ++ tailWord_549337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549399 : List Nat := [1, 1, 3, 6, 2, 1, 1, 6]
def baseStart_549399 : Nat := 118140960795 + 549399 * 2 ^ 59
def prefixEnd_549399 : Nat := 4983230072969 + 3 ^ 40 * 549399 * 2
def baseEnd_549399 : Nat := 41793445644385364086795

theorem tailTrace_549399 : CollatzResearch.WordTrace tailWord_549399 prefixEnd_549399 41793445644385364086795 := by
  unfold tailWord_549399
  simp only [CollatzResearch.WordTrace]
  refine ⟨20038227736628727724131251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13358818491085818482754167 20038227736628727724131251)
  ·
    refine ⟨30057341604943091586196877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20038227736628727724131251 30057341604943091586196877)
    ·
      refine ⟨11271503101853659344823829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30057341604943091586196877 11271503101853659344823829)
      ·
        refine ⟨528351707899390281788617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11271503101853659344823829 528351707899390281788617)
        ·
          refine ⟨396263780924542711341463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528351707899390281788617 396263780924542711341463)
          ·
            refine ⟨594395671386814067012195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396263780924542711341463 594395671386814067012195)
            ·
              refine ⟨891593507080221100518293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 594395671386814067012195 891593507080221100518293)
              ·
                refine ⟨41793445644385364086795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 891593507080221100518293 41793445644385364086795)
                ·
                  rfl

theorem cell21_549399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 6].length) (baseStart_549399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549399 prefixEnd_549399 := by exact prefixLift 549399
  have htrace : WordTrace (prefixWord ++ tailWord_549399) baseStart_549399 baseEnd_549399 := by
    simpa [prefixWord, tailWord_549399, baseEnd_549399] using wordTrace_append hprefix tailTrace_549399
  have hstable : (prefixWord ++ tailWord_549399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549399).length < 2 ^ (prefixWord ++ tailWord_549399).sum := by decide
  have hdescent : baseEnd_549399 < baseStart_549399 := by decide
  rcases family_descends (prefixWord ++ tailWord_549399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549430 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 3]
def baseStart_549430 : Nat := 118140960795 + 549430 * 2 ^ 59
def prefixEnd_549430 : Nat := 4983230072969 + 3 ^ 40 * 549430 * 2
def baseEnd_549430 : Nat := 125387411555506927243655

theorem tailTrace_549430 : CollatzResearch.WordTrace tailWord_549430 prefixEnd_549430 125387411555506927243655 := by
  unfold tailWord_549430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1252459899969776251156859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13359572266344280012339829 1252459899969776251156859)
  ·
    refine ⟨1878689849954664376735289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1252459899969776251156859 1878689849954664376735289)
    ·
      refine ⟨1409017387465998282551467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1878689849954664376735289 1409017387465998282551467)
      ·
        refine ⟨2113526081198997423827201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409017387465998282551467 2113526081198997423827201)
        ·
          refine ⟨1585144560899248067870401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113526081198997423827201 1585144560899248067870401)
          ·
            refine ⟨1188858420674436050902801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585144560899248067870401 1188858420674436050902801)
            ·
              refine ⟨891643815505827038177101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1188858420674436050902801 891643815505827038177101)
              ·
                refine ⟨334366430814685139316413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 891643815505827038177101 334366430814685139316413)
                ·
                  refine ⟨125387411555506927243655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334366430814685139316413 125387411555506927243655)
                  ·
                    rfl

theorem cell21_549430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_549430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549430 prefixEnd_549430 := by exact prefixLift 549430
  have htrace : WordTrace (prefixWord ++ tailWord_549430) baseStart_549430 baseEnd_549430 := by
    simpa [prefixWord, tailWord_549430, baseEnd_549430] using wordTrace_append hprefix tailTrace_549430
  have hstable : (prefixWord ++ tailWord_549430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549430).length < 2 ^ (prefixWord ++ tailWord_549430).sum := by decide
  have hdescent : baseEnd_549430 < baseStart_549430 := by decide
  rcases family_descends (prefixWord ++ tailWord_549430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549486 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_549486 : Nat := 118140960795 + 549486 * 2 ^ 59
def prefixEnd_549486 : Nat := 4983230072969 + 3 ^ 40 * 549486 * 2
def baseEnd_549486 : Nat := 125400191518463274310207

theorem tailTrace_549486 : CollatzResearch.WordTrace tailWord_549486 prefixEnd_549486 125400191518463274310207 := by
  unfold tailWord_549486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505175110914192697818539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13360933924875694388365541 2505175110914192697818539)
  ·
    refine ⟨3757762666371289046727809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505175110914192697818539 3757762666371289046727809)
    ·
      refine ⟨2818321999778466785045857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3757762666371289046727809 2818321999778466785045857)
      ·
        refine ⟨2113741499833850088784393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2818321999778466785045857 2113741499833850088784393)
        ·
          refine ⟨1585306124875387566588295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113741499833850088784393 1585306124875387566588295)
          ·
            refine ⟨2377959187313081349882443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585306124875387566588295 2377959187313081349882443)
            ·
              refine ⟨3566938780969622024823665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377959187313081349882443 3566938780969622024823665)
              ·
                refine ⟨2675204085727216518617749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566938780969622024823665 2675204085727216518617749)
                ·
                  refine ⟨125400191518463274310207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2675204085727216518617749 125400191518463274310207)
                  ·
                    rfl

theorem cell21_549486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_549486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549486 prefixEnd_549486 := by exact prefixLift 549486
  have htrace : WordTrace (prefixWord ++ tailWord_549486) baseStart_549486 baseEnd_549486 := by
    simpa [prefixWord, tailWord_549486, baseEnd_549486] using wordTrace_append hprefix tailTrace_549486
  have hstable : (prefixWord ++ tailWord_549486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549486).length < 2 ^ (prefixWord ++ tailWord_549486).sum := by decide
  have hdescent : baseEnd_549486 < baseStart_549486 := by decide
  rcases family_descends (prefixWord ++ tailWord_549486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549559 : List Nat := [1, 1, 3, 1, 15]
def baseStart_549559 : Nat := 118140960795 + 549559 * 2 ^ 59
def prefixEnd_549559 : Nat := 4983230072969 + 3 ^ 40 * 549559 * 2
def baseEnd_549559 : Nat := 1548356186580634192511

theorem tailTrace_549559 : CollatzResearch.WordTrace tailWord_549559 prefixEnd_549559 1548356186580634192511 := by
  unfold tailWord_549559
  simp only [CollatzResearch.WordTrace]
  refine ⟨20044063416049075049955731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13362708944032716699970487 20044063416049075049955731)
  ·
    refine ⟨30066095124073612574933597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20044063416049075049955731 30066095124073612574933597)
    ·
      refine ⟨11274785671527604715600099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30066095124073612574933597 11274785671527604715600099)
      ·
        refine ⟨16912178507291407073400149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11274785671527604715600099 16912178507291407073400149)
        ·
          refine ⟨1548356186580634192511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 16912178507291407073400149 1548356186580634192511)
          ·
            rfl

theorem cell21_549559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 15].length) (baseStart_549559 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549559 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549559 prefixEnd_549559 := by exact prefixLift 549559
  have htrace : WordTrace (prefixWord ++ tailWord_549559) baseStart_549559 baseEnd_549559 := by
    simpa [prefixWord, tailWord_549559, baseEnd_549559] using wordTrace_append hprefix tailTrace_549559
  have hstable : (prefixWord ++ tailWord_549559).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549559).length < 2 ^ (prefixWord ++ tailWord_549559).sum := by decide
  have hdescent : baseEnd_549559 < baseStart_549559 := by decide
  rcases family_descends (prefixWord ++ tailWord_549559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549562 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 4]
def baseStart_549562 : Nat := 118140960795 + 549562 * 2 ^ 59
def prefixEnd_549562 : Nat := 4983230072969 + 3 ^ 40 * 549562 * 2
def baseEnd_549562 : Nat := 125417535753904031043385

theorem tailTrace_549562 : CollatzResearch.WordTrace tailWord_549562 prefixEnd_549562 125417535753904031043385 := by
  unfold tailWord_549562
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011043208759551640578735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13362781890025471041543293 5011043208759551640578735)
  ·
    refine ⟨7516564813139327460868103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011043208759551640578735 7516564813139327460868103)
    ·
      refine ⟨11274847219708991191302155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516564813139327460868103 11274847219708991191302155)
      ·
        refine ⟨16912270829563486786953233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11274847219708991191302155 16912270829563486786953233)
        ·
          refine ⟨12684203122172615090214925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16912270829563486786953233 12684203122172615090214925)
          ·
            refine ⟨4756576170814730658830597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12684203122172615090214925 4756576170814730658830597)
            ·
              refine ⟨891858032027761998530737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4756576170814730658830597 891858032027761998530737)
              ·
                refine ⟨668893524020821498898053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 891858032027761998530737 668893524020821498898053)
                ·
                  refine ⟨125417535753904031043385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 668893524020821498898053 125417535753904031043385)
                  ·
                    rfl

theorem cell21_549562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_549562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549562 prefixEnd_549562 := by exact prefixLift 549562
  have htrace : WordTrace (prefixWord ++ tailWord_549562) baseStart_549562 baseEnd_549562 := by
    simpa [prefixWord, tailWord_549562, baseEnd_549562] using wordTrace_append hprefix tailTrace_549562
  have hstable : (prefixWord ++ tailWord_549562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549562).length < 2 ^ (prefixWord ++ tailWord_549562).sum := by decide
  have hdescent : baseEnd_549562 < baseStart_549562 := by decide
  rcases family_descends (prefixWord ++ tailWord_549562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549565 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 3]
def baseStart_549565 : Nat := 118140960795 + 549565 * 2 ^ 59
def prefixEnd_549565 : Nat := 4983230072969 + 3 ^ 40 * 549565 * 2
def baseEnd_549565 : Nat := 125418220394776692493379

theorem tailTrace_549565 : CollatzResearch.WordTrace tailWord_549565 prefixEnd_549565 125418220394776692493379 := by
  unfold tailWord_549565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20044282254027338074674149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13362854836018225383116099 20044282254027338074674149)
  ·
    refine ⟨3758302922630125889001403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20044282254027338074674149 3758302922630125889001403)
    ·
      refine ⟨5637454383945188833502105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758302922630125889001403 5637454383945188833502105)
      ·
        refine ⟨4228090787958891625126579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5637454383945188833502105 4228090787958891625126579)
        ·
          refine ⟨6342136181938337437689869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228090787958891625126579 6342136181938337437689869)
          ·
            refine ⟨2378301068226876539133701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6342136181938337437689869 2378301068226876539133701)
            ·
              refine ⟨445931450292539351087569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2378301068226876539133701 445931450292539351087569)
              ·
                refine ⟨334448587719404513315677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445931450292539351087569 334448587719404513315677)
                ·
                  refine ⟨125418220394776692493379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334448587719404513315677 125418220394776692493379)
                  ·
                    rfl

theorem cell21_549565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_549565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549565 prefixEnd_549565 := by exact prefixLift 549565
  have htrace : WordTrace (prefixWord ++ tailWord_549565) baseStart_549565 baseEnd_549565 := by
    simpa [prefixWord, tailWord_549565, baseEnd_549565] using wordTrace_append hprefix tailTrace_549565
  have hstable : (prefixWord ++ tailWord_549565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549565).length < 2 ^ (prefixWord ++ tailWord_549565).sum := by decide
  have hdescent : baseEnd_549565 < baseStart_549565 := by decide
  rcases family_descends (prefixWord ++ tailWord_549565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549576 : List Nat := [2, 1, 3, 1, 2, 3, 3, 6]
def baseStart_549576 : Nat := 118140960795 + 549576 * 2 ^ 59
def prefixEnd_549576 : Nat := 4983230072969 + 3 ^ 40 * 549576 * 2
def baseEnd_549576 : Nat := 41806910248214372603341

theorem tailTrace_549576 : CollatzResearch.WordTrace tailWord_549576 prefixEnd_549576 41806910248214372603341 := by
  unfold tailWord_549576
  simp only [CollatzResearch.WordTrace]
  refine ⟨10022341728493743476662291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13363122304658324635549721 10022341728493743476662291)
  ·
    refine ⟨15033512592740615214993437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10022341728493743476662291 15033512592740615214993437)
    ·
      refine ⟨5637567222277730705622539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15033512592740615214993437 5637567222277730705622539)
      ·
        refine ⟨8456350833416596058433809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5637567222277730705622539 8456350833416596058433809)
        ·
          refine ⟨6342263125062447043825357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8456350833416596058433809 6342263125062447043825357)
          ·
            refine ⟨2378348671898417641434509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6342263125062447043825357 2378348671898417641434509)
            ·
              refine ⟨891880751961906615537941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2378348671898417641434509 891880751961906615537941)
              ·
                refine ⟨41806910248214372603341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 891880751961906615537941 41806910248214372603341)
                ·
                  rfl

theorem cell21_549576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 6].length) (baseStart_549576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549576 prefixEnd_549576 := by exact prefixLift 549576
  have htrace : WordTrace (prefixWord ++ tailWord_549576) baseStart_549576 baseEnd_549576 := by
    simpa [prefixWord, tailWord_549576, baseEnd_549576] using wordTrace_append hprefix tailTrace_549576
  have hstable : (prefixWord ++ tailWord_549576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549576).length < 2 ^ (prefixWord ++ tailWord_549576).sum := by decide
  have hdescent : baseEnd_549576 < baseStart_549576 := by decide
  rcases family_descends (prefixWord ++ tailWord_549576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549635 : List Nat := [1, 1, 1, 3, 2, 2, 1, 10]
def baseStart_549635 : Nat := 118140960795 + 549635 * 2 ^ 59
def prefixEnd_549635 : Nat := 4983230072969 + 3 ^ 40 * 549635 * 2
def baseEnd_549635 : Nat := 41811398449490708775523

theorem tailTrace_549635 : CollatzResearch.WordTrace tailWord_549635 prefixEnd_549635 41811398449490708775523 := by
  unfold tailWord_549635
  simp only [CollatzResearch.WordTrace]
  refine ⟨20046835363773740029722359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13364556909182493353148239 20046835363773740029722359)
  ·
    refine ⟨30070253045660610044583539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20046835363773740029722359 30070253045660610044583539)
    ·
      refine ⟨45105379568490915066875309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30070253045660610044583539 45105379568490915066875309)
      ·
        refine ⟨16914517338184093150078241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45105379568490915066875309 16914517338184093150078241)
        ·
          refine ⟨12685888003638069862558681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16914517338184093150078241 12685888003638069862558681)
          ·
            refine ⟨9514416002728552396919011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12685888003638069862558681 9514416002728552396919011)
            ·
              refine ⟨14271624004092828595378517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9514416002728552396919011 14271624004092828595378517)
              ·
                refine ⟨41811398449490708775523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14271624004092828595378517 41811398449490708775523)
                ·
                  rfl

theorem cell21_549635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_549635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549635 prefixEnd_549635 := by exact prefixLift 549635
  have htrace : WordTrace (prefixWord ++ tailWord_549635) baseStart_549635 baseEnd_549635 := by
    simpa [prefixWord, tailWord_549635, baseEnd_549635] using wordTrace_append hprefix tailTrace_549635
  have hstable : (prefixWord ++ tailWord_549635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549635).length < 2 ^ (prefixWord ++ tailWord_549635).sum := by decide
  have hdescent : baseEnd_549635 < baseStart_549635 := by decide
  rcases family_descends (prefixWord ++ tailWord_549635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549683 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_549683 : Nat := 118140960795 + 549683 * 2 ^ 59
def prefixEnd_549683 : Nat := 4983230072969 + 3 ^ 40 * 549683 * 2
def baseEnd_549683 : Nat := 125445149602434709526471

theorem tailTrace_549683 : CollatzResearch.WordTrace tailWord_549683 prefixEnd_549683 125445149602434709526471 := by
  unfold tailWord_549683
  simp only [CollatzResearch.WordTrace]
  refine ⟨20048586067599844227469703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13365724045066562818313135 20048586067599844227469703)
  ·
    refine ⟨30072879101399766341204555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20048586067599844227469703 30072879101399766341204555)
    ·
      refine ⟨45109318652099649511806833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30072879101399766341204555 45109318652099649511806833)
      ·
        refine ⟨33831988989074737133855125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45109318652099649511806833 33831988989074737133855125)
        ·
          refine ⟨1585874483862878303149459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33831988989074737133855125 1585874483862878303149459)
          ·
            refine ⟨2378811725794317454724189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585874483862878303149459 2378811725794317454724189)
            ·
              refine ⟨892054397172869045521571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2378811725794317454724189 892054397172869045521571)
              ·
                refine ⟨1338081595759303568282357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892054397172869045521571 1338081595759303568282357)
                ·
                  refine ⟨125445149602434709526471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1338081595759303568282357 125445149602434709526471)
                  ·
                    rfl

theorem cell21_549683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_549683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549683 prefixEnd_549683 := by exact prefixLift 549683
  have htrace : WordTrace (prefixWord ++ tailWord_549683) baseStart_549683 baseEnd_549683 := by
    simpa [prefixWord, tailWord_549683, baseEnd_549683] using wordTrace_append hprefix tailTrace_549683
  have hstable : (prefixWord ++ tailWord_549683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549683).length < 2 ^ (prefixWord ++ tailWord_549683).sum := by decide
  have hdescent : baseEnd_549683 < baseStart_549683 := by decide
  rcases family_descends (prefixWord ++ tailWord_549683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549686 : List Nat := [5, 1, 2, 2, 2, 1, 2, 6]
def baseStart_549686 : Nat := 118140960795 + 549686 * 2 ^ 59
def prefixEnd_549686 : Nat := 4983230072969 + 3 ^ 40 * 549686 * 2
def baseEnd_549686 : Nat := 41815278081102456992155

theorem tailTrace_549686 : CollatzResearch.WordTrace tailWord_549686 prefixEnd_549686 41815278081102456992155 := by
  unfold tailWord_549686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253043467911810983739307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13365796991059317159885941 1253043467911810983739307)
  ·
    refine ⟨1879565201867716475608961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1253043467911810983739307 1879565201867716475608961)
    ·
      refine ⟨1409673901400787356706721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1879565201867716475608961 1409673901400787356706721)
      ·
        refine ⟨1057255426050590517530041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1409673901400787356706721 1057255426050590517530041)
        ·
          refine ⟨792941569537942888147531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057255426050590517530041 792941569537942888147531)
          ·
            refine ⟨1189412354306914332221297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792941569537942888147531 1189412354306914332221297)
            ·
              refine ⟨892059265730185749165973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1189412354306914332221297 892059265730185749165973)
              ·
                refine ⟨41815278081102456992155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 892059265730185749165973 41815278081102456992155)
                ·
                  rfl

theorem cell21_549686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_549686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549686 prefixEnd_549686 := by exact prefixLift 549686
  have htrace : WordTrace (prefixWord ++ tailWord_549686) baseStart_549686 baseEnd_549686 := by
    simpa [prefixWord, tailWord_549686, baseEnd_549686] using wordTrace_append hprefix tailTrace_549686
  have hstable : (prefixWord ++ tailWord_549686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549686).length < 2 ^ (prefixWord ++ tailWord_549686).sum := by decide
  have hdescent : baseEnd_549686 < baseStart_549686 := by decide
  rcases family_descends (prefixWord ++ tailWord_549686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549818 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_549818 : Nat := 118140960795 + 549818 * 2 ^ 59
def prefixEnd_549818 : Nat := 4983230072969 + 3 ^ 40 * 549818 * 2
def baseEnd_549818 : Nat := 125475958441704474776195

theorem tailTrace_549818 : CollatzResearch.WordTrace tailWord_549818 prefixEnd_549818 125475958441704474776195 := by
  unfold tailWord_549818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013377480527690570908527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13369006614740508189089405 5013377480527690570908527)
  ·
    refine ⟨7520066220791535856362791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013377480527690570908527 7520066220791535856362791)
    ·
      refine ⟨11280099331187303784544187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7520066220791535856362791 11280099331187303784544187)
      ·
        refine ⟨16920148996780955676816281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11280099331187303784544187 16920148996780955676816281)
        ·
          refine ⟨12690111747585716757612211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16920148996780955676816281 12690111747585716757612211)
          ·
            refine ⟨19035167621378575136418317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12690111747585716757612211 19035167621378575136418317)
            ·
              refine ⟨7138187858016965676156869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19035167621378575136418317 7138187858016965676156869)
              ·
                refine ⟨1338410223378181064279413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7138187858016965676156869 1338410223378181064279413)
                ·
                  refine ⟨125475958441704474776195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1338410223378181064279413 125475958441704474776195)
                  ·
                    rfl

theorem cell21_549818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_549818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549818 prefixEnd_549818 := by exact prefixLift 549818
  have htrace : WordTrace (prefixWord ++ tailWord_549818) baseStart_549818 baseEnd_549818 := by
    simpa [prefixWord, tailWord_549818, baseEnd_549818] using wordTrace_append hprefix tailTrace_549818
  have hstable : (prefixWord ++ tailWord_549818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549818).length < 2 ^ (prefixWord ++ tailWord_549818).sum := by decide
  have hdescent : baseEnd_549818 < baseStart_549818 := by decide
  rcases family_descends (prefixWord ++ tailWord_549818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549849 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_549849 : Nat := 118140960795 + 549849 * 2 ^ 59
def prefixEnd_549849 : Nat := 4983230072969 + 3 ^ 40 * 549849 * 2
def baseEnd_549849 : Nat := 125483033064055309759465

theorem tailTrace_549849 : CollatzResearch.WordTrace tailWord_549849 prefixEnd_549849 125483033064055309759465 := by
  unfold tailWord_549849
  simp only [CollatzResearch.WordTrace]
  refine ⟨20054640584998454578012601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13369760389998969718675067 20054640584998454578012601)
  ·
    refine ⟨15040980438748840933509451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20054640584998454578012601 15040980438748840933509451)
    ·
      refine ⟨22561470658123261400264177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15040980438748840933509451 22561470658123261400264177)
      ·
        refine ⟨16921102993592446050198133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22561470658123261400264177 16921102993592446050198133)
        ·
          refine ⟨1586353405649291817206075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16921102993592446050198133 1586353405649291817206075)
          ·
            refine ⟨2379530108473937725809113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586353405649291817206075 2379530108473937725809113)
            ·
              refine ⟨1784647581355453294356835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379530108473937725809113 1784647581355453294356835)
              ·
                refine ⟨2676971372033179941535253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784647581355453294356835 2676971372033179941535253)
                ·
                  refine ⟨125483033064055309759465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2676971372033179941535253 125483033064055309759465)
                  ·
                    rfl

theorem cell21_549849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_549849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549849 prefixEnd_549849 := by exact prefixLift 549849
  have htrace : WordTrace (prefixWord ++ tailWord_549849) baseStart_549849 baseEnd_549849 := by
    simpa [prefixWord, tailWord_549849, baseEnd_549849] using wordTrace_append hprefix tailTrace_549849
  have hstable : (prefixWord ++ tailWord_549849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549849).length < 2 ^ (prefixWord ++ tailWord_549849).sum := by decide
  have hdescent : baseEnd_549849 < baseStart_549849 := by decide
  rcases family_descends (prefixWord ++ tailWord_549849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549866 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_549866 : Nat := 118140960795 + 549866 * 2 ^ 59
def prefixEnd_549866 : Nat := 4983230072969 + 3 ^ 40 * 549866 * 2
def baseEnd_549866 : Nat := 125486912695667057976097

theorem tailTrace_549866 : CollatzResearch.WordTrace tailWord_549866 prefixEnd_549866 125486912695667057976097 := by
  unfold tailWord_549866
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013815156484216620345363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13370173750624577654254301 5013815156484216620345363)
  ·
    refine ⟨7520722734726324930518045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013815156484216620345363 7520722734726324930518045)
    ·
      refine ⟨2820271025522371848944267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7520722734726324930518045 2820271025522371848944267)
      ·
        refine ⟨4230406538283557773416401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820271025522371848944267 4230406538283557773416401)
        ·
          refine ⟨3172804903712668330062301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230406538283557773416401 3172804903712668330062301)
          ·
            refine ⟨1189801838892250623773363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3172804903712668330062301 1189801838892250623773363)
            ·
              refine ⟨1784702758338375935660045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189801838892250623773363 1784702758338375935660045)
              ·
                refine ⟨669263534376890975872517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1784702758338375935660045 669263534376890975872517)
                ·
                  refine ⟨125486912695667057976097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669263534376890975872517 125486912695667057976097)
                  ·
                    rfl

theorem cell21_549866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_549866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549866 prefixEnd_549866 := by exact prefixLift 549866
  have htrace : WordTrace (prefixWord ++ tailWord_549866) baseStart_549866 baseEnd_549866 := by
    simpa [prefixWord, tailWord_549866, baseEnd_549866] using wordTrace_append hprefix tailTrace_549866
  have hstable : (prefixWord ++ tailWord_549866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549866).length < 2 ^ (prefixWord ++ tailWord_549866).sum := by decide
  have hdescent : baseEnd_549866 < baseStart_549866 := by decide
  rcases family_descends (prefixWord ++ tailWord_549866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_549925 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_549925 : Nat := 118140960795 + 549925 * 2 ^ 59
def prefixEnd_549925 : Nat := 4983230072969 + 3 ^ 40 * 549925 * 2
def baseEnd_549925 : Nat := 125500377299496066492643

theorem tailTrace_549925 : CollatzResearch.WordTrace tailWord_549925 prefixEnd_549925 125500377299496066492643 := by
  unfold tailWord_549925
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057412532723119557779229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13371608355148746371852819 20057412532723119557779229)
  ·
    refine ⟨7521529699771169834167211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20057412532723119557779229 7521529699771169834167211)
    ·
      refine ⟨11282294549656754751250817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521529699771169834167211 11282294549656754751250817)
      ·
        refine ⟨8461720912242566063438113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11282294549656754751250817 8461720912242566063438113)
        ·
          refine ⟨6346290684181924547578585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8461720912242566063438113 6346290684181924547578585)
          ·
            refine ⟨4759718013136443410683939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6346290684181924547578585 4759718013136443410683939)
            ·
              refine ⟨7139577019704665116025909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4759718013136443410683939 7139577019704665116025909)
              ·
                refine ⟨669335345597312354627429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7139577019704665116025909 669335345597312354627429)
                ·
                  refine ⟨125500377299496066492643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669335345597312354627429 125500377299496066492643)
                  ·
                    rfl

theorem cell21_549925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_549925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_549925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_549925 prefixEnd_549925 := by exact prefixLift 549925
  have htrace : WordTrace (prefixWord ++ tailWord_549925) baseStart_549925 baseEnd_549925 := by
    simpa [prefixWord, tailWord_549925, baseEnd_549925] using wordTrace_append hprefix tailTrace_549925
  have hstable : (prefixWord ++ tailWord_549925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_549925).length < 2 ^ (prefixWord ++ tailWord_549925).sum := by decide
  have hdescent : baseEnd_549925 < baseStart_549925 := by decide
  rcases family_descends (prefixWord ++ tailWord_549925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550021 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 3]
def baseStart_550021 : Nat := 118140960795 + 550021 * 2 ^ 59
def prefixEnd_550021 : Nat := 4983230072969 + 3 ^ 40 * 550021 * 2
def baseEnd_550021 : Nat := 125522285807421232892447

theorem tailTrace_550021 : CollatzResearch.WordTrace tailWord_550021 prefixEnd_550021 125522285807421232892447 := by
  unfold tailWord_550021
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060913940375327953273917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13373942626916885302182611 20060913940375327953273917)
  ·
    refine ⟨7522842727640747982477719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20060913940375327953273917 7522842727640747982477719)
    ·
      refine ⟨11284264091461121973716579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522842727640747982477719 11284264091461121973716579)
      ·
        refine ⟨16926396137191682960574869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11284264091461121973716579 16926396137191682960574869)
        ·
          refine ⟨793424818930860138776947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16926396137191682960574869 793424818930860138776947)
          ·
            refine ⟨1190137228396290208165421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793424818930860138776947 1190137228396290208165421)
            ·
              refine ⟨446301460648608828062033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1190137228396290208165421 446301460648608828062033)
              ·
                refine ⟨334726095486456621046525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446301460648608828062033 334726095486456621046525)
                ·
                  refine ⟨125522285807421232892447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334726095486456621046525 125522285807421232892447)
                  ·
                    rfl

theorem cell21_550021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 3].length) (baseStart_550021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550021 prefixEnd_550021 := by exact prefixLift 550021
  have htrace : WordTrace (prefixWord ++ tailWord_550021) baseStart_550021 baseEnd_550021 := by
    simpa [prefixWord, tailWord_550021, baseEnd_550021] using wordTrace_append hprefix tailTrace_550021
  have hstable : (prefixWord ++ tailWord_550021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550021).length < 2 ^ (prefixWord ++ tailWord_550021).sum := by decide
  have hdescent : baseEnd_550021 < baseStart_550021 := by decide
  rcases family_descends (prefixWord ++ tailWord_550021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550060 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 6]
def baseStart_550060 : Nat := 118140960795 + 550060 * 2 ^ 59
def prefixEnd_550060 : Nat := 4983230072969 + 3 ^ 40 * 550060 * 2
def baseEnd_550060 : Nat := 125531186138765831742367

theorem tailTrace_550060 : CollatzResearch.WordTrace tailWord_550060 prefixEnd_550060 125531186138765831742367 := by
  unfold tailWord_550060
  simp only [CollatzResearch.WordTrace]
  refine ⟨10031168193617018806971817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13374890924822691742629089 10031168193617018806971817)
  ·
    refine ⟨7523376145212764105228863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10031168193617018806971817 7523376145212764105228863)
    ·
      refine ⟨11285064217819146157843295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7523376145212764105228863 11285064217819146157843295)
      ·
        refine ⟨16927596326728719236764943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11285064217819146157843295 16927596326728719236764943)
        ·
          refine ⟨25391394490093078855147415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16927596326728719236764943 25391394490093078855147415)
          ·
            refine ⟨38087091735139618282721123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25391394490093078855147415 38087091735139618282721123)
            ·
              refine ⟨57130637602709427424081685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38087091735139618282721123 57130637602709427424081685)
              ·
                refine ⟨2677998637627004410503829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57130637602709427424081685 2677998637627004410503829)
                ·
                  refine ⟨125531186138765831742367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2677998637627004410503829 125531186138765831742367)
                  ·
                    rfl

theorem cell21_550060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_550060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550060 prefixEnd_550060 := by exact prefixLift 550060
  have htrace : WordTrace (prefixWord ++ tailWord_550060) baseStart_550060 baseEnd_550060 := by
    simpa [prefixWord, tailWord_550060, baseEnd_550060] using wordTrace_append hprefix tailTrace_550060
  have hstable : (prefixWord ++ tailWord_550060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550060).length < 2 ^ (prefixWord ++ tailWord_550060).sum := by decide
  have hdescent : baseEnd_550060 < baseStart_550060 := by decide
  rcases family_descends (prefixWord ++ tailWord_550060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550077 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_550077 : Nat := 118140960795 + 550077 * 2 ^ 59
def prefixEnd_550077 : Nat := 4983230072969 + 3 ^ 40 * 550077 * 2
def baseEnd_550077 : Nat := 125535065770377579958999

theorem tailTrace_550077 : CollatzResearch.WordTrace tailWord_550077 prefixEnd_550077 125535065770377579958999 := by
  unfold tailWord_550077
  simp only [CollatzResearch.WordTrace]
  refine ⟨20062956428172449517312485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13375304285448299678208323 20062956428172449517312485)
  ·
    refine ⟨3761804330282334284496091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20062956428172449517312485 3761804330282334284496091)
    ·
      refine ⟨5642706495423501426744137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761804330282334284496091 5642706495423501426744137)
      ·
        refine ⟨4232029871567626070058103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642706495423501426744137 4232029871567626070058103)
        ·
          refine ⟨6348044807351439105087155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4232029871567626070058103 6348044807351439105087155)
          ·
            refine ⟨9522067211027158657630733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6348044807351439105087155 9522067211027158657630733)
            ·
              refine ⟨3570775204135184496611525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9522067211027158657630733 3570775204135184496611525)
              ·
                refine ⟨669520350775347093114661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3570775204135184496611525 669520350775347093114661)
                ·
                  refine ⟨125535065770377579958999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 669520350775347093114661 125535065770377579958999)
                  ·
                    rfl

theorem cell21_550077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_550077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550077 prefixEnd_550077 := by exact prefixLift 550077
  have htrace : WordTrace (prefixWord ++ tailWord_550077) baseStart_550077 baseEnd_550077 := by
    simpa [prefixWord, tailWord_550077, baseEnd_550077] using wordTrace_append hprefix tailTrace_550077
  have hstable : (prefixWord ++ tailWord_550077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550077).length < 2 ^ (prefixWord ++ tailWord_550077).sum := by decide
  have hdescent : baseEnd_550077 < baseStart_550077 := by decide
  rcases family_descends (prefixWord ++ tailWord_550077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550080 : List Nat := [2, 1, 1, 2, 6, 1, 1, 4, 3]
def baseStart_550080 : Nat := 118140960795 + 550080 * 2 ^ 59
def prefixEnd_550080 : Nat := 4983230072969 + 3 ^ 40 * 550080 * 2
def baseEnd_550080 : Nat := 125535750411250241408993

theorem tailTrace_550080 : CollatzResearch.WordTrace tailWord_550080 prefixEnd_550080 125535750411250241408993 := by
  unfold tailWord_550080
  simp only [CollatzResearch.WordTrace]
  refine ⟨10031532923580790514835847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13375377231441054019781129 10031532923580790514835847)
  ·
    refine ⟨15047299385371185772253771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10031532923580790514835847 15047299385371185772253771)
    ·
      refine ⟨22570949078056778658380657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15047299385371185772253771 22570949078056778658380657)
      ·
        refine ⟨16928211808542583993785493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22570949078056778658380657 16928211808542583993785493)
        ·
          refine ⟨793509928525433624708695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16928211808542583993785493 793509928525433624708695)
          ·
            refine ⟨1190264892788150437063043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793509928525433624708695 1190264892788150437063043)
            ·
              refine ⟨1785397339182225655594565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1190264892788150437063043 1785397339182225655594565)
              ·
                refine ⟨334762001096667310423981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1785397339182225655594565 334762001096667310423981)
                ·
                  refine ⟨125535750411250241408993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334762001096667310423981 125535750411250241408993)
                  ·
                    rfl

theorem cell21_550080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 4, 3].length) (baseStart_550080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550080 prefixEnd_550080 := by exact prefixLift 550080
  have htrace : WordTrace (prefixWord ++ tailWord_550080) baseStart_550080 baseEnd_550080 := by
    simpa [prefixWord, tailWord_550080, baseEnd_550080] using wordTrace_append hprefix tailTrace_550080
  have hstable : (prefixWord ++ tailWord_550080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550080).length < 2 ^ (prefixWord ++ tailWord_550080).sum := by decide
  have hdescent : baseEnd_550080 < baseStart_550080 := by decide
  rcases family_descends (prefixWord ++ tailWord_550080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550167 : List Nat := [1, 1, 3, 4, 1, 1, 3, 7]
def baseStart_550167 : Nat := 118140960795 + 550167 * 2 ^ 59
def prefixEnd_550167 : Nat := 4983230072969 + 3 ^ 40 * 550167 * 2
def baseEnd_550167 : Nat := 41851868332185807819605

theorem tailTrace_550167 : CollatzResearch.WordTrace tailWord_550167 prefixEnd_550167 41851868332185807819605 := by
  unfold tailWord_550167
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066238997846394888088755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13377492665230929925392503 20066238997846394888088755)
  ·
    refine ⟨30099358496769592332133133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20066238997846394888088755 30099358496769592332133133)
    ·
      refine ⟨11287259436288597124549925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30099358496769592332133133 11287259436288597124549925)
      ·
        refine ⟨2116361144304111960853111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11287259436288597124549925 2116361144304111960853111)
        ·
          refine ⟨3174541716456167941279667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116361144304111960853111 3174541716456167941279667)
          ·
            refine ⟨4761812574684251911919501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174541716456167941279667 4761812574684251911919501)
            ·
              refine ⟨1785679715506594466969813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4761812574684251911919501 1785679715506594466969813)
              ·
                refine ⟨41851868332185807819605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1785679715506594466969813 41851868332185807819605)
                ·
                  rfl

theorem cell21_550167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_550167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550167 prefixEnd_550167 := by exact prefixLift 550167
  have htrace : WordTrace (prefixWord ++ tailWord_550167) baseStart_550167 baseEnd_550167 := by
    simpa [prefixWord, tailWord_550167, baseEnd_550167] using wordTrace_append hprefix tailTrace_550167
  have hstable : (prefixWord ++ tailWord_550167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550167).length < 2 ^ (prefixWord ++ tailWord_550167).sum := by decide
  have hdescent : baseEnd_550167 < baseStart_550167 := by decide
  rcases family_descends (prefixWord ++ tailWord_550167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550173 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 3]
def baseStart_550173 : Nat := 118140960795 + 550173 * 2 ^ 59
def prefixEnd_550173 : Nat := 4983230072969 + 3 ^ 40 * 550173 * 2
def baseEnd_550173 : Nat := 125556974278302746358803

theorem tailTrace_550173 : CollatzResearch.WordTrace tailWord_550173 prefixEnd_550173 125556974278302746358803 := by
  unfold tailWord_550173
  simp only [CollatzResearch.WordTrace]
  refine ⟨20066457835824657912807173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13377638557216438608538115 20066457835824657912807173)
  ·
    refine ⟨3762460844217123358651345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20066457835824657912807173 3762460844217123358651345)
    ·
      refine ⟨2821845633162842518988509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3762460844217123358651345 2821845633162842518988509)
      ·
        refine ⟨1058192112436065944620691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2821845633162842518988509 1058192112436065944620691)
        ·
          refine ⟨1587288168654098916931037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058192112436065944620691 1587288168654098916931037)
          ·
            refine ⟨595233063245287093849139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1587288168654098916931037 595233063245287093849139)
            ·
              refine ⟨892849594867930640773709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595233063245287093849139 892849594867930640773709)
              ·
                refine ⟨334818598075473990290141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 892849594867930640773709 334818598075473990290141)
                ·
                  refine ⟨125556974278302746358803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334818598075473990290141 125556974278302746358803)
                  ·
                    rfl

theorem cell21_550173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_550173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550173 prefixEnd_550173 := by exact prefixLift 550173
  have htrace : WordTrace (prefixWord ++ tailWord_550173) baseStart_550173 baseEnd_550173 := by
    simpa [prefixWord, tailWord_550173, baseEnd_550173] using wordTrace_append hprefix tailTrace_550173
  have hstable : (prefixWord ++ tailWord_550173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550173).length < 2 ^ (prefixWord ++ tailWord_550173).sum := by decide
  have hdescent : baseEnd_550173 < baseStart_550173 := by decide
  rcases family_descends (prefixWord ++ tailWord_550173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550184 : List Nat := [2, 1, 5, 1, 2, 3, 7]
def baseStart_550184 : Nat := 118140960795 + 550184 * 2 ^ 59
def prefixEnd_550184 : Nat := 4983230072969 + 3 ^ 40 * 550184 * 2
def baseEnd_550184 : Nat := 13951053847574352408383

theorem tailTrace_550184 : CollatzResearch.WordTrace tailWord_550184 prefixEnd_550184 13951053847574352408383 := by
  unfold tailWord_550184
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033429519392403395728803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13377906025856537860971737 10033429519392403395728803)
  ·
    refine ⟨15050144279088605093593205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10033429519392403395728803 15050144279088605093593205)
    ·
      refine ⟨1410951026164556727524363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15050144279088605093593205 1410951026164556727524363)
      ·
        refine ⟨2116426539246835091286545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410951026164556727524363 2116426539246835091286545)
        ·
          refine ⟨1587319904435126318464909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2116426539246835091286545 1587319904435126318464909)
          ·
            refine ⟨595244964163172369424341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1587319904435126318464909 595244964163172369424341)
            ·
              refine ⟨13951053847574352408383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 595244964163172369424341 13951053847574352408383)
              ·
                rfl

theorem cell21_550184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 7].length) (baseStart_550184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550184 prefixEnd_550184 := by exact prefixLift 550184
  have htrace : WordTrace (prefixWord ++ tailWord_550184) baseStart_550184 baseEnd_550184 := by
    simpa [prefixWord, tailWord_550184, baseEnd_550184] using wordTrace_append hprefix tailTrace_550184
  have hstable : (prefixWord ++ tailWord_550184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550184).length < 2 ^ (prefixWord ++ tailWord_550184).sum := by decide
  have hdescent : baseEnd_550184 < baseStart_550184 := by decide
  rcases family_descends (prefixWord ++ tailWord_550184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550460 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 3]
def baseStart_550460 : Nat := 118140960795 + 550460 * 2 ^ 59
def prefixEnd_550460 : Nat := 4983230072969 + 3 ^ 40 * 550460 * 2
def baseEnd_550460 : Nat := 125622471588454025074883

theorem tailTrace_550460 : CollatzResearch.WordTrace tailWord_550460 prefixEnd_550460 125622471588454025074883 := by
  unfold tailWord_550460
  simp only [CollatzResearch.WordTrace]
  refine ⟨10038462792892452964252417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13384617057189937285669889 10038462792892452964252417)
  ·
    refine ⟨7528847094669339723189313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10038462792892452964252417 7528847094669339723189313)
    ·
      refine ⟨5646635321002004792391985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7528847094669339723189313 5646635321002004792391985)
      ·
        refine ⟨4234976490751503594293989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5646635321002004792391985 4234976490751503594293989)
        ·
          refine ⟨794058092015906923930123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4234976490751503594293989 794058092015906923930123)
          ·
            refine ⟨1191087138023860385895185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794058092015906923930123 1191087138023860385895185)
            ·
              refine ⟨893315353517895289421389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191087138023860385895185 893315353517895289421389)
              ·
                refine ⟨334993257569210733533021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893315353517895289421389 334993257569210733533021)
                ·
                  refine ⟨125622471588454025074883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 334993257569210733533021 125622471588454025074883)
                  ·
                    rfl

theorem cell21_550460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 3].length) (baseStart_550460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550460 prefixEnd_550460 := by exact prefixLift 550460
  have htrace : WordTrace (prefixWord ++ tailWord_550460) baseStart_550460 baseEnd_550460 := by
    simpa [prefixWord, tailWord_550460, baseEnd_550460] using wordTrace_append hprefix tailTrace_550460
  have hstable : (prefixWord ++ tailWord_550460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550460).length < 2 ^ (prefixWord ++ tailWord_550460).sum := by decide
  have hdescent : baseEnd_550460 < baseStart_550460 := by decide
  rcases family_descends (prefixWord ++ tailWord_550460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550471 : List Nat := [1, 1, 4, 1, 5, 1, 8]
def baseStart_550471 : Nat := 118140960795 + 550471 * 2 ^ 59
def prefixEnd_550471 : Nat := 4983230072969 + 3 ^ 40 * 550471 * 2
def baseEnd_550471 : Nat := 13958331326480050043503

theorem tailTrace_550471 : CollatzResearch.WordTrace tailWord_550471 prefixEnd_550471 13958331326480050043503 := by
  unfold tailWord_550471
  simp only [CollatzResearch.WordTrace]
  refine ⟨20077326788745054807155267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13384884525830036538103511 20077326788745054807155267)
  ·
    refine ⟨30115990183117582210732901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20077326788745054807155267 30115990183117582210732901)
    ·
      refine ⟨5646748159334546664512419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30115990183117582210732901 5646748159334546664512419)
      ·
        refine ⟨8470122239001819996768629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646748159334546664512419 8470122239001819996768629)
        ·
          refine ⟨794073959906420624697059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8470122239001819996768629 794073959906420624697059)
          ·
            refine ⟨1191110939859630937045589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794073959906420624697059 1191110939859630937045589)
            ·
              refine ⟨13958331326480050043503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1191110939859630937045589 13958331326480050043503)
              ·
                rfl

theorem cell21_550471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 8].length) (baseStart_550471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550471 prefixEnd_550471 := by exact prefixLift 550471
  have htrace : WordTrace (prefixWord ++ tailWord_550471) baseStart_550471 baseEnd_550471 := by
    simpa [prefixWord, tailWord_550471, baseEnd_550471] using wordTrace_append hprefix tailTrace_550471
  have hstable : (prefixWord ++ tailWord_550471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550471).length < 2 ^ (prefixWord ++ tailWord_550471).sum := by decide
  have hdescent : baseEnd_550471 < baseStart_550471 := by decide
  rcases family_descends (prefixWord ++ tailWord_550471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550536 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 5]
def baseStart_550536 : Nat := 118140960795 + 550536 * 2 ^ 59
def prefixEnd_550536 : Nat := 4983230072969 + 3 ^ 40 * 550536 * 2
def baseEnd_550536 : Nat := 125639815823894781808061

theorem tailTrace_550536 : CollatzResearch.WordTrace tailWord_550536 prefixEnd_550536 125639815823894781808061 := by
  unfold tailWord_550536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039848766754785454135731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13386465022339713938847641 10039848766754785454135731)
  ·
    refine ⟨15059773150132178181203597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10039848766754785454135731 15059773150132178181203597)
    ·
      refine ⟨5647414931299566817951349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15059773150132178181203597 5647414931299566817951349)
      ·
        refine ⟨529445149809334389182939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5647414931299566817951349 529445149809334389182939)
        ·
          refine ⟨794167724714001583774409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529445149809334389182939 794167724714001583774409)
          ·
            refine ⟨595625793535501187830807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794167724714001583774409 595625793535501187830807)
            ·
              refine ⟨893438690303251781746211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595625793535501187830807 893438690303251781746211)
              ·
                refine ⟨1340158035454877672619317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893438690303251781746211 1340158035454877672619317)
                ·
                  refine ⟨125639815823894781808061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340158035454877672619317 125639815823894781808061)
                  ·
                    rfl

theorem cell21_550536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_550536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550536 prefixEnd_550536 := by exact prefixLift 550536
  have htrace : WordTrace (prefixWord ++ tailWord_550536) baseStart_550536 baseEnd_550536 := by
    simpa [prefixWord, tailWord_550536, baseEnd_550536] using wordTrace_append hprefix tailTrace_550536
  have hstable : (prefixWord ++ tailWord_550536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550536).length < 2 ^ (prefixWord ++ tailWord_550536).sum := by decide
  have hdescent : baseEnd_550536 < baseStart_550536 := by decide
  rcases family_descends (prefixWord ++ tailWord_550536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550598 : List Nat := [6, 1, 2, 1, 1, 3, 1, 6]
def baseStart_550598 : Nat := 118140960795 + 550598 * 2 ^ 59
def prefixEnd_550598 : Nat := 4983230072969 + 3 ^ 40 * 550598 * 2
def baseEnd_550598 : Nat := 41884655022865483924867

theorem tailTrace_550598 : CollatzResearch.WordTrace tailWord_550598 prefixEnd_550598 41884655022865483924867 := by
  unfold tailWord_550598
  simp only [CollatzResearch.WordTrace]
  refine ⟨627561214352654859282139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 13387972572856636998018965 627561214352654859282139)
  ·
    refine ⟨941341821528982288923209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 627561214352654859282139 941341821528982288923209)
    ·
      refine ⟨706006366146736716692407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 941341821528982288923209 706006366146736716692407)
      ·
        refine ⟨1059009549220105075038611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 706006366146736716692407 1059009549220105075038611)
        ·
          refine ⟨1588514323830157612557917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059009549220105075038611 1588514323830157612557917)
          ·
            refine ⟨595692871436309104709219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1588514323830157612557917 595692871436309104709219)
            ·
              refine ⟨893539307154463657063829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595692871436309104709219 893539307154463657063829)
              ·
                refine ⟨41884655022865483924867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 893539307154463657063829 41884655022865483924867)
                ·
                  rfl

theorem cell21_550598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_550598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550598 prefixEnd_550598 := by exact prefixLift 550598
  have htrace : WordTrace (prefixWord ++ tailWord_550598) baseStart_550598 baseEnd_550598 := by
    simpa [prefixWord, tailWord_550598, baseEnd_550598] using wordTrace_append hprefix tailTrace_550598
  have hstable : (prefixWord ++ tailWord_550598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550598).length < 2 ^ (prefixWord ++ tailWord_550598).sum := by decide
  have hdescent : baseEnd_550598 < baseStart_550598 := by decide
  rcases family_descends (prefixWord ++ tailWord_550598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550623 : List Nat := [1, 1, 2, 3, 2, 2, 5, 5]
def baseStart_550623 : Nat := 118140960795 + 550623 * 2 ^ 59
def prefixEnd_550623 : Nat := 4983230072969 + 3 ^ 40 * 550623 * 2
def baseEnd_550623 : Nat := 41886556803067321285961

theorem tailTrace_550623 : CollatzResearch.WordTrace tailWord_550623 prefixEnd_550623 41886556803067321285961 := by
  unfold tailWord_550623
  simp only [CollatzResearch.WordTrace]
  refine ⟨20082870684194384766688523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13388580456129589844459015 20082870684194384766688523)
  ·
    refine ⟨30124306026291577150032785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20082870684194384766688523 30124306026291577150032785)
    ·
      refine ⟨22593229519718682862524589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30124306026291577150032785 22593229519718682862524589)
      ·
        refine ⟨8472461069894506073446721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22593229519718682862524589 8472461069894506073446721)
        ·
          refine ⟨6354345802420879555085041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8472461069894506073446721 6354345802420879555085041)
          ·
            refine ⟨4765759351815659666313781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6354345802420879555085041 4765759351815659666313781)
            ·
              refine ⟨446789939232718093716917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4765759351815659666313781 446789939232718093716917)
              ·
                refine ⟨41886556803067321285961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 446789939232718093716917 41886556803067321285961)
                ·
                  rfl

theorem cell21_550623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 5].length) (baseStart_550623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550623 prefixEnd_550623 := by exact prefixLift 550623
  have htrace : WordTrace (prefixWord ++ tailWord_550623) baseStart_550623 baseEnd_550623 := by
    simpa [prefixWord, tailWord_550623, baseEnd_550623] using wordTrace_append hprefix tailTrace_550623
  have hstable : (prefixWord ++ tailWord_550623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550623).length < 2 ^ (prefixWord ++ tailWord_550623).sum := by decide
  have hdescent : baseEnd_550623 < baseStart_550623 := by decide
  rcases family_descends (prefixWord ++ tailWord_550623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550668 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 4]
def baseStart_550668 : Nat := 118140960795 + 550668 * 2 ^ 59
def prefixEnd_550668 : Nat := 4983230072969 + 3 ^ 40 * 550668 * 2
def baseEnd_550668 : Nat := 125669940022291885607791

theorem tailTrace_550668 : CollatzResearch.WordTrace tailWord_550668 prefixEnd_550668 125669940022291885607791 := by
  unfold tailWord_550668
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042255984515678726038329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13389674646020904968051105 10042255984515678726038329)
  ·
    refine ⟨7531691988386759044528747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10042255984515678726038329 7531691988386759044528747)
    ·
      refine ⟨11297537982580138566793121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7531691988386759044528747 11297537982580138566793121)
      ·
        refine ⟨8473153486935103925094841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11297537982580138566793121 8473153486935103925094841)
        ·
          refine ⟨6354865115201327943821131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8473153486935103925094841 6354865115201327943821131)
          ·
            refine ⟨9532297672801991915731697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354865115201327943821131 9532297672801991915731697)
            ·
              refine ⟨7149223254601493936798773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9532297672801991915731697 7149223254601493936798773)
              ·
                refine ⟨670239680118890056574885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7149223254601493936798773 670239680118890056574885)
                ·
                  refine ⟨125669940022291885607791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670239680118890056574885 125669940022291885607791)
                  ·
                    rfl

theorem cell21_550668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_550668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550668 prefixEnd_550668 := by exact prefixLift 550668
  have htrace : WordTrace (prefixWord ++ tailWord_550668) baseStart_550668 baseEnd_550668 := by
    simpa [prefixWord, tailWord_550668, baseEnd_550668] using wordTrace_append hprefix tailTrace_550668
  have hstable : (prefixWord ++ tailWord_550668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550668).length < 2 ^ (prefixWord ++ tailWord_550668).sum := by decide
  have hdescent : baseEnd_550668 < baseStart_550668 := by decide
  rcases family_descends (prefixWord ++ tailWord_550668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550719 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 4]
def baseStart_550719 : Nat := 118140960795 + 550719 * 2 ^ 59
def prefixEnd_550719 : Nat := 4983230072969 + 3 ^ 40 * 550719 * 2
def baseEnd_550719 : Nat := 125681578917127130257687

theorem tailTrace_550719 : CollatzResearch.WordTrace tailWord_550719 prefixEnd_550719 125681578917127130257687 := by
  unfold tailWord_550719
  simp only [CollatzResearch.WordTrace]
  refine ⟨20086372091846593162183211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13390914727897728774788807 20086372091846593162183211)
  ·
    refine ⟨30129558137769889743274817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20086372091846593162183211 30129558137769889743274817)
    ·
      refine ⟨22597168603327417307456113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30129558137769889743274817 22597168603327417307456113)
      ·
        refine ⟨16947876452495562980592085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22597168603327417307456113 16947876452495562980592085)
        ·
          refine ⟨397215854355364757357627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16947876452495562980592085 397215854355364757357627)
          ·
            refine ⟨595823781533047136036441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397215854355364757357627 595823781533047136036441)
            ·
              refine ⟨446867836149785352027331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595823781533047136036441 446867836149785352027331)
              ·
                refine ⟨670301754224678028040997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446867836149785352027331 670301754224678028040997)
                ·
                  refine ⟨125681578917127130257687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670301754224678028040997 125681578917127130257687)
                  ·
                    rfl

theorem cell21_550719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 4].length) (baseStart_550719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550719 prefixEnd_550719 := by exact prefixLift 550719
  have htrace : WordTrace (prefixWord ++ tailWord_550719) baseStart_550719 baseEnd_550719 := by
    simpa [prefixWord, tailWord_550719, baseEnd_550719] using wordTrace_append hprefix tailTrace_550719
  have hstable : (prefixWord ++ tailWord_550719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550719).length < 2 ^ (prefixWord ++ tailWord_550719).sum := by decide
  have hdescent : baseEnd_550719 < baseStart_550719 := by decide
  rcases family_descends (prefixWord ++ tailWord_550719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550764 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 3]
def baseStart_550764 : Nat := 118140960795 + 550764 * 2 ^ 59
def prefixEnd_550764 : Nat := 4983230072969 + 3 ^ 40 * 550764 * 2
def baseEnd_550764 : Nat := 125691848530217052007595

theorem tailTrace_550764 : CollatzResearch.WordTrace tailWord_550764 prefixEnd_550764 125691848530217052007595 := by
  unfold tailWord_550764
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044006688341782923785673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13392008917789043898380897 10044006688341782923785673)
  ·
    refine ⟨7533005016256337192839255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10044006688341782923785673 7533005016256337192839255)
    ·
      refine ⟨11299507524384505789258883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533005016256337192839255 11299507524384505789258883)
      ·
        refine ⟨16949261286576758683888325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11299507524384505789258883 16949261286576758683888325)
        ·
          refine ⟨3177986491233142253229061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16949261286576758683888325 3177986491233142253229061)
          ·
            refine ⟨595872467106214172480449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3177986491233142253229061 595872467106214172480449)
            ·
              refine ⟨446904350329660629360337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595872467106214172480449 446904350329660629360337)
              ·
                refine ⟨335178262747245472020253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446904350329660629360337 335178262747245472020253)
                ·
                  refine ⟨125691848530217052007595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335178262747245472020253 125691848530217052007595)
                  ·
                    rfl

theorem cell21_550764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_550764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550764 prefixEnd_550764 := by exact prefixLift 550764
  have htrace : WordTrace (prefixWord ++ tailWord_550764) baseStart_550764 baseEnd_550764 := by
    simpa [prefixWord, tailWord_550764, baseEnd_550764] using wordTrace_append hprefix tailTrace_550764
  have hstable : (prefixWord ++ tailWord_550764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550764).length < 2 ^ (prefixWord ++ tailWord_550764).sum := by decide
  have hdescent : baseEnd_550764 < baseStart_550764 := by decide
  rcases family_descends (prefixWord ++ tailWord_550764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550789 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_550789 : Nat := 118140960795 + 550789 * 2 ^ 59
def prefixEnd_550789 : Nat := 4983230072969 + 3 ^ 40 * 550789 * 2
def baseEnd_550789 : Nat := 125697553870822564090877

theorem tailTrace_550789 : CollatzResearch.WordTrace tailWord_550789 prefixEnd_550789 125697553870822564090877 := by
  unfold tailWord_550789
  simp only [CollatzResearch.WordTrace]
  refine ⟨20088925201592995117231421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13392616801061996744820947 20088925201592995117231421)
  ·
    refine ⟨7533346950597373168961783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20088925201592995117231421 7533346950597373168961783)
    ·
      refine ⟨11300020425896059753442675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533346950597373168961783 11300020425896059753442675)
      ·
        refine ⟨16950030638844089630164013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11300020425896059753442675 16950030638844089630164013)
        ·
          refine ⟨6356261489566533611311505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16950030638844089630164013 6356261489566533611311505)
          ·
            refine ⟨4767196117174900208483629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6356261489566533611311505 4767196117174900208483629)
            ·
              refine ⟨1787698543940587578181361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4767196117174900208483629 1787698543940587578181361)
              ·
                refine ⟨1340773907955440683636021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787698543940587578181361 1340773907955440683636021)
                ·
                  refine ⟨125697553870822564090877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1340773907955440683636021 125697553870822564090877)
                  ·
                    rfl

theorem cell21_550789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_550789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550789 prefixEnd_550789 := by exact prefixLift 550789
  have htrace : WordTrace (prefixWord ++ tailWord_550789) baseStart_550789 baseEnd_550789 := by
    simpa [prefixWord, tailWord_550789, baseEnd_550789] using wordTrace_append hprefix tailTrace_550789
  have hstable : (prefixWord ++ tailWord_550789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550789).length < 2 ^ (prefixWord ++ tailWord_550789).sum := by decide
  have hdescent : baseEnd_550789 < baseStart_550789 := by decide
  rcases family_descends (prefixWord ++ tailWord_550789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550792 : List Nat := [2, 1, 3, 3, 3, 1, 3, 5]
def baseStart_550792 : Nat := 118140960795 + 550792 * 2 ^ 59
def prefixEnd_550792 : Nat := 4983230072969 + 3 ^ 40 * 550792 * 2
def baseEnd_550792 : Nat := 41899412837231741846957

theorem tailTrace_550792 : CollatzResearch.WordTrace tailWord_550792 prefixEnd_550792 41899412837231741846957 := by
  unfold tailWord_550792
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044517310291063314795315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13392689747054751086393753 10044517310291063314795315)
  ·
    refine ⟨15066775965436594972192973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10044517310291063314795315 15066775965436594972192973)
    ·
      refine ⟨5650040987038723114572365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15066775965436594972192973 5650040987038723114572365)
      ·
        refine ⟨2118765370139521167964637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5650040987038723114572365 2118765370139521167964637)
        ·
          refine ⟨794537013802320437986739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118765370139521167964637 794537013802320437986739)
          ·
            refine ⟨1191805520703480656980109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794537013802320437986739 1191805520703480656980109)
            ·
              refine ⟨446927070263805246367541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1191805520703480656980109 446927070263805246367541)
              ·
                refine ⟨41899412837231741846957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 446927070263805246367541 41899412837231741846957)
                ·
                  rfl

theorem cell21_550792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 5].length) (baseStart_550792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550792 prefixEnd_550792 := by exact prefixLift 550792
  have htrace : WordTrace (prefixWord ++ tailWord_550792) baseStart_550792 baseEnd_550792 := by
    simpa [prefixWord, tailWord_550792, baseEnd_550792] using wordTrace_append hprefix tailTrace_550792
  have hstable : (prefixWord ++ tailWord_550792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550792).length < 2 ^ (prefixWord ++ tailWord_550792).sum := by decide
  have hdescent : baseEnd_550792 < baseStart_550792 := by decide
  rcases family_descends (prefixWord ++ tailWord_550792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550820 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 6]
def baseStart_550820 : Nat := 118140960795 + 550820 * 2 ^ 59
def prefixEnd_550820 : Nat := 4983230072969 + 3 ^ 40 * 550820 * 2
def baseEnd_550820 : Nat := 125704628493173399074147

theorem tailTrace_550820 : CollatzResearch.WordTrace tailWord_550820 prefixEnd_550820 125704628493173399074147 := by
  unfold tailWord_550820
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045027932240343705804957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13393370576320458274406609 10045027932240343705804957)
  ·
    refine ⟨3766885474590128889676859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10045027932240343705804957 3766885474590128889676859)
    ·
      refine ⟨5650328211885193334515289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3766885474590128889676859 5650328211885193334515289)
      ·
        refine ⟨4237746158913895000886467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5650328211885193334515289 4237746158913895000886467)
        ·
          refine ⟨6356619238370842501329701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237746158913895000886467 6356619238370842501329701)
          ·
            refine ⟨1191866107194532968999319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6356619238370842501329701 1191866107194532968999319)
            ·
              refine ⟨1787799160791799453498979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191866107194532968999319 1787799160791799453498979)
              ·
                refine ⟨2681698741187699180248469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787799160791799453498979 2681698741187699180248469)
                ·
                  refine ⟨125704628493173399074147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2681698741187699180248469 125704628493173399074147)
                  ·
                    rfl

theorem cell21_550820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_550820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550820 prefixEnd_550820 := by exact prefixLift 550820
  have htrace : WordTrace (prefixWord ++ tailWord_550820) baseStart_550820 baseEnd_550820 := by
    simpa [prefixWord, tailWord_550820, baseEnd_550820] using wordTrace_append hprefix tailTrace_550820
  have hstable : (prefixWord ++ tailWord_550820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550820).length < 2 ^ (prefixWord ++ tailWord_550820).sum := by decide
  have hdescent : baseEnd_550820 < baseStart_550820 := by decide
  rcases family_descends (prefixWord ++ tailWord_550820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550823 : List Nat := [1, 1, 6, 1, 2, 1, 2, 4, 3]
def baseStart_550823 : Nat := 118140960795 + 550823 * 2 ^ 59
def prefixEnd_550823 : Nat := 4983230072969 + 3 ^ 40 * 550823 * 2
def baseEnd_550823 : Nat := 125705313134046060524141

theorem tailTrace_550823 : CollatzResearch.WordTrace tailWord_550823 prefixEnd_550823 125705313134046060524141 := by
  unfold tailWord_550823
  simp only [CollatzResearch.WordTrace]
  refine ⟨20090165283469818923969123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13393443522313212615979415 20090165283469818923969123)
  ·
    refine ⟨30135247925204728385953685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20090165283469818923969123 30135247925204728385953685)
    ·
      refine ⟨1412589746493971643091579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30135247925204728385953685 1412589746493971643091579)
      ·
        refine ⟨2118884619740957464637369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412589746493971643091579 2118884619740957464637369)
        ·
          refine ⟨1589163464805718098478027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2118884619740957464637369 1589163464805718098478027)
          ·
            refine ⟨2383745197208577147717041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589163464805718098478027 2383745197208577147717041)
            ·
              refine ⟨1787808897906432860787781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383745197208577147717041 1787808897906432860787781)
              ·
                refine ⟨335214168357456161397709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1787808897906432860787781 335214168357456161397709)
                ·
                  refine ⟨125705313134046060524141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335214168357456161397709 125705313134046060524141)
                  ·
                    rfl

theorem cell21_550823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 4, 3].length) (baseStart_550823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550823 prefixEnd_550823 := by exact prefixLift 550823
  have htrace : WordTrace (prefixWord ++ tailWord_550823) baseStart_550823 baseEnd_550823 := by
    simpa [prefixWord, tailWord_550823, baseEnd_550823] using wordTrace_append hprefix tailTrace_550823
  have hstable : (prefixWord ++ tailWord_550823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550823).length < 2 ^ (prefixWord ++ tailWord_550823).sum := by decide
  have hdescent : baseEnd_550823 < baseStart_550823 := by decide
  rcases family_descends (prefixWord ++ tailWord_550823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550933 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 3]
def baseStart_550933 : Nat := 118140960795 + 550933 * 2 ^ 59
def prefixEnd_550933 : Nat := 4983230072969 + 3 ^ 40 * 550933 * 2
def baseEnd_550933 : Nat := 125730416632710313690583

theorem tailTrace_550933 : CollatzResearch.WordTrace tailWord_550933 prefixEnd_550933 125730416632710313690583 := by
  unfold tailWord_550933
  simp only [CollatzResearch.WordTrace]
  refine ⟨20094177313071307710473453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13396118208714205140315635 20094177313071307710473453)
  ·
    refine ⟨7535316492401740391427545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20094177313071307710473453 7535316492401740391427545)
    ·
      refine ⟨5651487369301305293570659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7535316492401740391427545 5651487369301305293570659)
      ·
        refine ⟨8477231053951957940355989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651487369301305293570659 8477231053951957940355989)
        ·
          refine ⟨397370205653998028454187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8477231053951957940355989 397370205653998028454187)
          ·
            refine ⟨596055308480997042681281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397370205653998028454187 596055308480997042681281)
            ·
              refine ⟨447041481360747782010961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596055308480997042681281 447041481360747782010961)
              ·
                refine ⟨335281111020560836508221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447041481360747782010961 335281111020560836508221)
                ·
                  refine ⟨125730416632710313690583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335281111020560836508221 125730416632710313690583)
                  ·
                    rfl

theorem cell21_550933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_550933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550933 prefixEnd_550933 := by exact prefixLift 550933
  have htrace : WordTrace (prefixWord ++ tailWord_550933) baseStart_550933 baseEnd_550933 := by
    simpa [prefixWord, tailWord_550933, baseEnd_550933] using wordTrace_append hprefix tailTrace_550933
  have hstable : (prefixWord ++ tailWord_550933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550933).length < 2 ^ (prefixWord ++ tailWord_550933).sum := by decide
  have hdescent : baseEnd_550933 < baseStart_550933 := by decide
  rcases family_descends (prefixWord ++ tailWord_550933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_550958 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_550958 : Nat := 118140960795 + 550958 * 2 ^ 59
def prefixEnd_550958 : Nat := 4983230072969 + 3 ^ 40 * 550958 * 2
def baseEnd_550958 : Nat := 125736121973315825773865

theorem tailTrace_550958 : CollatzResearch.WordTrace tailWord_550958 prefixEnd_550958 125736121973315825773865 := by
  unfold tailWord_550958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511886142247592122516691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13396726091987157986755685 2511886142247592122516691)
  ·
    refine ⟨3767829213371388183775037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2511886142247592122516691 3767829213371388183775037)
    ·
      refine ⟨1412935955014270568915639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3767829213371388183775037 1412935955014270568915639)
      ·
        refine ⟨2119403932521405853373459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412935955014270568915639 2119403932521405853373459)
        ·
          refine ⟨3179105898782108780060189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119403932521405853373459 3179105898782108780060189)
          ·
            refine ⟨1192164712043290792522571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3179105898782108780060189 1192164712043290792522571)
            ·
              refine ⟨1788247068064936188783857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192164712043290792522571 1788247068064936188783857)
              ·
                refine ⟨1341185301048702141587893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788247068064936188783857 1341185301048702141587893)
                ·
                  refine ⟨125736121973315825773865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1341185301048702141587893 125736121973315825773865)
                  ·
                    rfl

theorem cell21_550958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_550958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_550958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_550958 prefixEnd_550958 := by exact prefixLift 550958
  have htrace : WordTrace (prefixWord ++ tailWord_550958) baseStart_550958 baseEnd_550958 := by
    simpa [prefixWord, tailWord_550958, baseEnd_550958] using wordTrace_append hprefix tailTrace_550958
  have hstable : (prefixWord ++ tailWord_550958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_550958).length < 2 ^ (prefixWord ++ tailWord_550958).sum := by decide
  have hdescent : baseEnd_550958 < baseStart_550958 := by decide
  rcases family_descends (prefixWord ++ tailWord_550958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551031 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_551031 : Nat := 118140960795 + 551031 * 2 ^ 59
def prefixEnd_551031 : Nat := 4983230072969 + 3 ^ 40 * 551031 * 2
def baseEnd_551031 : Nat := 125752781567883921057049

theorem tailTrace_551031 : CollatzResearch.WordTrace tailWord_551031 prefixEnd_551031 125752781567883921057049 := by
  unfold tailWord_551031
  simp only [CollatzResearch.WordTrace]
  refine ⟨20097751666716270447540947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13398501111144180298360631 20097751666716270447540947)
  ·
    refine ⟨30146627500074405671311421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20097751666716270447540947 30146627500074405671311421)
    ·
      refine ⟨11304985312527902126741783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30146627500074405671311421 11304985312527902126741783)
      ·
        refine ⟨16957477968791853190112675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11304985312527902126741783 16957477968791853190112675)
        ·
          refine ⟨25436216953187779785169013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16957477968791853190112675 25436216953187779785169013)
          ·
            refine ⟨2384645339361354354859595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25436216953187779785169013 2384645339361354354859595)
            ·
              refine ⟨3576968009042031532289393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384645339361354354859595 3576968009042031532289393)
              ·
                refine ⟨2682726006781523649217045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3576968009042031532289393 2682726006781523649217045)
                ·
                  refine ⟨125752781567883921057049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2682726006781523649217045 125752781567883921057049)
                  ·
                    rfl

theorem cell21_551031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_551031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551031 prefixEnd_551031 := by exact prefixLift 551031
  have htrace : WordTrace (prefixWord ++ tailWord_551031) baseStart_551031 baseEnd_551031 := by
    simpa [prefixWord, tailWord_551031, baseEnd_551031] using wordTrace_append hprefix tailTrace_551031
  have hstable : (prefixWord ++ tailWord_551031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551031).length < 2 ^ (prefixWord ++ tailWord_551031).sum := by decide
  have hdescent : baseEnd_551031 < baseStart_551031 := by decide
  rcases family_descends (prefixWord ++ tailWord_551031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551048 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_551048 : Nat := 118140960795 + 551048 * 2 ^ 59
def prefixEnd_551048 : Nat := 4983230072969 + 3 ^ 40 * 551048 * 2
def baseEnd_551048 : Nat := 125756661199495669273681

theorem tailTrace_551048 : CollatzResearch.WordTrace tailWord_551048 prefixEnd_551048 125756661199495669273681 := by
  unfold tailWord_551048
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049185853827341175454899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13398914471769788233939865 10049185853827341175454899)
  ·
    refine ⟨15073778780741011763182349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10049185853827341175454899 15073778780741011763182349)
    ·
      refine ⟨5652667042777879411193381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15073778780741011763182349 5652667042777879411193381)
      ·
        refine ⟨1059875070520852389598759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5652667042777879411193381 1059875070520852389598759)
        ·
          refine ⟨1589812605781278584398139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1059875070520852389598759 1589812605781278584398139)
          ·
            refine ⟨2384718908671917876597209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589812605781278584398139 2384718908671917876597209)
            ·
              refine ⟨1788539181503938407447907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384718908671917876597209 1788539181503938407447907)
              ·
                refine ⟨2682808772255907611171861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788539181503938407447907 2682808772255907611171861)
                ·
                  refine ⟨125756661199495669273681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2682808772255907611171861 125756661199495669273681)
                  ·
                    rfl

theorem cell21_551048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_551048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551048 prefixEnd_551048 := by exact prefixLift 551048
  have htrace : WordTrace (prefixWord ++ tailWord_551048) baseStart_551048 baseEnd_551048 := by
    simpa [prefixWord, tailWord_551048, baseEnd_551048] using wordTrace_append hprefix tailTrace_551048
  have hstable : (prefixWord ++ tailWord_551048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551048).length < 2 ^ (prefixWord ++ tailWord_551048).sum := by decide
  have hdescent : baseEnd_551048 < baseStart_551048 := by decide
  rcases family_descends (prefixWord ++ tailWord_551048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551169 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_551169 : Nat := 118140960795 + 551169 * 2 ^ 59
def prefixEnd_551169 : Nat := 4983230072969 + 3 ^ 40 * 551169 * 2
def baseEnd_551169 : Nat := 125784275048026347756767

theorem tailTrace_551169 : CollatzResearch.WordTrace tailWord_551169 prefixEnd_551169 125784275048026347756767 := by
  unfold tailWord_551169
  simp only [CollatzResearch.WordTrace]
  refine ⟨20102784940216320016064561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13401856626810880010709707 20102784940216320016064561)
  ·
    refine ⟨15077088705162240012048421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20102784940216320016064561 15077088705162240012048421)
    ·
      refine ⟨2826954132217920002259079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15077088705162240012048421 2826954132217920002259079)
      ·
        refine ⟨4240431198326880003388619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2826954132217920002259079 4240431198326880003388619)
        ·
          refine ⟨6360646797490320005082929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4240431198326880003388619 6360646797490320005082929)
          ·
            refine ⟨4770485098117740003812197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6360646797490320005082929 4770485098117740003812197)
            ·
              refine ⟨894465955897076250714787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4770485098117740003812197 894465955897076250714787)
              ·
                refine ⟨1341698933845614376072181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894465955897076250714787 1341698933845614376072181)
                ·
                  refine ⟨125784275048026347756767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1341698933845614376072181 125784275048026347756767)
                  ·
                    rfl

theorem cell21_551169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_551169 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551169 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551169 prefixEnd_551169 := by exact prefixLift 551169
  have htrace : WordTrace (prefixWord ++ tailWord_551169) baseStart_551169 baseEnd_551169 := by
    simpa [prefixWord, tailWord_551169, baseEnd_551169] using wordTrace_append hprefix tailTrace_551169
  have hstable : (prefixWord ++ tailWord_551169).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551169).length < 2 ^ (prefixWord ++ tailWord_551169).sum := by decide
  have hdescent : baseEnd_551169 < baseStart_551169 := by decide
  rcases family_descends (prefixWord ++ tailWord_551169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551183 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_551183 : Nat := 118140960795 + 551183 * 2 ^ 59
def prefixEnd_551183 : Nat := 4983230072969 + 3 ^ 40 * 551183 * 2
def baseEnd_551183 : Nat := 125787470038765434523405

theorem tailTrace_551183 : CollatzResearch.WordTrace tailWord_551183 prefixEnd_551183 125787470038765434523405 := by
  unfold tailWord_551183
  simp only [CollatzResearch.WordTrace]
  refine ⟨20103295562165600407074203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13402197041443733604716135 20103295562165600407074203)
  ·
    refine ⟨30154943343248400610611305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20103295562165600407074203 30154943343248400610611305)
    ·
      refine ⟨22616207507436300457958479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30154943343248400610611305 22616207507436300457958479)
      ·
        refine ⟨33924311261154450686937719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22616207507436300457958479 33924311261154450686937719)
        ·
          refine ⟨50886466891731676030406579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33924311261154450686937719 50886466891731676030406579)
          ·
            refine ⟨76329700337597514045609869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50886466891731676030406579 76329700337597514045609869)
            ·
              refine ⟨28623637626599067767103701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76329700337597514045609869 28623637626599067767103701)
              ·
                refine ⟨670866506873415650791493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 28623637626599067767103701 670866506873415650791493)
                ·
                  refine ⟨125787470038765434523405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670866506873415650791493 125787470038765434523405)
                  ·
                    rfl

theorem cell21_551183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_551183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551183 prefixEnd_551183 := by exact prefixLift 551183
  have htrace : WordTrace (prefixWord ++ tailWord_551183) baseStart_551183 baseEnd_551183 := by
    simpa [prefixWord, tailWord_551183, baseEnd_551183] using wordTrace_append hprefix tailTrace_551183
  have hstable : (prefixWord ++ tailWord_551183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551183).length < 2 ^ (prefixWord ++ tailWord_551183).sum := by decide
  have hdescent : baseEnd_551183 < baseStart_551183 := by decide
  rcases family_descends (prefixWord ++ tailWord_551183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551220 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 3]
def baseStart_551220 : Nat := 118140960795 + 551220 * 2 ^ 59
def prefixEnd_551220 : Nat := 4983230072969 + 3 ^ 40 * 551220 * 2
def baseEnd_551220 : Nat := 125795913942861592406663

theorem tailTrace_551220 : CollatzResearch.WordTrace tailWord_551220 prefixEnd_551220 125795913942861592406663 := by
  unfold tailWord_551220
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052322531515777863085557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13403096708687703817447409 10052322531515777863085557)
  ·
    refine ⟨942405237329604174664271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10052322531515777863085557 942405237329604174664271)
    ·
      refine ⟨1413607855994406261996407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942405237329604174664271 1413607855994406261996407)
      ·
        refine ⟨2120411783991609392994611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413607855994406261996407 2120411783991609392994611)
        ·
          refine ⟨3180617675987414089491917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120411783991609392994611 3180617675987414089491917)
          ·
            refine ⟨1192731628495280283559469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3180617675987414089491917 1192731628495280283559469)
            ·
              refine ⟨447274360685730106334801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192731628495280283559469 447274360685730106334801)
              ·
                refine ⟨335455770514297579751101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447274360685730106334801 335455770514297579751101)
                ·
                  refine ⟨125795913942861592406663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335455770514297579751101 125795913942861592406663)
                  ·
                    rfl

theorem cell21_551220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_551220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551220 prefixEnd_551220 := by exact prefixLift 551220
  have htrace : WordTrace (prefixWord ++ tailWord_551220) baseStart_551220 baseEnd_551220 := by
    simpa [prefixWord, tailWord_551220, baseEnd_551220] using wordTrace_append hprefix tailTrace_551220
  have hstable : (prefixWord ++ tailWord_551220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551220).length < 2 ^ (prefixWord ++ tailWord_551220).sum := by decide
  have hdescent : baseEnd_551220 < baseStart_551220 := by decide
  rcases family_descends (prefixWord ++ tailWord_551220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551372 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_551372 : Nat := 118140960795 + 551372 * 2 ^ 59
def prefixEnd_551372 : Nat := 4983230072969 + 3 ^ 40 * 551372 * 2
def baseEnd_551372 : Nat := 125830602413743105873019

theorem tailTrace_551372 : CollatzResearch.WordTrace tailWord_551372 prefixEnd_551372 125830602413743105873019 := by
  unfold tailWord_551372
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055094479240442842852185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13406792638987257123802913 10055094479240442842852185)
  ·
    refine ⟨7541320859430332132139139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10055094479240442842852185 7541320859430332132139139)
    ·
      refine ⟨11311981289145498198208709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541320859430332132139139 11311981289145498198208709)
      ·
        refine ⟨2120996491714780912164133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11311981289145498198208709 2120996491714780912164133)
        ·
          refine ⟨397686842196521421030775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2120996491714780912164133 397686842196521421030775)
          ·
            refine ⟨596530263294782131546163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397686842196521421030775 596530263294782131546163)
            ·
              refine ⟨894795394942173197319245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596530263294782131546163 894795394942173197319245)
              ·
                refine ⟨335548273103314948994717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 894795394942173197319245 335548273103314948994717)
                ·
                  refine ⟨125830602413743105873019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335548273103314948994717 125830602413743105873019)
                  ·
                    rfl

theorem cell21_551372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_551372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551372 prefixEnd_551372 := by exact prefixLift 551372
  have htrace : WordTrace (prefixWord ++ tailWord_551372) baseStart_551372 baseEnd_551372 := by
    simpa [prefixWord, tailWord_551372, baseEnd_551372] using wordTrace_append hprefix tailTrace_551372
  have hstable : (prefixWord ++ tailWord_551372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551372).length < 2 ^ (prefixWord ++ tailWord_551372).sum := by decide
  have hdescent : baseEnd_551372 < baseStart_551372 := by decide
  rcases family_descends (prefixWord ++ tailWord_551372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551411 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_551411 : Nat := 118140960795 + 551411 * 2 ^ 59
def prefixEnd_551411 : Nat := 4983230072969 + 3 ^ 40 * 551411 * 2
def baseEnd_551411 : Nat := 125839502745087704722939

theorem tailTrace_551411 : CollatzResearch.WordTrace tailWord_551411 prefixEnd_551411 125839502745087704722939 := by
  unfold tailWord_551411
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111611405339595346374087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13407740936893063564249391 20111611405339595346374087)
  ·
    refine ⟨30167417108009393019561131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20111611405339595346374087 30167417108009393019561131)
    ·
      refine ⟨45251125662014089529341697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30167417108009393019561131 45251125662014089529341697)
      ·
        refine ⟨33938344246510567147006273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45251125662014089529341697 33938344246510567147006273)
        ·
          refine ⟨25453758184882925360254705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33938344246510567147006273 25453758184882925360254705)
          ·
            refine ⟨19090318638662194020191029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25453758184882925360254705 19090318638662194020191029)
            ·
              refine ⟨1789717372374580689392909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19090318638662194020191029 1789717372374580689392909)
              ·
                refine ⟨671144014640467758522341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789717372374580689392909 671144014640467758522341)
                ·
                  refine ⟨125839502745087704722939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671144014640467758522341 125839502745087704722939)
                  ·
                    rfl

theorem cell21_551411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_551411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551411 prefixEnd_551411 := by exact prefixLift 551411
  have htrace : WordTrace (prefixWord ++ tailWord_551411) baseStart_551411 baseEnd_551411 := by
    simpa [prefixWord, tailWord_551411, baseEnd_551411] using wordTrace_append hprefix tailTrace_551411
  have hstable : (prefixWord ++ tailWord_551411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551411).length < 2 ^ (prefixWord ++ tailWord_551411).sum := by decide
  have hdescent : baseEnd_551411 < baseStart_551411 := by decide
  rcases family_descends (prefixWord ++ tailWord_551411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551532 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 5]
def baseStart_551532 : Nat := 118140960795 + 551532 * 2 ^ 59
def prefixEnd_551532 : Nat := 4983230072969 + 3 ^ 40 * 551532 * 2
def baseEnd_551532 : Nat := 125867116593618383206025

theorem tailTrace_551532 : CollatzResearch.WordTrace tailWord_551532 prefixEnd_551532 125867116593618383206025 := by
  unfold tailWord_551532
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058012318950616505764425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13410683091934155341019233 10058012318950616505764425)
  ·
    refine ⟨7543509239212962379323319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058012318950616505764425 7543509239212962379323319)
    ·
      refine ⟨11315263858819443568984979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543509239212962379323319 11315263858819443568984979)
      ·
        refine ⟨16972895788229165353477469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11315263858819443568984979 16972895788229165353477469)
        ·
          refine ⟨6364835920585937007554051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16972895788229165353477469 6364835920585937007554051)
          ·
            refine ⟨9547253880878905511331077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6364835920585937007554051 9547253880878905511331077)
            ·
              refine ⟨1790110102664794783374577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9547253880878905511331077 1790110102664794783374577)
              ·
                refine ⟨1342582576998596087530933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790110102664794783374577 1342582576998596087530933)
                ·
                  refine ⟨125867116593618383206025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1342582576998596087530933 125867116593618383206025)
                  ·
                    rfl

theorem cell21_551532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_551532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551532 prefixEnd_551532 := by exact prefixLift 551532
  have htrace : WordTrace (prefixWord ++ tailWord_551532) baseStart_551532 baseEnd_551532 := by
    simpa [prefixWord, tailWord_551532, baseEnd_551532] using wordTrace_append hprefix tailTrace_551532
  have hstable : (prefixWord ++ tailWord_551532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551532).length < 2 ^ (prefixWord ++ tailWord_551532).sum := by decide
  have hdescent : baseEnd_551532 < baseStart_551532 := by decide
  rcases family_descends (prefixWord ++ tailWord_551532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551577 : List Nat := [1, 2, 1, 2, 1, 2, 6, 6]
def baseStart_551577 : Nat := 118140960795 + 551577 * 2 ^ 59
def prefixEnd_551577 : Nat := 4983230072969 + 3 ^ 40 * 551577 * 2
def baseEnd_551577 : Nat := 41959128735569434985311

theorem tailTrace_551577 : CollatzResearch.WordTrace tailWord_551577 prefixEnd_551577 41959128735569434985311 := by
  unfold tailWord_551577
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117665922738205696916985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13411777281825470464611323 20117665922738205696916985)
  ·
    refine ⟨15088249442053654272687739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20117665922738205696916985 15088249442053654272687739)
    ·
      refine ⟨22632374163080481409031609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15088249442053654272687739 22632374163080481409031609)
      ·
        refine ⟨16974280622310361056773707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22632374163080481409031609 16974280622310361056773707)
        ·
          refine ⟨25461420933465541585160561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16974280622310361056773707 25461420933465541585160561)
          ·
            refine ⟨19096065700099156188870421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25461420933465541585160561 19096065700099156188870421)
            ·
              refine ⟨895128079692147946353301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19096065700099156188870421 895128079692147946353301)
              ·
                refine ⟨41959128735569434985311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 895128079692147946353301 41959128735569434985311)
                ·
                  rfl

theorem cell21_551577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_551577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551577 prefixEnd_551577 := by exact prefixLift 551577
  have htrace : WordTrace (prefixWord ++ tailWord_551577) baseStart_551577 baseEnd_551577 := by
    simpa [prefixWord, tailWord_551577, baseEnd_551577] using wordTrace_append hprefix tailTrace_551577
  have hstable : (prefixWord ++ tailWord_551577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551577).length < 2 ^ (prefixWord ++ tailWord_551577).sum := by decide
  have hdescent : baseEnd_551577 < baseStart_551577 := by decide
  rcases family_descends (prefixWord ++ tailWord_551577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551580 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 4]
def baseStart_551580 : Nat := 118140960795 + 551580 * 2 ^ 59
def prefixEnd_551580 : Nat := 4983230072969 + 3 ^ 40 * 551580 * 2
def baseEnd_551580 : Nat := 125878070847580966405927

theorem tailTrace_551580 : CollatzResearch.WordTrace tailWord_551580 prefixEnd_551580 125878070847580966405927 := by
  unfold tailWord_551580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058887670863668604638097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13411850227818224806184129 10058887670863668604638097)
  ·
    refine ⟨7544165753147751453478573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058887670863668604638097 7544165753147751453478573)
    ·
      refine ⟨2829062157430406795054465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7544165753147751453478573 2829062157430406795054465)
      ·
        refine ⟨2121796618072805096290849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2829062157430406795054465 2121796618072805096290849)
        ·
          refine ⟨1591347463554603822218137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2121796618072805096290849 1591347463554603822218137)
          ·
            refine ⟨1193510597665952866663603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591347463554603822218137 1193510597665952866663603)
            ·
              refine ⟨1790265896498929299995405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193510597665952866663603 1790265896498929299995405)
              ·
                refine ⟨671349711187098487498277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1790265896498929299995405 671349711187098487498277)
                ·
                  refine ⟨125878070847580966405927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671349711187098487498277 125878070847580966405927)
                  ·
                    rfl

theorem cell21_551580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_551580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551580 prefixEnd_551580 := by exact prefixLift 551580
  have htrace : WordTrace (prefixWord ++ tailWord_551580) baseStart_551580 baseEnd_551580 := by
    simpa [prefixWord, tailWord_551580, baseEnd_551580] using wordTrace_append hprefix tailTrace_551580
  have hstable : (prefixWord ++ tailWord_551580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551580).length < 2 ^ (prefixWord ++ tailWord_551580).sum := by decide
  have hdescent : baseEnd_551580 < baseStart_551580 := by decide
  rcases family_descends (prefixWord ++ tailWord_551580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551617 : List Nat := [1, 2, 6, 2, 1, 2, 2, 2, 3]
def baseStart_551617 : Nat := 118140960795 + 551617 * 2 ^ 59
def prefixEnd_551617 : Nat := 4983230072969 + 3 ^ 40 * 551617 * 2
def baseEnd_551617 : Nat := 125886514751677124289185

theorem tailTrace_551617 : CollatzResearch.WordTrace tailWord_551617 prefixEnd_551617 125886514751677124289185 := by
  unfold tailWord_551617
  simp only [CollatzResearch.WordTrace]
  refine ⟨20119124842593292528373105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13412749895062195018915403 20119124842593292528373105)
  ·
    refine ⟨15089343631944969396279829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20119124842593292528373105 15089343631944969396279829)
    ·
      refine ⟨707312982747420440450617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15089343631944969396279829 707312982747420440450617)
      ·
        refine ⟨530484737060565330337963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 707312982747420440450617 530484737060565330337963)
        ·
          refine ⟨795727105590847995506945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530484737060565330337963 795727105590847995506945)
          ·
            refine ⟨596795329193135996630209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795727105590847995506945 596795329193135996630209)
            ·
              refine ⟨447596496894851997472657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596795329193135996630209 447596496894851997472657)
              ·
                refine ⟨335697372671138998104493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447596496894851997472657 335697372671138998104493)
                ·
                  refine ⟨125886514751677124289185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335697372671138998104493 125886514751677124289185)
                  ·
                    rfl

theorem cell21_551617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2, 3].length) (baseStart_551617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551617 prefixEnd_551617 := by exact prefixLift 551617
  have htrace : WordTrace (prefixWord ++ tailWord_551617) baseStart_551617 baseEnd_551617 := by
    simpa [prefixWord, tailWord_551617, baseEnd_551617] using wordTrace_append hprefix tailTrace_551617
  have hstable : (prefixWord ++ tailWord_551617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551617).length < 2 ^ (prefixWord ++ tailWord_551617).sum := by decide
  have hdescent : baseEnd_551617 < baseStart_551617 := by decide
  rcases family_descends (prefixWord ++ tailWord_551617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551639 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_551639 : Nat := 118140960795 + 551639 * 2 ^ 59
def prefixEnd_551639 : Nat := 4983230072969 + 3 ^ 40 * 551639 * 2
def baseEnd_551639 : Nat := 125891535451409974922473

theorem tailTrace_551639 : CollatzResearch.WordTrace tailWord_551639 prefixEnd_551639 125891535451409974922473 := by
  unfold tailWord_551639
  simp only [CollatzResearch.WordTrace]
  refine ⟨20119927248513590285673971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13413284832342393523782647 20119927248513590285673971)
  ·
    refine ⟨30179890872770385428510957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20119927248513590285673971 30179890872770385428510957)
    ·
      refine ⟨11317459077288894535691609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30179890872770385428510957 11317459077288894535691609)
      ·
        refine ⟨8488094307966670901768707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11317459077288894535691609 8488094307966670901768707)
        ·
          refine ⟨12732141461950006352653061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488094307966670901768707 12732141461950006352653061)
          ·
            refine ⟨2387276524115626191122449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12732141461950006352653061 2387276524115626191122449)
            ·
              refine ⟨1790457393086719643341837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387276524115626191122449 1790457393086719643341837)
              ·
                refine ⟨671421522407519866253189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1790457393086719643341837 671421522407519866253189)
                ·
                  refine ⟨125891535451409974922473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671421522407519866253189 125891535451409974922473)
                  ·
                    rfl

theorem cell21_551639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_551639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551639 prefixEnd_551639 := by exact prefixLift 551639
  have htrace : WordTrace (prefixWord ++ tailWord_551639) baseStart_551639 baseEnd_551639 := by
    simpa [prefixWord, tailWord_551639, baseEnd_551639] using wordTrace_append hprefix tailTrace_551639
  have hstable : (prefixWord ++ tailWord_551639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551639).length < 2 ^ (prefixWord ++ tailWord_551639).sum := by decide
  have hdescent : baseEnd_551639 < baseStart_551639 := by decide
  rcases family_descends (prefixWord ++ tailWord_551639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551667 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_551667 : Nat := 118140960795 + 551667 * 2 ^ 59
def prefixEnd_551667 : Nat := 4983230072969 + 3 ^ 40 * 551667 * 2
def baseEnd_551667 : Nat := 125897925432888148455749

theorem tailTrace_551667 : CollatzResearch.WordTrace tailWord_551667 prefixEnd_551667 125897925432888148455749 := by
  unfold tailWord_551667
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120948492412151067693255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13413965661608100711795503 20120948492412151067693255)
  ·
    refine ⟨30181422738618226601539883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20120948492412151067693255 30181422738618226601539883)
    ·
      refine ⟨45272134107927339902309825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30181422738618226601539883 45272134107927339902309825)
      ·
        refine ⟨33954100580945504926732369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45272134107927339902309825 33954100580945504926732369)
        ·
          refine ⟨25465575435709128695049277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33954100580945504926732369 25465575435709128695049277)
          ·
            refine ⟨9549590788390923260643479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25465575435709128695049277 9549590788390923260643479)
            ·
              refine ⟨14324386182586384890965219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9549590788390923260643479 14324386182586384890965219)
              ·
                refine ⟨21486579273879577336447829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14324386182586384890965219 21486579273879577336447829)
                ·
                  refine ⟨125897925432888148455749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21486579273879577336447829 125897925432888148455749)
                  ·
                    rfl

theorem cell21_551667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_551667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551667 prefixEnd_551667 := by exact prefixLift 551667
  have htrace : WordTrace (prefixWord ++ tailWord_551667) baseStart_551667 baseEnd_551667 := by
    simpa [prefixWord, tailWord_551667, baseEnd_551667] using wordTrace_append hprefix tailTrace_551667
  have hstable : (prefixWord ++ tailWord_551667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551667).length < 2 ^ (prefixWord ++ tailWord_551667).sum := by decide
  have hdescent : baseEnd_551667 < baseStart_551667 := by decide
  rcases family_descends (prefixWord ++ tailWord_551667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551794 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 3]
def baseStart_551794 : Nat := 118140960795 + 551794 * 2 ^ 59
def prefixEnd_551794 : Nat := 4983230072969 + 3 ^ 40 * 551794 * 2
def baseEnd_551794 : Nat := 125926908563164149838823

theorem tailTrace_551794 : CollatzResearch.WordTrace tailWord_551794 prefixEnd_551794 125926908563164149838823 := by
  unfold tailWord_551794
  simp only [CollatzResearch.WordTrace]
  refine ⟨5031395140738012939391609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13417053708634701171710957 5031395140738012939391609)
  ·
    refine ⟨3773546355553509704543707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5031395140738012939391609 3773546355553509704543707)
    ·
      refine ⟨5660319533330264556815561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773546355553509704543707 5660319533330264556815561)
      ·
        refine ⟨4245239649997698417611671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5660319533330264556815561 4245239649997698417611671)
        ·
          refine ⟨6367859474996547626417507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245239649997698417611671 6367859474996547626417507)
          ·
            refine ⟨9551789212494821439626261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367859474996547626417507 9551789212494821439626261)
            ·
              refine ⟨447740119335694754982481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9551789212494821439626261 447740119335694754982481)
              ·
                refine ⟨335805089501771066236861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 447740119335694754982481 335805089501771066236861)
                ·
                  refine ⟨125926908563164149838823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335805089501771066236861 125926908563164149838823)
                  ·
                    rfl

theorem cell21_551794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_551794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551794 prefixEnd_551794 := by exact prefixLift 551794
  have htrace : WordTrace (prefixWord ++ tailWord_551794) baseStart_551794 baseEnd_551794 := by
    simpa [prefixWord, tailWord_551794, baseEnd_551794] using wordTrace_append hprefix tailTrace_551794
  have hstable : (prefixWord ++ tailWord_551794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551794).length < 2 ^ (prefixWord ++ tailWord_551794).sum := by decide
  have hdescent : baseEnd_551794 < baseStart_551794 := by decide
  rcases family_descends (prefixWord ++ tailWord_551794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551805 : List Nat := [1, 4, 1, 1, 2, 1, 5, 6]
def baseStart_551805 : Nat := 118140960795 + 551805 * 2 ^ 59
def prefixEnd_551805 : Nat := 4983230072969 + 3 ^ 40 * 551805 * 2
def baseEnd_551805 : Nat := 41976472971010191718489

theorem tailTrace_551805 : CollatzResearch.WordTrace tailWord_551805 prefixEnd_551805 41976472971010191718489 := by
  unfold tailWord_551805
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125981765912200636216869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13417321177274800424144579 20125981765912200636216869)
  ·
    refine ⟨3773621581108537619290663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20125981765912200636216869 3773621581108537619290663)
    ·
      refine ⟨5660432371662806428935995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773621581108537619290663 5660432371662806428935995)
      ·
        refine ⟨8490648557494209643403993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5660432371662806428935995 8490648557494209643403993)
        ·
          refine ⟨6367986418120657232552995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8490648557494209643403993 6367986418120657232552995)
          ·
            refine ⟨9551979627180985848829493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367986418120657232552995 9551979627180985848829493)
            ·
              refine ⟨895498090048217423327765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9551979627180985848829493 895498090048217423327765)
              ·
                refine ⟨41976472971010191718489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 895498090048217423327765 41976472971010191718489)
                ·
                  rfl

theorem cell21_551805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_551805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551805 prefixEnd_551805 := by exact prefixLift 551805
  have htrace : WordTrace (prefixWord ++ tailWord_551805) baseStart_551805 baseEnd_551805 := by
    simpa [prefixWord, tailWord_551805, baseEnd_551805] using wordTrace_append hprefix tailTrace_551805
  have hstable : (prefixWord ++ tailWord_551805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551805).length < 2 ^ (prefixWord ++ tailWord_551805).sum := by decide
  have hdescent : baseEnd_551805 < baseStart_551805 := by decide
  rcases family_descends (prefixWord ++ tailWord_551805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551819 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_551819 : Nat := 118140960795 + 551819 * 2 ^ 59
def prefixEnd_551819 : Nat := 4983230072969 + 3 ^ 40 * 551819 * 2
def baseEnd_551819 : Nat := 125932613903769661922105

theorem tailTrace_551819 : CollatzResearch.WordTrace tailWord_551819 prefixEnd_551819 125932613903769661922105 := by
  unfold tailWord_551819
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126492387861481027226511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13417661591907654018151007 20126492387861481027226511)
  ·
    refine ⟨30189738581792221540839767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20126492387861481027226511 30189738581792221540839767)
    ·
      refine ⟨45284607872688332311259651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30189738581792221540839767 45284607872688332311259651)
      ·
        refine ⟨67926911809032498466889477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45284607872688332311259651 67926911809032498466889477)
        ·
          refine ⟨12736295964193593462541777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67926911809032498466889477 12736295964193593462541777)
          ·
            refine ⟨9552221973145195096906333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12736295964193593462541777 9552221973145195096906333)
            ·
              refine ⟨3582083239929448161339875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9552221973145195096906333 3582083239929448161339875)
              ·
                refine ⟨5373124859894172242009813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582083239929448161339875 5373124859894172242009813)
                ·
                  refine ⟨125932613903769661922105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5373124859894172242009813 125932613903769661922105)
                  ·
                    rfl

theorem cell21_551819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_551819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551819 prefixEnd_551819 := by exact prefixLift 551819
  have htrace : WordTrace (prefixWord ++ tailWord_551819) baseStart_551819 baseEnd_551819 := by
    simpa [prefixWord, tailWord_551819, baseEnd_551819] using wordTrace_append hprefix tailTrace_551819
  have hstable : (prefixWord ++ tailWord_551819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551819).length < 2 ^ (prefixWord ++ tailWord_551819).sum := by decide
  have hdescent : baseEnd_551819 < baseStart_551819 := by decide
  rcases family_descends (prefixWord ++ tailWord_551819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551912 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_551912 : Nat := 118140960795 + 551912 * 2 ^ 59
def prefixEnd_551912 : Nat := 4983230072969 + 3 ^ 40 * 551912 * 2
def baseEnd_551912 : Nat := 125953837770822166871915

theorem tailTrace_551912 : CollatzResearch.WordTrace tailWord_551912 prefixEnd_551912 125953837770822166871915 := by
  unfold tailWord_551912
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064942188262278955180995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13419922917683038606907993 10064942188262278955180995)
  ·
    refine ⟨15097413282393418432771493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10064942188262278955180995 15097413282393418432771493)
    ·
      refine ⟨2830764990448765956144655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15097413282393418432771493 2830764990448765956144655)
      ·
        refine ⟨4246147485673148934216983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830764990448765956144655 4246147485673148934216983)
        ·
          refine ⟨6369221228509723401325475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246147485673148934216983 6369221228509723401325475)
          ·
            refine ⟨9553831842764585101988213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369221228509723401325475 9553831842764585101988213)
            ·
              refine ⟨895671735259179853311395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9553831842764585101988213 895671735259179853311395)
              ·
                refine ⟨1343507602888769779967093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895671735259179853311395 1343507602888769779967093)
                ·
                  refine ⟨125953837770822166871915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1343507602888769779967093 125953837770822166871915)
                  ·
                    rfl

theorem cell21_551912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_551912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551912 prefixEnd_551912 := by exact prefixLift 551912
  have htrace : WordTrace (prefixWord ++ tailWord_551912) baseStart_551912 baseEnd_551912 := by
    simpa [prefixWord, tailWord_551912, baseEnd_551912] using wordTrace_append hprefix tailTrace_551912
  have hstable : (prefixWord ++ tailWord_551912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551912).length < 2 ^ (prefixWord ++ tailWord_551912).sum := by decide
  have hdescent : baseEnd_551912 < baseStart_551912 := by decide
  rcases family_descends (prefixWord ++ tailWord_551912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_551918 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_551918 : Nat := 118140960795 + 551918 * 2 ^ 59
def prefixEnd_551918 : Nat := 4983230072969 + 3 ^ 40 * 551918 * 2
def baseEnd_551918 : Nat := 125955207052567489771903

theorem tailTrace_551918 : CollatzResearch.WordTrace tailWord_551918 prefixEnd_551918 125955207052567489771903 := by
  unfold tailWord_551918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516262901812852616885051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13420068809668547290053605 2516262901812852616885051)
  ·
    refine ⟨3774394352719278925327577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2516262901812852616885051 3774394352719278925327577)
    ·
      refine ⟨2830795764539459193995683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3774394352719278925327577 2830795764539459193995683)
      ·
        refine ⟨4246193646809188790993525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830795764539459193995683 4246193646809188790993525)
        ·
          refine ⟨398080654388361449155643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4246193646809188790993525 398080654388361449155643)
          ·
            refine ⟨597120981582542173733465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398080654388361449155643 597120981582542173733465)
            ·
              refine ⟨447840736186906630300099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597120981582542173733465 447840736186906630300099)
              ·
                refine ⟨671761104280359945450149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447840736186906630300099 671761104280359945450149)
                ·
                  refine ⟨125955207052567489771903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 671761104280359945450149 125955207052567489771903)
                  ·
                    rfl

theorem cell21_551918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_551918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_551918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_551918 prefixEnd_551918 := by exact prefixLift 551918
  have htrace : WordTrace (prefixWord ++ tailWord_551918) baseStart_551918 baseEnd_551918 := by
    simpa [prefixWord, tailWord_551918, baseEnd_551918] using wordTrace_append hprefix tailTrace_551918
  have hstable : (prefixWord ++ tailWord_551918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_551918).length < 2 ^ (prefixWord ++ tailWord_551918).sum := by decide
  have hdescent : baseEnd_551918 < baseStart_551918 := by decide
  rcases family_descends (prefixWord ++ tailWord_551918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552047 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_552047 : Nat := 118140960795 + 552047 * 2 ^ 59
def prefixEnd_552047 : Nat := 4983230072969 + 3 ^ 40 * 552047 * 2
def baseEnd_552047 : Nat := 125984646610091932121639

theorem tailTrace_552047 : CollatzResearch.WordTrace tailWord_552047 prefixEnd_552047 125984646610091932121639 := by
  unfold tailWord_552047
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134808231035475966526395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13423205487356983977684263 20134808231035475966526395)
  ·
    refine ⟨30202212346553213949789593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20134808231035475966526395 30202212346553213949789593)
    ·
      refine ⟨22651659259914910462342195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30202212346553213949789593 22651659259914910462342195)
      ·
        refine ⟨33977488889872365693513293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22651659259914910462342195 33977488889872365693513293)
        ·
          refine ⟨12741558333702137135067485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33977488889872365693513293 12741558333702137135067485)
          ·
            refine ⟨4778084375138301425650307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12741558333702137135067485 4778084375138301425650307)
            ·
              refine ⟨7167126562707452138475461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778084375138301425650307 7167126562707452138475461)
              ·
                refine ⟨1343836230507647275964149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7167126562707452138475461 1343836230507647275964149)
                ·
                  refine ⟨125984646610091932121639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1343836230507647275964149 125984646610091932121639)
                  ·
                    rfl

theorem cell21_552047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_552047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552047 prefixEnd_552047 := by exact prefixLift 552047
  have htrace : WordTrace (prefixWord ++ tailWord_552047) baseStart_552047 baseEnd_552047 := by
    simpa [prefixWord, tailWord_552047, baseEnd_552047] using wordTrace_append hprefix tailTrace_552047
  have hstable : (prefixWord ++ tailWord_552047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552047).length < 2 ^ (prefixWord ++ tailWord_552047).sum := by decide
  have hdescent : baseEnd_552047 < baseStart_552047 := by decide
  rcases family_descends (prefixWord ++ tailWord_552047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552132 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_552132 : Nat := 118140960795 + 552132 * 2 ^ 59
def prefixEnd_552132 : Nat := 4983230072969 + 3 ^ 40 * 552132 * 2
def baseEnd_552132 : Nat := 126004044768150673204799

theorem tailTrace_552132 : CollatzResearch.WordTrace tailWord_552132 prefixEnd_552132 126004044768150673204799 := by
  unfold tailWord_552132
  simp only [CollatzResearch.WordTrace]
  refine ⟨10068954217863767741685325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13425272290485023655580433 10068954217863767741685325)
  ·
    refine ⟨3775857831698912903131997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10068954217863767741685325 3775857831698912903131997)
    ·
      refine ⟨1415946686887092338674499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3775857831698912903131997 1415946686887092338674499)
      ·
        refine ⟨2123920030330638508011749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415946686887092338674499 2123920030330638508011749)
        ·
          refine ⟨398235005686994720252203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2123920030330638508011749 398235005686994720252203)
          ·
            refine ⟨597352508530492080378305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398235005686994720252203 597352508530492080378305)
            ·
              refine ⟨448014381397869060283729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 597352508530492080378305 448014381397869060283729)
              ·
                refine ⟨336010786048401795212797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448014381397869060283729 336010786048401795212797)
                ·
                  refine ⟨126004044768150673204799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336010786048401795212797 126004044768150673204799)
                  ·
                    rfl

theorem cell21_552132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_552132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552132 prefixEnd_552132 := by exact prefixLift 552132
  have htrace : WordTrace (prefixWord ++ tailWord_552132) baseStart_552132 baseEnd_552132 := by
    simpa [prefixWord, tailWord_552132, baseEnd_552132] using wordTrace_append hprefix tailTrace_552132
  have hstable : (prefixWord ++ tailWord_552132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552132).length < 2 ^ (prefixWord ++ tailWord_552132).sum := by decide
  have hdescent : baseEnd_552132 < baseStart_552132 := by decide
  rcases family_descends (prefixWord ++ tailWord_552132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552137 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_552137 : Nat := 118140960795 + 552137 * 2 ^ 59
def prefixEnd_552137 : Nat := 4983230072969 + 3 ^ 40 * 552137 * 2
def baseEnd_552137 : Nat := 126005185836271775621455

theorem tailTrace_552137 : CollatzResearch.WordTrace tailWord_552137 prefixEnd_552137 126005185836271775621455 := by
  unfold tailWord_552137
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138090800709421337302665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13425393867139614224868443 20138090800709421337302665)
  ·
    refine ⟨15103568100532066002976999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20138090800709421337302665 15103568100532066002976999)
    ·
      refine ⟨22655352150798099004465499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15103568100532066002976999 22655352150798099004465499)
      ·
        refine ⟨33983028226197148506698249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22655352150798099004465499 33983028226197148506698249)
        ·
          refine ⟨25487271169647861380023687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33983028226197148506698249 25487271169647861380023687)
          ·
            refine ⟨38230906754471792070035531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25487271169647861380023687 38230906754471792070035531)
            ·
              refine ⟨57346360131707688105053297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38230906754471792070035531 57346360131707688105053297)
              ·
                refine ⟨43009770098780766078789973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57346360131707688105053297 43009770098780766078789973)
                ·
                  refine ⟨126005185836271775621455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 43009770098780766078789973 126005185836271775621455)
                  ·
                    rfl

theorem cell21_552137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_552137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552137 prefixEnd_552137 := by exact prefixLift 552137
  have htrace : WordTrace (prefixWord ++ tailWord_552137) baseStart_552137 baseEnd_552137 := by
    simpa [prefixWord, tailWord_552137, baseEnd_552137] using wordTrace_append hprefix tailTrace_552137
  have hstable : (prefixWord ++ tailWord_552137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552137).length < 2 ^ (prefixWord ++ tailWord_552137).sum := by decide
  have hdescent : baseEnd_552137 < baseStart_552137 := by decide
  rcases family_descends (prefixWord ++ tailWord_552137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552157 : List Nat := [1, 4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_552157 : Nat := 118140960795 + 552157 * 2 ^ 59
def prefixEnd_552157 : Nat := 4983230072969 + 3 ^ 40 * 552157 * 2
def baseEnd_552157 : Nat := 126009750108756185288081

theorem tailTrace_552157 : CollatzResearch.WordTrace tailWord_552157 prefixEnd_552157 126009750108756185288081 := by
  unfold tailWord_552157
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138820260636964753030725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13425880173757976502020483 20138820260636964753030725)
  ·
    refine ⟨3776028798869430891193261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20138820260636964753030725 3776028798869430891193261)
    ·
      refine ⟨1416010799576036584197473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3776028798869430891193261 1416010799576036584197473)
      ·
        refine ⟨1062008099682027438148105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1416010799576036584197473 1062008099682027438148105)
        ·
          refine ⟨796506074761520578611079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062008099682027438148105 796506074761520578611079)
          ·
            refine ⟨1194759112142280867916619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796506074761520578611079 1194759112142280867916619)
            ·
              refine ⟨1792138668213421301874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194759112142280867916619 1792138668213421301874929)
              ·
                refine ⟨1344104001160065976406197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792138668213421301874929 1344104001160065976406197)
                ·
                  refine ⟨126009750108756185288081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344104001160065976406197 126009750108756185288081)
                  ·
                    rfl

theorem cell21_552157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_552157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552157 prefixEnd_552157 := by exact prefixLift 552157
  have htrace : WordTrace (prefixWord ++ tailWord_552157) baseStart_552157 baseEnd_552157 := by
    simpa [prefixWord, tailWord_552157, baseEnd_552157] using wordTrace_append hprefix tailTrace_552157
  have hstable : (prefixWord ++ tailWord_552157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552157).length < 2 ^ (prefixWord ++ tailWord_552157).sum := by decide
  have hdescent : baseEnd_552157 < baseStart_552157 := by decide
  rcases family_descends (prefixWord ++ tailWord_552157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552188 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_552188 : Nat := 118140960795 + 552188 * 2 ^ 59
def prefixEnd_552188 : Nat := 4983230072969 + 3 ^ 40 * 552188 * 2
def baseEnd_552188 : Nat := 126016824731107020271351

theorem tailTrace_552188 : CollatzResearch.WordTrace tailWord_552188 prefixEnd_552188 126016824731107020271351 := by
  unfold tailWord_552188
  simp only [CollatzResearch.WordTrace]
  refine ⟨10069975461762328523704609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13426633949016438031606145 10069975461762328523704609)
  ·
    refine ⟨7552481596321746392778457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10069975461762328523704609 7552481596321746392778457)
    ·
      refine ⟨5664361197241309794583843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7552481596321746392778457 5664361197241309794583843)
      ·
        refine ⟨8496541795861964691875765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5664361197241309794583843 8496541795861964691875765)
        ·
          refine ⟨796550793362059189863353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8496541795861964691875765 796550793362059189863353)
          ·
            refine ⟨597413095021544392397515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796550793362059189863353 597413095021544392397515)
            ·
              refine ⟨896119642532316588596273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597413095021544392397515 896119642532316588596273)
              ·
                refine ⟨672089731899237441447205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 896119642532316588596273 672089731899237441447205)
                ·
                  refine ⟨126016824731107020271351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 672089731899237441447205 126016824731107020271351)
                  ·
                    rfl

theorem cell21_552188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_552188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552188 prefixEnd_552188 := by exact prefixLift 552188
  have htrace : WordTrace (prefixWord ++ tailWord_552188) baseStart_552188 baseEnd_552188 := by
    simpa [prefixWord, tailWord_552188, baseEnd_552188] using wordTrace_append hprefix tailTrace_552188
  have hstable : (prefixWord ++ tailWord_552188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552188).length < 2 ^ (prefixWord ++ tailWord_552188).sum := by decide
  have hdescent : baseEnd_552188 < baseStart_552188 := by decide
  rcases family_descends (prefixWord ++ tailWord_552188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552289 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_552289 : Nat := 118140960795 + 552289 * 2 ^ 59
def prefixEnd_552289 : Nat := 4983230072969 + 3 ^ 40 * 552289 * 2
def baseEnd_552289 : Nat := 126039874307153289087811

theorem tailTrace_552289 : CollatzResearch.WordTrace tailWord_552289 prefixEnd_552289 126039874307153289087811 := by
  unfold tailWord_552289
  simp only [CollatzResearch.WordTrace]
  refine ⟨20143634696158751296835921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13429089797439167531223947 20143634696158751296835921)
  ·
    refine ⟨15107726022119063472626941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20143634696158751296835921 15107726022119063472626941)
    ·
      refine ⟨5665397258294648802235103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15107726022119063472626941 5665397258294648802235103)
      ·
        refine ⟨8498095887441973203352655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5665397258294648802235103 8498095887441973203352655)
        ·
          refine ⟨12747143831162959805028983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498095887441973203352655 12747143831162959805028983)
          ·
            refine ⟨19120715746744439707543475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12747143831162959805028983 19120715746744439707543475)
            ·
              refine ⟨28681073620116659561315213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19120715746744439707543475 28681073620116659561315213)
              ·
                refine ⟨10755402607543747335493205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28681073620116659561315213 10755402607543747335493205)
                ·
                  refine ⟨126039874307153289087811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10755402607543747335493205 126039874307153289087811)
                  ·
                    rfl

theorem cell21_552289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_552289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552289 prefixEnd_552289 := by exact prefixLift 552289
  have htrace : WordTrace (prefixWord ++ tailWord_552289) baseStart_552289 baseEnd_552289 := by
    simpa [prefixWord, tailWord_552289, baseEnd_552289] using wordTrace_append hprefix tailTrace_552289
  have hstable : (prefixWord ++ tailWord_552289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552289).length < 2 ^ (prefixWord ++ tailWord_552289).sum := by decide
  have hdescent : baseEnd_552289 < baseStart_552289 := by decide
  rcases family_descends (prefixWord ++ tailWord_552289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552413 : List Nat := [1, 4, 3, 1, 1, 4, 7]
def baseStart_552413 : Nat := 118140960795 + 552413 * 2 ^ 59
def prefixEnd_552413 : Nat := 4983230072969 + 3 ^ 40 * 552413 * 2
def baseEnd_552413 : Nat := 14007574755172958780099

theorem tailTrace_552413 : CollatzResearch.WordTrace tailWord_552413 prefixEnd_552413 14007574755172958780099 := by
  unfold tailWord_552413
  simp only [CollatzResearch.WordTrace]
  refine ⟨20148157347709520474349893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13432104898473013649566595 20148157347709520474349893)
  ·
    refine ⟨3777779502695535088940605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20148157347709520474349893 3777779502695535088940605)
    ·
      refine ⟨1416667313510825658352727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3777779502695535088940605 1416667313510825658352727)
      ·
        refine ⟨2125000970266238487529091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416667313510825658352727 2125000970266238487529091)
        ·
          refine ⟨3187501455399357731293637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125000970266238487529091 3187501455399357731293637)
          ·
            refine ⟨597656522887379574617557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3187501455399357731293637 597656522887379574617557)
            ·
              refine ⟨14007574755172958780099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 597656522887379574617557 14007574755172958780099)
              ·
                rfl

theorem cell21_552413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 7].length) (baseStart_552413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552413 prefixEnd_552413 := by exact prefixLift 552413
  have htrace : WordTrace (prefixWord ++ tailWord_552413) baseStart_552413 baseEnd_552413 := by
    simpa [prefixWord, tailWord_552413, baseEnd_552413] using wordTrace_append hprefix tailTrace_552413
  have hstable : (prefixWord ++ tailWord_552413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552413).length < 2 ^ (prefixWord ++ tailWord_552413).sum := by decide
  have hdescent : baseEnd_552413 < baseStart_552413 := by decide
  rcases family_descends (prefixWord ++ tailWord_552413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552472 : List Nat := [2, 1, 2, 3, 4, 9]
def baseStart_552472 : Nat := 118140960795 + 552472 * 2 ^ 59
def prefixEnd_552472 : Nat := 4983230072969 + 3 ^ 40 * 552472 * 2
def baseEnd_552472 : Nat := 4669690274088356945831

theorem tailTrace_552472 : CollatzResearch.WordTrace tailWord_552472 prefixEnd_552472 4669690274088356945831 := by
  unfold tailWord_552472
  simp only [CollatzResearch.WordTrace]
  refine ⟨10075154627247886775373835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13433539502997182367165113 10075154627247886775373835)
  ·
    refine ⟨15112731940871830163060753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10075154627247886775373835 15112731940871830163060753)
    ·
      refine ⟨11334548955653872622295565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15112731940871830163060753 11334548955653872622295565)
      ·
        refine ⟨4250455858370202233360837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11334548955653872622295565 4250455858370202233360837)
        ·
          refine ⟨796960473444412918755157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4250455858370202233360837 796960473444412918755157)
          ·
            refine ⟨4669690274088356945831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 796960473444412918755157 4669690274088356945831)
            ·
              rfl

theorem cell21_552472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 9].length) (baseStart_552472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552472 prefixEnd_552472 := by exact prefixLift 552472
  have htrace : WordTrace (prefixWord ++ tailWord_552472) baseStart_552472 baseEnd_552472 := by
    simpa [prefixWord, tailWord_552472, baseEnd_552472] using wordTrace_append hprefix tailTrace_552472
  have hstable : (prefixWord ++ tailWord_552472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552472).length < 2 ^ (prefixWord ++ tailWord_552472).sum := by decide
  have hdescent : baseEnd_552472 < baseStart_552472 := by decide
  rcases family_descends (prefixWord ++ tailWord_552472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552503 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_552503 : Nat := 118140960795 + 552503 * 2 ^ 59
def prefixEnd_552503 : Nat := 4983230072969 + 3 ^ 40 * 552503 * 2
def baseEnd_552503 : Nat := 126088712022736472520707

theorem tailTrace_552503 : CollatzResearch.WordTrace tailWord_552503 prefixEnd_552503 126088712022736472520707 := by
  unfold tailWord_552503
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151439917383465845126163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13434293278255643896750775 20151439917383465845126163)
  ·
    refine ⟨30227159876075198767689245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20151439917383465845126163 30227159876075198767689245)
    ·
      refine ⟨11335184953528199537883467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30227159876075198767689245 11335184953528199537883467)
      ·
        refine ⟨17002777430292299306825201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11335184953528199537883467 17002777430292299306825201)
        ·
          refine ⟨12752083072719224480118901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17002777430292299306825201 12752083072719224480118901)
          ·
            refine ⟨1195507788067427295011147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12752083072719224480118901 1195507788067427295011147)
            ·
              refine ⟨1793261682101140942516721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195507788067427295011147 1793261682101140942516721)
              ·
                refine ⟨1344946261575855706887541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793261682101140942516721 1344946261575855706887541)
                ·
                  refine ⟨126088712022736472520707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1344946261575855706887541 126088712022736472520707)
                  ·
                    rfl

theorem cell21_552503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_552503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552503 prefixEnd_552503 := by exact prefixLift 552503
  have htrace : WordTrace (prefixWord ++ tailWord_552503) baseStart_552503 baseEnd_552503 := by
    simpa [prefixWord, tailWord_552503, baseEnd_552503] using wordTrace_append hprefix tailTrace_552503
  have hstable : (prefixWord ++ tailWord_552503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552503).length < 2 ^ (prefixWord ++ tailWord_552503).sum := by decide
  have hdescent : baseEnd_552503 < baseStart_552503 := by decide
  rcases family_descends (prefixWord ++ tailWord_552503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552517 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_552517 : Nat := 118140960795 + 552517 * 2 ^ 59
def prefixEnd_552517 : Nat := 4983230072969 + 3 ^ 40 * 552517 * 2
def baseEnd_552517 : Nat := 126091907013475559287345

theorem tailTrace_552517 : CollatzResearch.WordTrace tailWord_552517 prefixEnd_552517 126091907013475559287345 := by
  unfold tailWord_552517
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151950539332746236135805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13434633692888497490757203 20151950539332746236135805)
  ·
    refine ⟨7556981452249779838550927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20151950539332746236135805 7556981452249779838550927)
    ·
      refine ⟨11335472178374669757826391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7556981452249779838550927 11335472178374669757826391)
      ·
        refine ⟨17003208267562004636739587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11335472178374669757826391 17003208267562004636739587)
        ·
          refine ⟨25504812401343006955109381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17003208267562004636739587 25504812401343006955109381)
          ·
            refine ⟨4782152325251813804083009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25504812401343006955109381 4782152325251813804083009)
            ·
              refine ⟨3586614243938860353062257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4782152325251813804083009 3586614243938860353062257)
              ·
                refine ⟨2689960682954145264796693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3586614243938860353062257 2689960682954145264796693)
                ·
                  refine ⟨126091907013475559287345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2689960682954145264796693 126091907013475559287345)
                  ·
                    rfl

theorem cell21_552517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_552517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552517 prefixEnd_552517 := by exact prefixLift 552517
  have htrace : WordTrace (prefixWord ++ tailWord_552517) baseStart_552517 baseEnd_552517 := by
    simpa [prefixWord, tailWord_552517, baseEnd_552517] using wordTrace_append hprefix tailTrace_552517
  have hstable : (prefixWord ++ tailWord_552517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552517).length < 2 ^ (prefixWord ++ tailWord_552517).sum := by decide
  have hdescent : baseEnd_552517 < baseStart_552517 := by decide
  rcases family_descends (prefixWord ++ tailWord_552517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552565 : List Nat := [1, 3, 4, 2, 1, 2, 1, 7]
def baseStart_552565 : Nat := 118140960795 + 552565 * 2 ^ 59
def prefixEnd_552565 : Nat := 4983230072969 + 3 ^ 40 * 552565 * 2
def baseEnd_552565 : Nat := 42034287089146047495749

theorem tailTrace_552565 : CollatzResearch.WordTrace tailWord_552565 prefixEnd_552565 42034287089146047495749 := by
  unfold tailWord_552565
  simp only [CollatzResearch.WordTrace]
  refine ⟨20153701243158850433883149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13435800828772566955922099 20153701243158850433883149)
  ·
    refine ⟨7557637966184568912706181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20153701243158850433883149 7557637966184568912706181)
    ·
      refine ⟨1417057118659606671132409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7557637966184568912706181 1417057118659606671132409)
      ·
        refine ⟨1062792838994705003349307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417057118659606671132409 1062792838994705003349307)
        ·
          refine ⟨1594189258492057505023961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062792838994705003349307 1594189258492057505023961)
          ·
            refine ⟨1195641943869043128767971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1594189258492057505023961 1195641943869043128767971)
            ·
              refine ⟨1793462915803564693151957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195641943869043128767971 1793462915803564693151957)
              ·
                refine ⟨42034287089146047495749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1793462915803564693151957 42034287089146047495749)
                ·
                  rfl

theorem cell21_552565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_552565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552565 prefixEnd_552565 := by exact prefixLift 552565
  have htrace : WordTrace (prefixWord ++ tailWord_552565) baseStart_552565 baseEnd_552565 := by
    simpa [prefixWord, tailWord_552565, baseEnd_552565] using wordTrace_append hprefix tailTrace_552565
  have hstable : (prefixWord ++ tailWord_552565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552565).length < 2 ^ (prefixWord ++ tailWord_552565).sum := by decide
  have hdescent : baseEnd_552565 < baseStart_552565 := by decide
  rcases family_descends (prefixWord ++ tailWord_552565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552683 : List Nat := [1, 1, 1, 1, 2, 4, 2, 9]
def baseStart_552683 : Nat := 118140960795 + 552683 * 2 ^ 59
def prefixEnd_552683 : Nat := 4983230072969 + 3 ^ 40 * 552683 * 2
def baseEnd_552683 : Nat := 42043263491698719840113

theorem tailTrace_552683 : CollatzResearch.WordTrace tailWord_552683 prefixEnd_552683 42043263491698719840113 := by
  unfold tailWord_552683
  simp only [CollatzResearch.WordTrace]
  refine ⟨20158005056731356586678703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13438670037820904391119135 20158005056731356586678703)
  ·
    refine ⟨30237007585097034880018055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20158005056731356586678703 30237007585097034880018055)
    ·
      refine ⟨45355511377645552320027083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30237007585097034880018055 45355511377645552320027083)
      ·
        refine ⟨68033267066468328480040625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45355511377645552320027083 68033267066468328480040625)
        ·
          refine ⟨51024950299851246360030469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68033267066468328480040625 51024950299851246360030469)
          ·
            refine ⟨9567178181222108692505713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51024950299851246360030469 9567178181222108692505713)
            ·
              refine ⟨7175383635916581519379285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9567178181222108692505713 7175383635916581519379285)
              ·
                refine ⟨42043263491698719840113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7175383635916581519379285 42043263491698719840113)
                ·
                  rfl

theorem cell21_552683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_552683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552683 prefixEnd_552683 := by exact prefixLift 552683
  have htrace : WordTrace (prefixWord ++ tailWord_552683) baseStart_552683 baseEnd_552683 := by
    simpa [prefixWord, tailWord_552683, baseEnd_552683] using wordTrace_append hprefix tailTrace_552683
  have hstable : (prefixWord ++ tailWord_552683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552683).length < 2 ^ (prefixWord ++ tailWord_552683).sum := by decide
  have hdescent : baseEnd_552683 < baseStart_552683 := by decide
  rcases family_descends (prefixWord ++ tailWord_552683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552748 : List Nat := [2, 2, 1, 1, 1, 5, 3, 3, 3]
def baseStart_552748 : Nat := 118140960795 + 552748 * 2 ^ 59
def prefixEnd_552748 : Nat := 4983230072969 + 3 ^ 40 * 552748 * 2
def baseEnd_552748 : Nat := 126144624360670490936873

theorem tailTrace_552748 : CollatzResearch.WordTrace tailWord_552748 prefixEnd_552748 126144624360670490936873 := by
  unfold tailWord_552748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080187900747936343897449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13440250534330581791863265 10080187900747936343897449)
  ·
    refine ⟨7560140925560952257923087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10080187900747936343897449 7560140925560952257923087)
    ·
      refine ⟨11340211388341428386884631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7560140925560952257923087 11340211388341428386884631)
      ·
        refine ⟨17010317082512142580326947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11340211388341428386884631 17010317082512142580326947)
        ·
          refine ⟨25515475623768213870490421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17010317082512142580326947 25515475623768213870490421)
          ·
            refine ⟨2392075839728270050358477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25515475623768213870490421 2392075839728270050358477)
            ·
              refine ⟨897028439898101268884429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2392075839728270050358477 897028439898101268884429)
              ·
                refine ⟨336385664961787975831661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897028439898101268884429 336385664961787975831661)
                ·
                  refine ⟨126144624360670490936873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336385664961787975831661 126144624360670490936873)
                  ·
                    rfl

theorem cell21_552748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_552748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552748 prefixEnd_552748 := by exact prefixLift 552748
  have htrace : WordTrace (prefixWord ++ tailWord_552748) baseStart_552748 baseEnd_552748 := by
    simpa [prefixWord, tailWord_552748, baseEnd_552748] using wordTrace_append hprefix tailTrace_552748
  have hstable : (prefixWord ++ tailWord_552748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552748).length < 2 ^ (prefixWord ++ tailWord_552748).sum := by decide
  have hdescent : baseEnd_552748 < baseStart_552748 := by decide
  rcases family_descends (prefixWord ++ tailWord_552748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552776 : List Nat := [2, 1, 3, 1, 1, 5, 2, 6]
def baseStart_552776 : Nat := 118140960795 + 552776 * 2 ^ 59
def prefixEnd_552776 : Nat := 4983230072969 + 3 ^ 40 * 552776 * 2
def baseEnd_552776 : Nat := 42050338114049554823383

theorem tailTrace_552776 : CollatzResearch.WordTrace tailWord_552776 prefixEnd_552776 42050338114049554823383 := by
  unfold tailWord_552776
  simp only [CollatzResearch.WordTrace]
  refine ⟨10080698522697216734907091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13440931363596288979876121 10080698522697216734907091)
  ·
    refine ⟨15121047784045825102360637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10080698522697216734907091 15121047784045825102360637)
    ·
      refine ⟨5670392919017184413385239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15121047784045825102360637 5670392919017184413385239)
      ·
        refine ⟨8505589378525776620077859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670392919017184413385239 8505589378525776620077859)
        ·
          refine ⟨12758384067788664930116789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505589378525776620077859 12758384067788664930116789)
          ·
            refine ⟨1196098506355187337198449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12758384067788664930116789 1196098506355187337198449)
            ·
              refine ⟨897073879766390502898837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196098506355187337198449 897073879766390502898837)
              ·
                refine ⟨42050338114049554823383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 897073879766390502898837 42050338114049554823383)
                ·
                  rfl

theorem cell21_552776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_552776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552776 prefixEnd_552776 := by exact prefixLift 552776
  have htrace : WordTrace (prefixWord ++ tailWord_552776) baseStart_552776 baseEnd_552776 := by
    simpa [prefixWord, tailWord_552776, baseEnd_552776] using wordTrace_append hprefix tailTrace_552776
  have hstable : (prefixWord ++ tailWord_552776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552776).length < 2 ^ (prefixWord ++ tailWord_552776).sum := by decide
  have hdescent : baseEnd_552776 < baseStart_552776 := by decide
  rcases family_descends (prefixWord ++ tailWord_552776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552883 : List Nat := [1, 1, 1, 2, 3, 1, 3, 6, 3]
def baseStart_552883 : Nat := 118140960795 + 552883 * 2 ^ 59
def prefixEnd_552883 : Nat := 4983230072969 + 3 ^ 40 * 552883 * 2
def baseEnd_552883 : Nat := 126175433199940256186597

theorem tailTrace_552883 : CollatzResearch.WordTrace tailWord_552883 prefixEnd_552883 126175433199940256186597 := by
  unfold tailWord_552883
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165299656006790743959303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13443533104004527162639535 20165299656006790743959303)
  ·
    refine ⟨30247949484010186115938955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20165299656006790743959303 30247949484010186115938955)
    ·
      refine ⟨45371924226015279173908433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30247949484010186115938955 45371924226015279173908433)
      ·
        refine ⟨34028943169511459380431325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45371924226015279173908433 34028943169511459380431325)
        ·
          refine ⟨12760853688566797267661747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34028943169511459380431325 12760853688566797267661747)
          ·
            refine ⟨19141280532850195901492621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760853688566797267661747 19141280532850195901492621)
            ·
              refine ⟨7177980199818823463059733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19141280532850195901492621 7177980199818823463059733)
              ·
                refine ⟨336467821866507349830925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7177980199818823463059733 336467821866507349830925)
                ·
                  refine ⟨126175433199940256186597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336467821866507349830925 126175433199940256186597)
                  ·
                    rfl

theorem cell21_552883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 6, 3].length) (baseStart_552883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552883 prefixEnd_552883 := by exact prefixLift 552883
  have htrace : WordTrace (prefixWord ++ tailWord_552883) baseStart_552883 baseEnd_552883 := by
    simpa [prefixWord, tailWord_552883, baseEnd_552883] using wordTrace_append hprefix tailTrace_552883
  have hstable : (prefixWord ++ tailWord_552883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552883).length < 2 ^ (prefixWord ++ tailWord_552883).sum := by decide
  have hdescent : baseEnd_552883 < baseStart_552883 := by decide
  rcases family_descends (prefixWord ++ tailWord_552883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552911 : List Nat := [1, 1, 2, 1, 1, 5, 3, 7]
def baseStart_552911 : Nat := 118140960795 + 552911 * 2 ^ 59
def prefixEnd_552911 : Nat := 4983230072969 + 3 ^ 40 * 552911 * 2
def baseEnd_552911 : Nat := 42060607727139476573291

theorem tailTrace_552911 : CollatzResearch.WordTrace tailWord_552911 prefixEnd_552911 42060607727139476573291 := by
  unfold tailWord_552911
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166320899905351525978587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13444213933270234350652391 20166320899905351525978587)
  ·
    refine ⟨30249481349858027288967881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20166320899905351525978587 30249481349858027288967881)
    ·
      refine ⟨22687111012393520466725911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30249481349858027288967881 22687111012393520466725911)
      ·
        refine ⟨34030666518590280700088867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22687111012393520466725911 34030666518590280700088867)
        ·
          refine ⟨51045999777885421050133301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34030666518590280700088867 51045999777885421050133301)
          ·
            refine ⟨4785562479176758223449997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 51045999777885421050133301 4785562479176758223449997)
            ·
              refine ⟨1794585929691284333793749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4785562479176758223449997 1794585929691284333793749)
              ·
                refine ⟨42060607727139476573291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1794585929691284333793749 42060607727139476573291)
                ·
                  rfl

theorem cell21_552911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_552911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552911 prefixEnd_552911 := by exact prefixLift 552911
  have htrace : WordTrace (prefixWord ++ tailWord_552911) baseStart_552911 baseEnd_552911 := by
    simpa [prefixWord, tailWord_552911, baseEnd_552911] using wordTrace_append hprefix tailTrace_552911
  have hstable : (prefixWord ++ tailWord_552911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552911).length < 2 ^ (prefixWord ++ tailWord_552911).sum := by decide
  have hdescent : baseEnd_552911 < baseStart_552911 := by decide
  rcases family_descends (prefixWord ++ tailWord_552911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_552917 : List Nat := [1, 3, 2, 3, 2, 3, 1, 3, 3]
def baseStart_552917 : Nat := 118140960795 + 552917 * 2 ^ 59
def prefixEnd_552917 : Nat := 4983230072969 + 3 ^ 40 * 552917 * 2
def baseEnd_552917 : Nat := 126183192463163752619861

theorem tailTrace_552917 : CollatzResearch.WordTrace tailWord_552917 prefixEnd_552917 126183192463163752619861 := by
  unfold tailWord_552917
  simp only [CollatzResearch.WordTrace]
  refine ⟨20166539737883614550697005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13444359825255743033798003 20166539737883614550697005)
  ·
    refine ⟨7562452401706355456511377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20166539737883614550697005 7562452401706355456511377)
    ·
      refine ⟨5671839301279766592383533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7562452401706355456511377 5671839301279766592383533)
      ·
        refine ⟨2126939737979912472143825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5671839301279766592383533 2126939737979912472143825)
        ·
          refine ⟨1595204803484934354107869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2126939737979912472143825 1595204803484934354107869)
          ·
            refine ⟨598201801306850382790451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1595204803484934354107869 598201801306850382790451)
            ·
              refine ⟨897302701960275574185677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598201801306850382790451 897302701960275574185677)
              ·
                refine ⟨336488513235103340319629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897302701960275574185677 336488513235103340319629)
                ·
                  refine ⟨126183192463163752619861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336488513235103340319629 126183192463163752619861)
                  ·
                    rfl

theorem cell21_552917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_552917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_552917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_552917 prefixEnd_552917 := by exact prefixLift 552917
  have htrace : WordTrace (prefixWord ++ tailWord_552917) baseStart_552917 baseEnd_552917 := by
    simpa [prefixWord, tailWord_552917, baseEnd_552917] using wordTrace_append hprefix tailTrace_552917
  have hstable : (prefixWord ++ tailWord_552917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_552917).length < 2 ^ (prefixWord ++ tailWord_552917).sum := by decide
  have hdescent : baseEnd_552917 < baseStart_552917 := by decide
  rcases family_descends (prefixWord ++ tailWord_552917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553052 : List Nat := [2, 2, 4, 1, 1, 2, 2, 4, 3]
def baseStart_553052 : Nat := 118140960795 + 553052 * 2 ^ 59
def prefixEnd_553052 : Nat := 4983230072969 + 3 ^ 40 * 553052 * 2
def baseEnd_553052 : Nat := 126214001302433517869585

theorem tailTrace_553052 : CollatzResearch.WordTrace tailWord_553052 prefixEnd_553052 126214001302433517869585 := by
  unfold tailWord_553052
  simp only [CollatzResearch.WordTrace]
  refine ⟨10085731796197266303430705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13447642394929688404574273 10085731796197266303430705)
  ·
    refine ⟨7564298847147949727573029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10085731796197266303430705 7564298847147949727573029)
    ·
      refine ⟨1418306033840240573919943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7564298847147949727573029 1418306033840240573919943)
      ·
        refine ⟨2127459050760360860879915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418306033840240573919943 2127459050760360860879915)
        ·
          refine ⟨3191188576140541291319873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127459050760360860879915 3191188576140541291319873)
          ·
            refine ⟨2393391432105405968489905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3191188576140541291319873 2393391432105405968489905)
            ·
              refine ⟨1795043574079054476367429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393391432105405968489905 1795043574079054476367429)
              ·
                refine ⟨336570670139822714318893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1795043574079054476367429 336570670139822714318893)
                ·
                  refine ⟨126214001302433517869585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336570670139822714318893 126214001302433517869585)
                  ·
                    rfl

theorem cell21_553052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_553052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553052 prefixEnd_553052 := by exact prefixLift 553052
  have htrace : WordTrace (prefixWord ++ tailWord_553052) baseStart_553052 baseEnd_553052 := by
    simpa [prefixWord, tailWord_553052, baseEnd_553052] using wordTrace_append hprefix tailTrace_553052
  have hstable : (prefixWord ++ tailWord_553052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553052).length < 2 ^ (prefixWord ++ tailWord_553052).sum := by decide
  have hdescent : baseEnd_553052 < baseStart_553052 := by decide
  rcases family_descends (prefixWord ++ tailWord_553052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553063 : List Nat := [1, 1, 5, 1, 1, 2, 2, 8]
def baseStart_553063 : Nat := 118140960795 + 553063 * 2 ^ 59
def prefixEnd_553063 : Nat := 4983230072969 + 3 ^ 40 * 553063 * 2
def baseEnd_553063 : Nat := 42072170550766647728743

theorem tailTrace_553063 : CollatzResearch.WordTrace tailWord_553063 prefixEnd_553063 42072170550766647728743 := by
  unfold tailWord_553063
  simp only [CollatzResearch.WordTrace]
  refine ⟨20171864795354681485511843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13447909863569787657007895 20171864795354681485511843)
  ·
    refine ⟨30257797193032022228267765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20171864795354681485511843 30257797193032022228267765)
    ·
      refine ⟨2836668486846752083900103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30257797193032022228267765 2836668486846752083900103)
      ·
        refine ⟨4255002730270128125850155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836668486846752083900103 4255002730270128125850155)
        ·
          refine ⟨6382504095405192188775233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255002730270128125850155 6382504095405192188775233)
          ·
            refine ⟨4786878071553894141581425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6382504095405192188775233 4786878071553894141581425)
            ·
              refine ⟨3590158553665420606186069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4786878071553894141581425 3590158553665420606186069)
              ·
                refine ⟨42072170550766647728743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3590158553665420606186069 42072170550766647728743)
                ·
                  rfl

theorem cell21_553063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 8].length) (baseStart_553063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553063 prefixEnd_553063 := by exact prefixLift 553063
  have htrace : WordTrace (prefixWord ++ tailWord_553063) baseStart_553063 baseEnd_553063 := by
    simpa [prefixWord, tailWord_553063, baseEnd_553063] using wordTrace_append hprefix tailTrace_553063
  have hstable : (prefixWord ++ tailWord_553063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553063).length < 2 ^ (prefixWord ++ tailWord_553063).sum := by decide
  have hdescent : baseEnd_553063 < baseStart_553063 := by decide
  rcases family_descends (prefixWord ++ tailWord_553063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553125 : List Nat := [1, 3, 1, 2, 1, 3, 3, 3, 4]
def baseStart_553125 : Nat := 118140960795 + 553125 * 2 ^ 59
def prefixEnd_553125 : Nat := 4983230072969 + 3 ^ 40 * 553125 * 2
def baseEnd_553125 : Nat := 126230660897001613152769

theorem tailTrace_553125 : CollatzResearch.WordTrace tailWord_553125 prefixEnd_553125 126230660897001613152769 := by
  unfold tailWord_553125
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174126121130066074268829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13449417414086710716179219 20174126121130066074268829)
  ·
    refine ⟨7565297295423774777850811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20174126121130066074268829 7565297295423774777850811)
    ·
      refine ⟨11347945943135662166776217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565297295423774777850811 11347945943135662166776217)
      ·
        refine ⟨8510959457351746625082163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11347945943135662166776217 8510959457351746625082163)
        ·
          refine ⟨12766439186027619937623245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8510959457351746625082163 12766439186027619937623245)
          ·
            refine ⟨4787414694760357476608717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12766439186027619937623245 4787414694760357476608717)
            ·
              refine ⟨1795280510535134053728269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4787414694760357476608717 1795280510535134053728269)
              ·
                refine ⟨673230191450675270148101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1795280510535134053728269 673230191450675270148101)
                ·
                  refine ⟨126230660897001613152769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673230191450675270148101 126230660897001613152769)
                  ·
                    rfl

theorem cell21_553125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_553125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553125 prefixEnd_553125 := by exact prefixLift 553125
  have htrace : WordTrace (prefixWord ++ tailWord_553125) baseStart_553125 baseEnd_553125 := by
    simpa [prefixWord, tailWord_553125, baseEnd_553125] using wordTrace_append hprefix tailTrace_553125
  have hstable : (prefixWord ++ tailWord_553125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553125).length < 2 ^ (prefixWord ++ tailWord_553125).sum := by decide
  have hdescent : baseEnd_553125 < baseStart_553125 := by decide
  rcases family_descends (prefixWord ++ tailWord_553125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553173 : List Nat := [1, 3, 2, 4, 2, 2, 1, 6]
def baseStart_553173 : Nat := 118140960795 + 553173 * 2 ^ 59
def prefixEnd_553173 : Nat := 4983230072969 + 3 ^ 40 * 553173 * 2
def baseEnd_553173 : Nat := 42080538383654732117557

theorem tailTrace_553173 : CollatzResearch.WordTrace tailWord_553173 prefixEnd_553173 42080538383654732117557 := by
  unfold tailWord_553173
  simp only [CollatzResearch.WordTrace]
  refine ⟨20175876824956170272016173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13450584549970780181344115 20175876824956170272016173)
  ·
    refine ⟨7565953809358563852006065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20175876824956170272016173 7565953809358563852006065)
    ·
      refine ⟨5674465357018922889004549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7565953809358563852006065 5674465357018922889004549)
      ·
        refine ⟨1063962254441048041688353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5674465357018922889004549 1063962254441048041688353)
        ·
          refine ⟨797971690830786031266265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1063962254441048041688353 797971690830786031266265)
          ·
            refine ⟨598478768123089523449699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 797971690830786031266265 598478768123089523449699)
            ·
              refine ⟨897718152184634285174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598478768123089523449699 897718152184634285174549)
              ·
                refine ⟨42080538383654732117557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 897718152184634285174549 42080538383654732117557)
                ·
                  rfl

theorem cell21_553173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 6].length) (baseStart_553173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553173 prefixEnd_553173 := by exact prefixLift 553173
  have htrace : WordTrace (prefixWord ++ tailWord_553173) baseStart_553173 baseEnd_553173 := by
    simpa [prefixWord, tailWord_553173, baseEnd_553173] using wordTrace_append hprefix tailTrace_553173
  have hstable : (prefixWord ++ tailWord_553173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553173).length < 2 ^ (prefixWord ++ tailWord_553173).sum := by decide
  have hdescent : baseEnd_553173 < baseStart_553173 := by decide
  rcases family_descends (prefixWord ++ tailWord_553173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553218 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 6]
def baseStart_553218 : Nat := 118140960795 + 553218 * 2 ^ 59
def prefixEnd_553218 : Nat := 4983230072969 + 3 ^ 40 * 553218 * 2
def baseEnd_553218 : Nat := 126251884764054118102579

theorem tailTrace_553218 : CollatzResearch.WordTrace tailWord_553218 prefixEnd_553218 126251884764054118102579 := by
  unfold tailWord_553218
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044379527448285739351077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13451678739862095304936205 5044379527448285739351077)
  ·
    refine ⟨945821161396553576128327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5044379527448285739351077 945821161396553576128327)
    ·
      refine ⟨1418731742094830364192491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945821161396553576128327 1418731742094830364192491)
      ·
        refine ⟨2128097613142245546288737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418731742094830364192491 2128097613142245546288737)
        ·
          refine ⟨1596073209856684159716553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128097613142245546288737 1596073209856684159716553)
          ·
            refine ⟨1197054907392513119787415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596073209856684159716553 1197054907392513119787415)
            ·
              refine ⟨1795582361088769679681123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197054907392513119787415 1795582361088769679681123)
              ·
                refine ⟨2693373541633154519521685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795582361088769679681123 2693373541633154519521685)
                ·
                  refine ⟨126251884764054118102579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2693373541633154519521685 126251884764054118102579)
                  ·
                    rfl

theorem cell21_553218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_553218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553218 prefixEnd_553218 := by exact prefixLift 553218
  have htrace : WordTrace (prefixWord ++ tailWord_553218) baseStart_553218 baseEnd_553218 := by
    simpa [prefixWord, tailWord_553218, baseEnd_553218] using wordTrace_append hprefix tailTrace_553218
  have hstable : (prefixWord ++ tailWord_553218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553218).length < 2 ^ (prefixWord ++ tailWord_553218).sum := by decide
  have hdescent : baseEnd_553218 < baseStart_553218 := by decide
  rcases family_descends (prefixWord ++ tailWord_553218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553255 : List Nat := [1, 1, 8, 1, 1, 2, 1, 3, 3]
def baseStart_553255 : Nat := 118140960795 + 553255 * 2 ^ 59
def prefixEnd_553255 : Nat := 4983230072969 + 3 ^ 40 * 553255 * 2
def baseEnd_553255 : Nat := 126260328668150275985837

theorem tailTrace_553255 : CollatzResearch.WordTrace tailWord_553255 prefixEnd_553255 126260328668150275985837 := by
  unfold tailWord_553255
  simp only [CollatzResearch.WordTrace]
  refine ⟨20178867610659098276501219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13452578407106065517667479 20178867610659098276501219)
  ·
    refine ⟨30268301415988647414751829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20178867610659098276501219 30268301415988647414751829)
    ·
      refine ⟨354706657218616961891623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 30268301415988647414751829 354706657218616961891623)
      ·
        refine ⟨532059985827925442837435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354706657218616961891623 532059985827925442837435)
        ·
          refine ⟨798089978741888164256153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532059985827925442837435 798089978741888164256153)
          ·
            refine ⟨598567484056416123192115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798089978741888164256153 598567484056416123192115)
            ·
              refine ⟨897851226084624184788173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598567484056416123192115 897851226084624184788173)
              ·
                refine ⟨336694209781734069295565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897851226084624184788173 336694209781734069295565)
                ·
                  refine ⟨126260328668150275985837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336694209781734069295565 126260328668150275985837)
                  ·
                    rfl

theorem cell21_553255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 3, 3].length) (baseStart_553255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553255 prefixEnd_553255 := by exact prefixLift 553255
  have htrace : WordTrace (prefixWord ++ tailWord_553255) baseStart_553255 baseEnd_553255 := by
    simpa [prefixWord, tailWord_553255, baseEnd_553255] using wordTrace_append hprefix tailTrace_553255
  have hstable : (prefixWord ++ tailWord_553255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553255).length < 2 ^ (prefixWord ++ tailWord_553255).sum := by decide
  have hdescent : baseEnd_553255 < baseStart_553255 := by decide
  rcases family_descends (prefixWord ++ tailWord_553255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553260 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 6]
def baseStart_553260 : Nat := 118140960795 + 553260 * 2 ^ 59
def prefixEnd_553260 : Nat := 4983230072969 + 3 ^ 40 * 553260 * 2
def baseEnd_553260 : Nat := 126261469736271378402493

theorem tailTrace_553260 : CollatzResearch.WordTrace tailWord_553260 prefixEnd_553260 126261469736271378402493 := by
  unfold tailWord_553260
  simp only [CollatzResearch.WordTrace]
  refine ⟨10089524987820492065216617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13452699983760656086955489 10089524987820492065216617)
  ·
    refine ⟨7567143740865369048912463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10089524987820492065216617 7567143740865369048912463)
    ·
      refine ⟨11350715611298053573368695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7567143740865369048912463 11350715611298053573368695)
      ·
        refine ⟨17026073416947080360053043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11350715611298053573368695 17026073416947080360053043)
        ·
          refine ⟨25539110125420620540079565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17026073416947080360053043 25539110125420620540079565)
          ·
            refine ⟨9577166297032732702529837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25539110125420620540079565 9577166297032732702529837)
            ·
              refine ⟨3591437361387274763448689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9577166297032732702529837 3591437361387274763448689)
              ·
                refine ⟨2693578021040456072586517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3591437361387274763448689 2693578021040456072586517)
                ·
                  refine ⟨126261469736271378402493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2693578021040456072586517 126261469736271378402493)
                  ·
                    rfl

theorem cell21_553260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_553260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553260 prefixEnd_553260 := by exact prefixLift 553260
  have htrace : WordTrace (prefixWord ++ tailWord_553260) baseStart_553260 baseEnd_553260 := by
    simpa [prefixWord, tailWord_553260, baseEnd_553260] using wordTrace_append hprefix tailTrace_553260
  have hstable : (prefixWord ++ tailWord_553260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553260).length < 2 ^ (prefixWord ++ tailWord_553260).sum := by decide
  have hdescent : baseEnd_553260 < baseStart_553260 := by decide
  rcases family_descends (prefixWord ++ tailWord_553260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553263 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 3]
def baseStart_553263 : Nat := 118140960795 + 553263 * 2 ^ 59
def prefixEnd_553263 : Nat := 4983230072969 + 3 ^ 40 * 553263 * 2
def baseEnd_553263 : Nat := 126262154377144039852487

theorem tailTrace_553263 : CollatzResearch.WordTrace tailWord_553263 prefixEnd_553263 126262154377144039852487 := by
  unfold tailWord_553263
  simp only [CollatzResearch.WordTrace]
  refine ⟨20179159394630115642792443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13452772929753410428528295 20179159394630115642792443)
  ·
    refine ⟨30268739091945173464188665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20179159394630115642792443 30268739091945173464188665)
    ·
      refine ⟨22701554318958880098141499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30268739091945173464188665 22701554318958880098141499)
      ·
        refine ⟨34052331478438320147212249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22701554318958880098141499 34052331478438320147212249)
        ·
          refine ⟨25539248608828740110409187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34052331478438320147212249 25539248608828740110409187)
          ·
            refine ⟨38308872913243110165613781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25539248608828740110409187 38308872913243110165613781)
            ·
              refine ⟨897864208904135394506573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38308872913243110165613781 897864208904135394506573)
              ·
                refine ⟨336699078339050772939965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897864208904135394506573 336699078339050772939965)
                ·
                  refine ⟨126262154377144039852487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336699078339050772939965 126262154377144039852487)
                  ·
                    rfl

theorem cell21_553263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 3].length) (baseStart_553263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553263 prefixEnd_553263 := by exact prefixLift 553263
  have htrace : WordTrace (prefixWord ++ tailWord_553263) baseStart_553263 baseEnd_553263 := by
    simpa [prefixWord, tailWord_553263, baseEnd_553263] using wordTrace_append hprefix tailTrace_553263
  have hstable : (prefixWord ++ tailWord_553263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553263).length < 2 ^ (prefixWord ++ tailWord_553263).sum := by decide
  have hdescent : baseEnd_553263 < baseStart_553263 := by decide
  rcases family_descends (prefixWord ++ tailWord_553263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553305 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 7]
def baseStart_553305 : Nat := 118140960795 + 553305 * 2 ^ 59
def prefixEnd_553305 : Nat := 4983230072969 + 3 ^ 40 * 553305 * 2
def baseEnd_553305 : Nat := 126271739349361300152401

theorem tailTrace_553305 : CollatzResearch.WordTrace tailWord_553305 prefixEnd_553305 126271739349361300152401 := by
  unfold tailWord_553305
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180691260477956815821369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13453794173651971210547579 20180691260477956815821369)
  ·
    refine ⟨15135518445358467611866027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20180691260477956815821369 15135518445358467611866027)
    ·
      refine ⟨22703277668037701417799041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15135518445358467611866027 22703277668037701417799041)
      ·
        refine ⟨17027458251028276063349281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22703277668037701417799041 17027458251028276063349281)
        ·
          refine ⟨12770593688271207047511961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17027458251028276063349281 12770593688271207047511961)
          ·
            refine ⟨9577945266203405285633971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12770593688271207047511961 9577945266203405285633971)
            ·
              refine ⟨14366917899305107928450957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9577945266203405285633971 14366917899305107928450957)
              ·
                refine ⟨5387594212239415473169109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14366917899305107928450957 5387594212239415473169109)
                ·
                  refine ⟨126271739349361300152401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5387594212239415473169109 126271739349361300152401)
                  ·
                    rfl

theorem cell21_553305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_553305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553305 prefixEnd_553305 := by exact prefixLift 553305
  have htrace : WordTrace (prefixWord ++ tailWord_553305) baseStart_553305 baseEnd_553305 := by
    simpa [prefixWord, tailWord_553305, baseEnd_553305] using wordTrace_append hprefix tailTrace_553305
  have hstable : (prefixWord ++ tailWord_553305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553305).length < 2 ^ (prefixWord ++ tailWord_553305).sum := by decide
  have hdescent : baseEnd_553305 < baseStart_553305 := by decide
  rcases family_descends (prefixWord ++ tailWord_553305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553339 : List Nat := [1, 1, 1, 1, 1, 8, 1, 4, 3]
def baseStart_553339 : Nat := 118140960795 + 553339 * 2 ^ 59
def prefixEnd_553339 : Nat := 4983230072969 + 3 ^ 40 * 553339 * 2
def baseEnd_553339 : Nat := 126279498612584796585665

theorem tailTrace_553339 : CollatzResearch.WordTrace tailWord_553339 prefixEnd_553339 126279498612584796585665 := by
  unfold tailWord_553339
  simp only [CollatzResearch.WordTrace]
  refine ⟨20181931342354780622559071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13454620894903187081706047 20181931342354780622559071)
  ·
    refine ⟨30272897013532170933838607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20181931342354780622559071 30272897013532170933838607)
    ·
      refine ⟨45409345520298256400757911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30272897013532170933838607 45409345520298256400757911)
      ·
        refine ⟨68114018280447384601136867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45409345520298256400757911 68114018280447384601136867)
        ·
          refine ⟨102171027420671076901705301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68114018280447384601136867 102171027420671076901705301)
          ·
            refine ⟨1197316727585989182441859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 102171027420671076901705301 1197316727585989182441859)
            ·
              refine ⟨1795975091378983773662789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197316727585989182441859 1795975091378983773662789)
              ·
                refine ⟨336745329633559457561773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1795975091378983773662789 336745329633559457561773)
                ·
                  refine ⟨126279498612584796585665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336745329633559457561773 126279498612584796585665)
                  ·
                    rfl

theorem cell21_553339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 4, 3].length) (baseStart_553339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553339 prefixEnd_553339 := by exact prefixLift 553339
  have htrace : WordTrace (prefixWord ++ tailWord_553339) baseStart_553339 baseEnd_553339 := by
    simpa [prefixWord, tailWord_553339, baseEnd_553339] using wordTrace_append hprefix tailTrace_553339
  have hstable : (prefixWord ++ tailWord_553339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553339).length < 2 ^ (prefixWord ++ tailWord_553339).sum := by decide
  have hdescent : baseEnd_553339 < baseStart_553339 := by decide
  rcases family_descends (prefixWord ++ tailWord_553339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553353 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 4]
def baseStart_553353 : Nat := 118140960795 + 553353 * 2 ^ 59
def prefixEnd_553353 : Nat := 4983230072969 + 3 ^ 40 * 553353 * 2
def baseEnd_553353 : Nat := 126282693603323883352303

theorem tailTrace_553353 : CollatzResearch.WordTrace tailWord_553353 prefixEnd_553353 126282693603323883352303 := by
  unfold tailWord_553353
  simp only [CollatzResearch.WordTrace]
  refine ⟨20182441964304061013568713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13454961309536040675712475 20182441964304061013568713)
  ·
    refine ⟨15136831473228045760176535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20182441964304061013568713 15136831473228045760176535)
    ·
      refine ⟨22705247209842068640264803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15136831473228045760176535 22705247209842068640264803)
      ·
        refine ⟨34057870814763102960397205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22705247209842068640264803 34057870814763102960397205)
        ·
          refine ⟨1596462694442020451268619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34057870814763102960397205 1596462694442020451268619)
          ·
            refine ⟨2394694041663030676902929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596462694442020451268619 2394694041663030676902929)
            ·
              refine ⟨1796020531247273007677197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394694041663030676902929 1796020531247273007677197)
              ·
                refine ⟨673507699217727377878949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1796020531247273007677197 673507699217727377878949)
                ·
                  refine ⟨126282693603323883352303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673507699217727377878949 126282693603323883352303)
                  ·
                    rfl

theorem cell21_553353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_553353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553353 prefixEnd_553353 := by exact prefixLift 553353
  have htrace : WordTrace (prefixWord ++ tailWord_553353) baseStart_553353 baseEnd_553353 := by
    simpa [prefixWord, tailWord_553353, baseEnd_553353] using wordTrace_append hprefix tailTrace_553353
  have hstable : (prefixWord ++ tailWord_553353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553353).length < 2 ^ (prefixWord ++ tailWord_553353).sum := by decide
  have hdescent : baseEnd_553353 < baseStart_553353 := by decide
  rcases family_descends (prefixWord ++ tailWord_553353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553381 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 7]
def baseStart_553381 : Nat := 118140960795 + 553381 * 2 ^ 59
def prefixEnd_553381 : Nat := 4983230072969 + 3 ^ 40 * 553381 * 2
def baseEnd_553381 : Nat := 126289083584802056885579

theorem tailTrace_553381 : CollatzResearch.WordTrace tailWord_553381 prefixEnd_553381 126289083584802056885579 := by
  unfold tailWord_553381
  simp only [CollatzResearch.WordTrace]
  refine ⟨20183463208202621795587997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13455642138801747863725331 20183463208202621795587997)
  ·
    refine ⟨7568798703075983173345499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20183463208202621795587997 7568798703075983173345499)
    ·
      refine ⟨11353198054613974760018249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7568798703075983173345499 11353198054613974760018249)
      ·
        refine ⟨8514898540960481070013687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11353198054613974760018249 8514898540960481070013687)
        ·
          refine ⟨12772347811440721605020531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8514898540960481070013687 12772347811440721605020531)
          ·
            refine ⟨19158521717161082407530797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12772347811440721605020531 19158521717161082407530797)
            ·
              refine ⟨7184445643935405902824049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19158521717161082407530797 7184445643935405902824049)
              ·
                refine ⟨5388334232951554427118037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7184445643935405902824049 5388334232951554427118037)
                ·
                  refine ⟨126289083584802056885579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5388334232951554427118037 126289083584802056885579)
                  ·
                    rfl

theorem cell21_553381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_553381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553381 prefixEnd_553381 := by exact prefixLift 553381
  have htrace : WordTrace (prefixWord ++ tailWord_553381) baseStart_553381 baseEnd_553381 := by
    simpa [prefixWord, tailWord_553381, baseEnd_553381] using wordTrace_append hprefix tailTrace_553381
  have hstable : (prefixWord ++ tailWord_553381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553381).length < 2 ^ (prefixWord ++ tailWord_553381).sum := by decide
  have hdescent : baseEnd_553381 < baseStart_553381 := by decide
  rcases family_descends (prefixWord ++ tailWord_553381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553384 : List Nat := [2, 1, 6, 1, 1, 2, 8]
def baseStart_553384 : Nat := 118140960795 + 553384 * 2 ^ 59
def prefixEnd_553384 : Nat := 4983230072969 + 3 ^ 40 * 553384 * 2
def baseEnd_553384 : Nat := 14032196469519413148397

theorem tailTrace_553384 : CollatzResearch.WordTrace tailWord_553384 prefixEnd_553384 14032196469519413148397 := by
  unfold tailWord_553384
  simp only [CollatzResearch.WordTrace]
  refine ⟨10091786313595876653973603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13455715084794502205298137 10091786313595876653973603)
  ·
    refine ⟨15137679470393814980960405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10091786313595876653973603 15137679470393814980960405)
    ·
      refine ⟨709578725174710077232519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15137679470393814980960405 709578725174710077232519)
      ·
        refine ⟨1064368087762065115848779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709578725174710077232519 1064368087762065115848779)
        ·
          refine ⟨1596552131643097673773169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064368087762065115848779 1596552131643097673773169)
          ·
            refine ⟨1197414098732323255329877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596552131643097673773169 1197414098732323255329877)
            ·
              refine ⟨14032196469519413148397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1197414098732323255329877 14032196469519413148397)
              ·
                rfl

theorem cell21_553384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 8].length) (baseStart_553384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553384 prefixEnd_553384 := by exact prefixLift 553384
  have htrace : WordTrace (prefixWord ++ tailWord_553384) baseStart_553384 baseEnd_553384 := by
    simpa [prefixWord, tailWord_553384, baseEnd_553384] using wordTrace_append hprefix tailTrace_553384
  have hstable : (prefixWord ++ tailWord_553384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553384).length < 2 ^ (prefixWord ++ tailWord_553384).sum := by decide
  have hdescent : baseEnd_553384 < baseStart_553384 := by decide
  rcases family_descends (prefixWord ++ tailWord_553384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553505 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_553505 : Nat := 118140960795 + 553505 * 2 ^ 59
def prefixEnd_553505 : Nat := 4983230072969 + 3 ^ 40 * 553505 * 2
def baseEnd_553505 : Nat := 126317382074205396818659

theorem tailTrace_553505 : CollatzResearch.WordTrace tailWord_553505 prefixEnd_553505 126317382074205396818659 := by
  unfold tailWord_553505
  simp only [CollatzResearch.WordTrace]
  refine ⟨20187985859753390973101969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13458657239835593982067979 20187985859753390973101969)
  ·
    refine ⟨15140989394815043229826477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20187985859753390973101969 15140989394815043229826477)
    ·
      refine ⟨5677871023055641211184929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15140989394815043229826477 5677871023055641211184929)
      ·
        refine ⟨4258403267291730908388697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5677871023055641211184929 4258403267291730908388697)
        ·
          refine ⟨3193802450468798181291523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4258403267291730908388697 3193802450468798181291523)
          ·
            refine ⟨4790703675703197271937285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3193802450468798181291523 4790703675703197271937285)
            ·
              refine ⟨898256939194349488488241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4790703675703197271937285 898256939194349488488241)
              ·
                refine ⟨673692704395762116366181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 898256939194349488488241 673692704395762116366181)
                ·
                  refine ⟨126317382074205396818659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 673692704395762116366181 126317382074205396818659)
                  ·
                    rfl

theorem cell21_553505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_553505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553505 prefixEnd_553505 := by exact prefixLift 553505
  have htrace : WordTrace (prefixWord ++ tailWord_553505) baseStart_553505 baseEnd_553505 := by
    simpa [prefixWord, tailWord_553505, baseEnd_553505] using wordTrace_append hprefix tailTrace_553505
  have hstable : (prefixWord ++ tailWord_553505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553505).length < 2 ^ (prefixWord ++ tailWord_553505).sum := by decide
  have hdescent : baseEnd_553505 < baseStart_553505 := by decide
  rcases family_descends (prefixWord ++ tailWord_553505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553677 : List Nat := [1, 6, 2, 1, 2, 1, 1, 4, 3]
def baseStart_553677 : Nat := 118140960795 + 553677 * 2 ^ 59
def prefixEnd_553677 : Nat := 4983230072969 + 3 ^ 40 * 553677 * 2
def baseEnd_553677 : Nat := 126356634817571319951641

theorem tailTrace_553677 : CollatzResearch.WordTrace tailWord_553677 prefixEnd_553677 126356634817571319951641 := by
  unfold tailWord_553677
  simp only [CollatzResearch.WordTrace]
  refine ⟨20194259215130264348363285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13462839476753509565575523 20194259215130264348363285)
  ·
    refine ⟨946605900709231141329529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 20194259215130264348363285 946605900709231141329529)
    ·
      refine ⟨709954425531923355997147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 946605900709231141329529 709954425531923355997147)
      ·
        refine ⟨1064931638297885033995721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709954425531923355997147 1064931638297885033995721)
        ·
          refine ⟨798698728723413775496791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1064931638297885033995721 798698728723413775496791)
          ·
            refine ⟨1198048093085120663245187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798698728723413775496791 1198048093085120663245187)
            ·
              refine ⟨1797072139627680994867781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198048093085120663245187 1797072139627680994867781)
              ·
                refine ⟨336951026180190186537709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1797072139627680994867781 336951026180190186537709)
                ·
                  refine ⟨126356634817571319951641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336951026180190186537709 126356634817571319951641)
                  ·
                    rfl

theorem cell21_553677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_553677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553677 prefixEnd_553677 := by exact prefixLift 553677
  have htrace : WordTrace (prefixWord ++ tailWord_553677) baseStart_553677 baseEnd_553677 := by
    simpa [prefixWord, tailWord_553677, baseEnd_553677] using wordTrace_append hprefix tailTrace_553677
  have hstable : (prefixWord ++ tailWord_553677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553677).length < 2 ^ (prefixWord ++ tailWord_553677).sum := by decide
  have hdescent : baseEnd_553677 < baseStart_553677 := by decide
  rcases family_descends (prefixWord ++ tailWord_553677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553761 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_553761 : Nat := 118140960795 + 553761 * 2 ^ 59
def prefixEnd_553761 : Nat := 4983230072969 + 3 ^ 40 * 553761 * 2
def baseEnd_553761 : Nat := 126375804762005840551469

theorem tailTrace_553761 : CollatzResearch.WordTrace tailWord_553761 prefixEnd_553761 126375804762005840551469 := by
  unfold tailWord_553761
  simp only [CollatzResearch.WordTrace]
  refine ⟨20197322946825946694421137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13464881964550631129614091 20197322946825946694421137)
  ·
    refine ⟨15147992210119460020815853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20197322946825946694421137 15147992210119460020815853)
    ·
      refine ⟨5680497078794797507805945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15147992210119460020815853 5680497078794797507805945)
      ·
        refine ⟨4260372809096098130854459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5680497078794797507805945 4260372809096098130854459)
        ·
          refine ⟨6390559213644147196281689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4260372809096098130854459 6390559213644147196281689)
          ·
            refine ⟨4792919410233110397211267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6390559213644147196281689 4792919410233110397211267)
            ·
              refine ⟨7189379115349665595816901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792919410233110397211267 7189379115349665595816901)
              ·
                refine ⟨1348008584128062299215669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7189379115349665595816901 1348008584128062299215669)
                ·
                  refine ⟨126375804762005840551469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1348008584128062299215669 126375804762005840551469)
                  ·
                    rfl

theorem cell21_553761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_553761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553761 prefixEnd_553761 := by exact prefixLift 553761
  have htrace : WordTrace (prefixWord ++ tailWord_553761) baseStart_553761 baseEnd_553761 := by
    simpa [prefixWord, tailWord_553761, baseEnd_553761] using wordTrace_append hprefix tailTrace_553761
  have hstable : (prefixWord ++ tailWord_553761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553761).length < 2 ^ (prefixWord ++ tailWord_553761).sum := by decide
  have hdescent : baseEnd_553761 < baseStart_553761 := by decide
  rcases family_descends (prefixWord ++ tailWord_553761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553770 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_553770 : Nat := 118140960795 + 553770 * 2 ^ 59
def prefixEnd_553770 : Nat := 4983230072969 + 3 ^ 40 * 553770 * 2
def baseEnd_553770 : Nat := 126377858684623824901451

theorem tailTrace_553770 : CollatzResearch.WordTrace tailWord_553770 prefixEnd_553770 126377858684623824901451 := by
  unfold tailWord_553770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049412800948335307874691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13465100802528894154332509 5049412800948335307874691)
  ·
    refine ⟨7574119201422502961812037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5049412800948335307874691 7574119201422502961812037)
    ·
      refine ⟨1420147350266719305339757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7574119201422502961812037 1420147350266719305339757)
      ·
        refine ⟨532555256350019739502409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1420147350266719305339757 532555256350019739502409)
        ·
          refine ⟨399416442262514804626807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532555256350019739502409 399416442262514804626807)
          ·
            refine ⟨599124663393772206940211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399416442262514804626807 599124663393772206940211)
            ·
              refine ⟨898686995090658310410317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599124663393772206940211 898686995090658310410317)
              ·
                refine ⟨337007623158996866403869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 898686995090658310410317 337007623158996866403869)
                ·
                  refine ⟨126377858684623824901451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337007623158996866403869 126377858684623824901451)
                  ·
                    rfl

theorem cell21_553770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_553770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553770 prefixEnd_553770 := by exact prefixLift 553770
  have htrace : WordTrace (prefixWord ++ tailWord_553770) baseStart_553770 baseEnd_553770 := by
    simpa [prefixWord, tailWord_553770, baseEnd_553770] using wordTrace_append hprefix tailTrace_553770
  have hstable : (prefixWord ++ tailWord_553770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553770).length < 2 ^ (prefixWord ++ tailWord_553770).sum := by decide
  have hdescent : baseEnd_553770 < baseStart_553770 := by decide
  rcases family_descends (prefixWord ++ tailWord_553770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553795 : List Nat := [1, 1, 1, 3, 1, 4, 5, 2, 3]
def baseStart_553795 : Nat := 118140960795 + 553795 * 2 ^ 59
def prefixEnd_553795 : Nat := 4983230072969 + 3 ^ 40 * 553795 * 2
def baseEnd_553795 : Nat := 126383564025229336984733

theorem tailTrace_553795 : CollatzResearch.WordTrace tailWord_553795 prefixEnd_553795 126383564025229336984733 := by
  unfold tailWord_553795
  simp only [CollatzResearch.WordTrace]
  refine ⟨20198563028702770501158839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13465708685801847000772559 20198563028702770501158839)
  ·
    refine ⟨30297844543054155751738259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20198563028702770501158839 30297844543054155751738259)
    ·
      refine ⟨45446766814581233627607389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30297844543054155751738259 45446766814581233627607389)
      ·
        refine ⟨17042537555467962610352771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45446766814581233627607389 17042537555467962610352771)
        ·
          refine ⟨25563806333201943915529157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17042537555467962610352771 25563806333201943915529157)
          ·
            refine ⟨4793213687475364484161717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25563806333201943915529157 4793213687475364484161717)
            ·
              refine ⟨449363783200815420390161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4793213687475364484161717 449363783200815420390161)
              ·
                refine ⟨337022837400611565292621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449363783200815420390161 337022837400611565292621)
                ·
                  refine ⟨126383564025229336984733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337022837400611565292621 126383564025229336984733)
                  ·
                    rfl

theorem cell21_553795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 2, 3].length) (baseStart_553795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553795 prefixEnd_553795 := by exact prefixLift 553795
  have htrace : WordTrace (prefixWord ++ tailWord_553795) baseStart_553795 baseEnd_553795 := by
    simpa [prefixWord, tailWord_553795, baseEnd_553795] using wordTrace_append hprefix tailTrace_553795
  have hstable : (prefixWord ++ tailWord_553795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553795).length < 2 ^ (prefixWord ++ tailWord_553795).sum := by decide
  have hdescent : baseEnd_553795 < baseStart_553795 := by decide
  rcases family_descends (prefixWord ++ tailWord_553795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553809 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 4]
def baseStart_553809 : Nat := 118140960795 + 553809 * 2 ^ 59
def prefixEnd_553809 : Nat := 4983230072969 + 3 ^ 40 * 553809 * 2
def baseEnd_553809 : Nat := 126386759015968423751371

theorem tailTrace_553809 : CollatzResearch.WordTrace tailWord_553809 prefixEnd_553809 126386759015968423751371 := by
  unfold tailWord_553809
  simp only [CollatzResearch.WordTrace]
  refine ⟨20199073650652050892168481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13466049100434700594778987 20199073650652050892168481)
  ·
    refine ⟨15149305237989038169126361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20199073650652050892168481 15149305237989038169126361)
    ·
      refine ⟨11361978928491778626844771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15149305237989038169126361 11361978928491778626844771)
      ·
        refine ⟨17042968392737667940267157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11361978928491778626844771 17042968392737667940267157)
        ·
          refine ⟨798889143409578184700023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17042968392737667940267157 798889143409578184700023)
          ·
            refine ⟨1198333715114367277050035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798889143409578184700023 1198333715114367277050035)
            ·
              refine ⟨1797500572671550915575053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1198333715114367277050035 1797500572671550915575053)
              ·
                refine ⟨674062714751831593340645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797500572671550915575053 674062714751831593340645)
                ·
                  refine ⟨126386759015968423751371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674062714751831593340645 126386759015968423751371)
                  ·
                    rfl

theorem cell21_553809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_553809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553809 prefixEnd_553809 := by exact prefixLift 553809
  have htrace : WordTrace (prefixWord ++ tailWord_553809) baseStart_553809 baseEnd_553809 := by
    simpa [prefixWord, tailWord_553809, baseEnd_553809] using wordTrace_append hprefix tailTrace_553809
  have hstable : (prefixWord ++ tailWord_553809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553809).length < 2 ^ (prefixWord ++ tailWord_553809).sum := by decide
  have hdescent : baseEnd_553809 < baseStart_553809 := by decide
  rcases family_descends (prefixWord ++ tailWord_553809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553851 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_553851 : Nat := 118140960795 + 553851 * 2 ^ 59
def prefixEnd_553851 : Nat := 4983230072969 + 3 ^ 40 * 553851 * 2
def baseEnd_553851 : Nat := 126396343988185684051285

theorem tailTrace_553851 : CollatzResearch.WordTrace tailWord_553851 prefixEnd_553851 126396343988185684051285 := by
  unfold tailWord_553851
  simp only [CollatzResearch.WordTrace]
  refine ⟨20200605516499892065197407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13467070344333261376798271 20200605516499892065197407)
  ·
    refine ⟨30300908274749838097796111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20200605516499892065197407 30300908274749838097796111)
    ·
      refine ⟨45451362412124757146694167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30300908274749838097796111 45451362412124757146694167)
      ·
        refine ⟨68177043618187135720041251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45451362412124757146694167 68177043618187135720041251)
        ·
          refine ⟨102265565427280703580061877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68177043618187135720041251 102265565427280703580061877)
          ·
            refine ⟨9587396758807565960630801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 102265565427280703580061877 9587396758807565960630801)
            ·
              refine ⟨7190547569105674470473101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9587396758807565960630801 7190547569105674470473101)
              ·
                refine ⟨2696455338414627926427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7190547569105674470473101 2696455338414627926427413)
                ·
                  refine ⟨126396343988185684051285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2696455338414627926427413 126396343988185684051285)
                  ·
                    rfl

theorem cell21_553851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_553851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553851 prefixEnd_553851 := by exact prefixLift 553851
  have htrace : WordTrace (prefixWord ++ tailWord_553851) baseStart_553851 baseEnd_553851 := by
    simpa [prefixWord, tailWord_553851, baseEnd_553851] using wordTrace_append hprefix tailTrace_553851
  have hstable : (prefixWord ++ tailWord_553851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553851).length < 2 ^ (prefixWord ++ tailWord_553851).sum := by decide
  have hdescent : baseEnd_553851 < baseStart_553851 := by decide
  rcases family_descends (prefixWord ++ tailWord_553851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553868 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_553868 : Nat := 118140960795 + 553868 * 2 ^ 59
def prefixEnd_553868 : Nat := 4983230072969 + 3 ^ 40 * 553868 * 2
def baseEnd_553868 : Nat := 126400223619797432267917

theorem tailTrace_553868 : CollatzResearch.WordTrace tailWord_553868 prefixEnd_553868 126400223619797432267917 := by
  unfold tailWord_553868
  simp only [CollatzResearch.WordTrace]
  refine ⟨10100612778719151984283129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13467483704958869312377505 10100612778719151984283129)
  ·
    refine ⟨7575459584039363988212347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10100612778719151984283129 7575459584039363988212347)
    ·
      refine ⟨11363189376059045982318521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7575459584039363988212347 11363189376059045982318521)
      ·
        refine ⟨8522392032044284486738891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11363189376059045982318521 8522392032044284486738891)
        ·
          refine ⟨12783588048066426730108337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8522392032044284486738891 12783588048066426730108337)
          ·
            refine ⟨9587691036049820047581253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12783588048066426730108337 9587691036049820047581253)
            ·
              refine ⟨1797692069259341258921485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9587691036049820047581253 1797692069259341258921485)
              ·
                refine ⟨674134525972252972095557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797692069259341258921485 674134525972252972095557)
                ·
                  refine ⟨126400223619797432267917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674134525972252972095557 126400223619797432267917)
                  ·
                    rfl

theorem cell21_553868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_553868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553868 prefixEnd_553868 := by exact prefixLift 553868
  have htrace : WordTrace (prefixWord ++ tailWord_553868) baseStart_553868 baseEnd_553868 := by
    simpa [prefixWord, tailWord_553868, baseEnd_553868] using wordTrace_append hprefix tailTrace_553868
  have hstable : (prefixWord ++ tailWord_553868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553868).length < 2 ^ (prefixWord ++ tailWord_553868).sum := by decide
  have hdescent : baseEnd_553868 < baseStart_553868 := by decide
  rcases family_descends (prefixWord ++ tailWord_553868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_553913 : List Nat := [1, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_553913 : Nat := 118140960795 + 553913 * 2 ^ 59
def prefixEnd_553913 : Nat := 4983230072969 + 3 ^ 40 * 553913 * 2
def baseEnd_553913 : Nat := 126410493232887354017825

theorem tailTrace_553913 : CollatzResearch.WordTrace tailWord_553913 prefixEnd_553913 126410493232887354017825 := by
  unfold tailWord_553913
  simp only [CollatzResearch.WordTrace]
  refine ⟨20202866842275276653954393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13468577894850184435969595 20202866842275276653954393)
  ·
    refine ⟨15152150131706457490465795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20202866842275276653954393 15152150131706457490465795)
    ·
      refine ⟨22728225197559686235698693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15152150131706457490465795 22728225197559686235698693)
      ·
        refine ⟨4261542224542441169193505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22728225197559686235698693 4261542224542441169193505)
        ·
          refine ⟨3196156668406830876895129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4261542224542441169193505 3196156668406830876895129)
          ·
            refine ⟨2397117501305123157671347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3196156668406830876895129 2397117501305123157671347)
            ·
              refine ⟨3595676251957684736507021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397117501305123157671347 3595676251957684736507021)
              ·
                refine ⟨1348378594484131776190133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3595676251957684736507021 1348378594484131776190133)
                ·
                  refine ⟨126410493232887354017825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1348378594484131776190133 126410493232887354017825)
                  ·
                    rfl

theorem cell21_553913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_553913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_553913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_553913 prefixEnd_553913 := by exact prefixLift 553913
  have htrace : WordTrace (prefixWord ++ tailWord_553913) baseStart_553913 baseEnd_553913 := by
    simpa [prefixWord, tailWord_553913, baseEnd_553913] using wordTrace_append hprefix tailTrace_553913
  have hstable : (prefixWord ++ tailWord_553913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_553913).length < 2 ^ (prefixWord ++ tailWord_553913).sum := by decide
  have hdescent : baseEnd_553913 < baseStart_553913 := by decide
  rcases family_descends (prefixWord ++ tailWord_553913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554079 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_554079 : Nat := 118140960795 + 554079 * 2 ^ 59
def prefixEnd_554079 : Nat := 4983230072969 + 3 ^ 40 * 554079 * 2
def baseEnd_554079 : Nat := 126448376694507954250819

theorem tailTrace_554079 : CollatzResearch.WordTrace tailWord_554079 prefixEnd_554079 126448376694507954250819 := by
  unfold tailWord_554079
  simp only [CollatzResearch.WordTrace]
  refine ⟨20208921359673887004497291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13472614239782591336331527 20208921359673887004497291)
  ·
    refine ⟨30313382039510830506745937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20208921359673887004497291 30313382039510830506745937)
    ·
      refine ⟨22735036529633122880059453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30313382039510830506745937 22735036529633122880059453)
      ·
        refine ⟨8525638698612421080022295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22735036529633122880059453 8525638698612421080022295)
        ·
          refine ⟨12788458047918631620033443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8525638698612421080022295 12788458047918631620033443)
          ·
            refine ⟨19182687071877947430050165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12788458047918631620033443 19182687071877947430050165)
            ·
              refine ⟨1798376912988557571567203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19182687071877947430050165 1798376912988557571567203)
              ·
                refine ⟨2697565369482836357350805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798376912988557571567203 2697565369482836357350805)
                ·
                  refine ⟨126448376694507954250819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2697565369482836357350805 126448376694507954250819)
                  ·
                    rfl

theorem cell21_554079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_554079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554079 prefixEnd_554079 := by exact prefixLift 554079
  have htrace : WordTrace (prefixWord ++ tailWord_554079) baseStart_554079 baseEnd_554079 := by
    simpa [prefixWord, tailWord_554079, baseEnd_554079] using wordTrace_append hprefix tailTrace_554079
  have hstable : (prefixWord ++ tailWord_554079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554079).length < 2 ^ (prefixWord ++ tailWord_554079).sum := by decide
  have hdescent : baseEnd_554079 < baseStart_554079 := by decide
  rcases family_descends (prefixWord ++ tailWord_554079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554082 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 5]
def baseStart_554082 : Nat := 118140960795 + 554082 * 2 ^ 59
def prefixEnd_554082 : Nat := 4983230072969 + 3 ^ 40 * 554082 * 2
def baseEnd_554082 : Nat := 126449061335380615700813

theorem tailTrace_554082 : CollatzResearch.WordTrace tailWord_554082 prefixEnd_554082 126449061335380615700813 := by
  unfold tailWord_554082
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052257694665754629214125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13472687185775345677904333 5052257694665754629214125)
  ·
    refine ⟨1894596635499657985955297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5052257694665754629214125 1894596635499657985955297)
    ·
      refine ⟨1420947476624743489466473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1894596635499657985955297 1420947476624743489466473)
      ·
        refine ⟨1065710607468557617099855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1420947476624743489466473 1065710607468557617099855)
        ·
          refine ⟨1598565911202836425649783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065710607468557617099855 1598565911202836425649783)
          ·
            refine ⟨2397848866804254638474675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598565911202836425649783 2397848866804254638474675)
            ·
              refine ⟨3596773300206381957712013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2397848866804254638474675 3596773300206381957712013)
              ·
                refine ⟨1348789987577393234142005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3596773300206381957712013 1348789987577393234142005)
                ·
                  refine ⟨126449061335380615700813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1348789987577393234142005 126449061335380615700813)
                  ·
                    rfl

theorem cell21_554082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_554082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554082 prefixEnd_554082 := by exact prefixLift 554082
  have htrace : WordTrace (prefixWord ++ tailWord_554082) baseStart_554082 baseEnd_554082 := by
    simpa [prefixWord, tailWord_554082, baseEnd_554082] using wordTrace_append hprefix tailTrace_554082
  have hstable : (prefixWord ++ tailWord_554082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554082).length < 2 ^ (prefixWord ++ tailWord_554082).sum := by decide
  have hdescent : baseEnd_554082 < baseStart_554082 := by decide
  rcases family_descends (prefixWord ++ tailWord_554082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554124 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_554124 : Nat := 118140960795 + 554124 * 2 ^ 59
def prefixEnd_554124 : Nat := 4983230072969 + 3 ^ 40 * 554124 * 2
def baseEnd_554124 : Nat := 126458646307597876000727

theorem tailTrace_554124 : CollatzResearch.WordTrace tailWord_554124 prefixEnd_554124 126458646307597876000727 := by
  unfold tailWord_554124
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105281322255429844942713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13473708429673906459923617 10105281322255429844942713)
  ·
    refine ⟨7578960991691572383707035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10105281322255429844942713 7578960991691572383707035)
    ·
      refine ⟨11368441487537358575560553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7578960991691572383707035 11368441487537358575560553)
      ·
        refine ⟨8526331115653018931670415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11368441487537358575560553 8526331115653018931670415)
        ·
          refine ⟨12789496673479528397505623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8526331115653018931670415 12789496673479528397505623)
          ·
            refine ⟨19184245010219292596258435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12789496673479528397505623 19184245010219292596258435)
            ·
              refine ⟨28776367515328938894387653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19184245010219292596258435 28776367515328938894387653)
              ·
                refine ⟨5395568909124176042697685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28776367515328938894387653 5395568909124176042697685)
                ·
                  refine ⟨126458646307597876000727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5395568909124176042697685 126458646307597876000727)
                  ·
                    rfl

theorem cell21_554124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_554124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554124 prefixEnd_554124 := by exact prefixLift 554124
  have htrace : WordTrace (prefixWord ++ tailWord_554124) baseStart_554124 baseEnd_554124 := by
    simpa [prefixWord, tailWord_554124, baseEnd_554124] using wordTrace_append hprefix tailTrace_554124
  have hstable : (prefixWord ++ tailWord_554124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554124).length < 2 ^ (prefixWord ++ tailWord_554124).sum := by decide
  have hdescent : baseEnd_554124 < baseStart_554124 := by decide
  rcases family_descends (prefixWord ++ tailWord_554124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554234 : List Nat := [3, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_554234 : Nat := 118140960795 + 554234 * 2 ^ 59
def prefixEnd_554234 : Nat := 4983230072969 + 3 ^ 40 * 554234 * 2
def baseEnd_554234 : Nat := 126483749806262129167169

theorem tailTrace_554234 : CollatzResearch.WordTrace tailWord_554234 prefixEnd_554234 126483749806262129167169 := by
  unfold tailWord_554234
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053643668528087119097439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13476383116074898984259837 5053643668528087119097439)
  ·
    refine ⟨7580465502792130678646159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5053643668528087119097439 7580465502792130678646159)
    ·
      refine ⟨11370698254188196017969239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7580465502792130678646159 11370698254188196017969239)
      ·
        refine ⟨17056047381282294026953859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11370698254188196017969239 17056047381282294026953859)
        ·
          refine ⟨25584071071923441040430789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17056047381282294026953859 25584071071923441040430789)
          ·
            refine ⟨4797013325985645195080773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25584071071923441040430789 4797013325985645195080773)
            ·
              refine ⟨899439998622308474077645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4797013325985645195080773 899439998622308474077645)
              ·
                refine ⟨337289999483365677779117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899439998622308474077645 337289999483365677779117)
                ·
                  refine ⟨126483749806262129167169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337289999483365677779117 126483749806262129167169)
                  ·
                    rfl

theorem cell21_554234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_554234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554234 prefixEnd_554234 := by exact prefixLift 554234
  have htrace : WordTrace (prefixWord ++ tailWord_554234) baseStart_554234 baseEnd_554234 := by
    simpa [prefixWord, tailWord_554234, baseEnd_554234] using wordTrace_append hprefix tailTrace_554234
  have hstable : (prefixWord ++ tailWord_554234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554234).length < 2 ^ (prefixWord ++ tailWord_554234).sum := by decide
  have hdescent : baseEnd_554234 < baseStart_554234 := by decide
  rcases family_descends (prefixWord ++ tailWord_554234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554245 : List Nat := [1, 3, 1, 1, 2, 1, 12]
def baseStart_554245 : Nat := 118140960795 + 554245 * 2 ^ 59
def prefixEnd_554245 : Nat := 4983230072969 + 3 ^ 40 * 554245 * 2
def baseEnd_554245 : Nat := 14054028906236506053757

theorem tailTrace_554245 : CollatzResearch.WordTrace tailWord_554245 prefixEnd_554245 14054028906236506053757 := by
  unfold tailWord_554245
  simp only [CollatzResearch.WordTrace]
  refine ⟨20214975877072497355040189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13476650584714998236693459 20214975877072497355040189)
  ·
    refine ⟨7580615953902186508140071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20214975877072497355040189 7580615953902186508140071)
    ·
      refine ⟨11370923930853279762210107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7580615953902186508140071 11370923930853279762210107)
      ·
        refine ⟨17056385896279919643315161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11370923930853279762210107 17056385896279919643315161)
        ·
          refine ⟨12792289422209939732486371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17056385896279919643315161 12792289422209939732486371)
          ·
            refine ⟨19188434133314909598729557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12792289422209939732486371 19188434133314909598729557)
            ·
              refine ⟨14054028906236506053757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 19188434133314909598729557 14054028906236506053757)
              ·
                rfl

theorem cell21_554245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 12].length) (baseStart_554245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554245 prefixEnd_554245 := by exact prefixLift 554245
  have htrace : WordTrace (prefixWord ++ tailWord_554245) baseStart_554245 baseEnd_554245 := by
    simpa [prefixWord, tailWord_554245, baseEnd_554245] using wordTrace_append hprefix tailTrace_554245
  have hstable : (prefixWord ++ tailWord_554245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554245).length < 2 ^ (prefixWord ++ tailWord_554245).sum := by decide
  have hdescent : baseEnd_554245 < baseStart_554245 := by decide
  rcases family_descends (prefixWord ++ tailWord_554245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554248 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 6]
def baseStart_554248 : Nat := 118140960795 + 554248 * 2 ^ 59
def prefixEnd_554248 : Nat := 4983230072969 + 3 ^ 40 * 554248 * 2
def baseEnd_554248 : Nat := 126486944797001215933807

theorem tailTrace_554248 : CollatzResearch.WordTrace tailWord_554248 prefixEnd_554248 126486944797001215933807 := by
  unfold tailWord_554248
  simp only [CollatzResearch.WordTrace]
  refine ⟨10107542648030814433699699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13476723530707752578266265 10107542648030814433699699)
  ·
    refine ⟨15161313972046221650549549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10107542648030814433699699 15161313972046221650549549)
    ·
      refine ⟨5685492739517333118956081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15161313972046221650549549 5685492739517333118956081)
      ·
        refine ⟨4264119554637999839217061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5685492739517333118956081 4264119554637999839217061)
        ·
          refine ⟨799522416494624969853199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4264119554637999839217061 799522416494624969853199)
          ·
            refine ⟨1199283624741937454779799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799522416494624969853199 1199283624741937454779799)
            ·
              refine ⟨1798925437112906182169699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1199283624741937454779799 1798925437112906182169699)
              ·
                refine ⟨2698388155669359273254549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1798925437112906182169699 2698388155669359273254549)
                ·
                  refine ⟨126486944797001215933807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2698388155669359273254549 126486944797001215933807)
                  ·
                    rfl

theorem cell21_554248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_554248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554248 prefixEnd_554248 := by exact prefixLift 554248
  have htrace : WordTrace (prefixWord ++ tailWord_554248) baseStart_554248 baseEnd_554248 := by
    simpa [prefixWord, tailWord_554248, baseEnd_554248] using wordTrace_append hprefix tailTrace_554248
  have hstable : (prefixWord ++ tailWord_554248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554248).length < 2 ^ (prefixWord ++ tailWord_554248).sum := by decide
  have hdescent : baseEnd_554248 < baseStart_554248 := by decide
  rcases family_descends (prefixWord ++ tailWord_554248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554307 : List Nat := [1, 1, 1, 3, 1, 3, 1, 6, 4]
def baseStart_554307 : Nat := 118140960795 + 554307 * 2 ^ 59
def prefixEnd_554307 : Nat := 4983230072969 + 3 ^ 40 * 554307 * 2
def baseEnd_554307 : Nat := 126500409400830224450353

theorem tailTrace_554307 : CollatzResearch.WordTrace tailWord_554307 prefixEnd_554307 126500409400830224450353 := by
  unfold tailWord_554307
  simp only [CollatzResearch.WordTrace]
  refine ⟨20217237202847881943797175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13478158135231921295864783 20217237202847881943797175)
  ·
    refine ⟨30325855804271822915695763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20217237202847881943797175 30325855804271822915695763)
    ·
      refine ⟨45488783706407734373543645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30325855804271822915695763 45488783706407734373543645)
      ·
        refine ⟨17058293889902900390078867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45488783706407734373543645 17058293889902900390078867)
        ·
          refine ⟨25587440834854350585118301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17058293889902900390078867 25587440834854350585118301)
          ·
            refine ⟨9595290313070381469419363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25587440834854350585118301 9595290313070381469419363)
            ·
              refine ⟨14392935469605572204129045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9595290313070381469419363 14392935469605572204129045)
              ·
                refine ⟨674668850137761197068549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14392935469605572204129045 674668850137761197068549)
                ·
                  refine ⟨126500409400830224450353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674668850137761197068549 126500409400830224450353)
                  ·
                    rfl

theorem cell21_554307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 6, 4].length) (baseStart_554307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554307 prefixEnd_554307 := by exact prefixLift 554307
  have htrace : WordTrace (prefixWord ++ tailWord_554307) baseStart_554307 baseEnd_554307 := by
    simpa [prefixWord, tailWord_554307, baseEnd_554307] using wordTrace_append hprefix tailTrace_554307
  have hstable : (prefixWord ++ tailWord_554307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554307).length < 2 ^ (prefixWord ++ tailWord_554307).sum := by decide
  have hdescent : baseEnd_554307 < baseStart_554307 := by decide
  rcases family_descends (prefixWord ++ tailWord_554307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554324 : List Nat := [2, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_554324 : Nat := 118140960795 + 554324 * 2 ^ 59
def prefixEnd_554324 : Nat := 4983230072969 + 3 ^ 40 * 554324 * 2
def baseEnd_554324 : Nat := 126504289032441972666985

theorem tailTrace_554324 : CollatzResearch.WordTrace tailWord_554324 prefixEnd_554324 126504289032441972666985 := by
  unfold tailWord_554324
  simp only [CollatzResearch.WordTrace]
  refine ⟨10108928621893146923583013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13478571495857529231444017 10108928621893146923583013)
  ·
    refine ⟨1895424116604965048171815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10108928621893146923583013 1895424116604965048171815)
    ·
      refine ⟨2843136174907447572257723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895424116604965048171815 2843136174907447572257723)
      ·
        refine ⟨4264704262361171358386585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2843136174907447572257723 4264704262361171358386585)
        ·
          refine ⟨3198528196770878518789939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4264704262361171358386585 3198528196770878518789939)
          ·
            refine ⟨4797792295156317778184909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198528196770878518789939 4797792295156317778184909)
            ·
              refine ⟨1799172110683619166819341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4797792295156317778184909 1799172110683619166819341)
              ·
                refine ⟨674689541506357187557253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1799172110683619166819341 674689541506357187557253)
                ·
                  refine ⟨126504289032441972666985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674689541506357187557253 126504289032441972666985)
                  ·
                    rfl

theorem cell21_554324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_554324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554324 prefixEnd_554324 := by exact prefixLift 554324
  have htrace : WordTrace (prefixWord ++ tailWord_554324) baseStart_554324 baseEnd_554324 := by
    simpa [prefixWord, tailWord_554324, baseEnd_554324] using wordTrace_append hprefix tailTrace_554324
  have hstable : (prefixWord ++ tailWord_554324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554324).length < 2 ^ (prefixWord ++ tailWord_554324).sum := by decide
  have hdescent : baseEnd_554324 < baseStart_554324 := by decide
  rcases family_descends (prefixWord ++ tailWord_554324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554338 : List Nat := [3, 3, 2, 1, 1, 1, 1, 9]
def baseStart_554338 : Nat := 118140960795 + 554338 * 2 ^ 59
def prefixEnd_554338 : Nat := 4983230072969 + 3 ^ 40 * 554338 * 2
def baseEnd_554338 : Nat := 42169161341060353144541

theorem tailTrace_554338 : CollatzResearch.WordTrace tailWord_554338 prefixEnd_554338 42169161341060353144541 := by
  unfold tailWord_554338
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054591966433893559543917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13478911910490382825450445 5054591966433893559543917)
  ·
    refine ⟨1895471987412710084828969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5054591966433893559543917 1895471987412710084828969)
    ·
      refine ⟨1421603990559532563621727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1895471987412710084828969 1421603990559532563621727)
      ·
        refine ⟨2132405985839298845432591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421603990559532563621727 2132405985839298845432591)
        ·
          refine ⟨3198608978758948268148887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2132405985839298845432591 3198608978758948268148887)
          ·
            refine ⟨4797913468138422402223331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3198608978758948268148887 4797913468138422402223331)
            ·
              refine ⟨7196870202207633603334997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4797913468138422402223331 7196870202207633603334997)
              ·
                refine ⟨42169161341060353144541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7196870202207633603334997 42169161341060353144541)
                ·
                  rfl

theorem cell21_554338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_554338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554338 prefixEnd_554338 := by exact prefixLift 554338
  have htrace : WordTrace (prefixWord ++ tailWord_554338) baseStart_554338 baseEnd_554338 := by
    simpa [prefixWord, tailWord_554338, baseEnd_554338] using wordTrace_append hprefix tailTrace_554338
  have hstable : (prefixWord ++ tailWord_554338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554338).length < 2 ^ (prefixWord ++ tailWord_554338).sum := by decide
  have hdescent : baseEnd_554338 < baseStart_554338 := by decide
  rcases family_descends (prefixWord ++ tailWord_554338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554493 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 4]
def baseStart_554493 : Nat := 118140960795 + 554493 * 2 ^ 59
def prefixEnd_554493 : Nat := 4983230072969 + 3 ^ 40 * 554493 * 2
def baseEnd_554493 : Nat := 126542857134935234349973

theorem tailTrace_554493 : CollatzResearch.WordTrace tailWord_554493 prefixEnd_554493 126542857134935234349973 := by
  unfold tailWord_554493
  simp only [CollatzResearch.WordTrace]
  refine ⟨20224021180174035710068133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13482680786782690473378755 20224021180174035710068133)
  ·
    refine ⟨3792003971282631695637775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20224021180174035710068133 3792003971282631695637775)
    ·
      refine ⟨5688005956923947543456663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3792003971282631695637775 5688005956923947543456663)
      ·
        refine ⟨8532008935385921315184995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5688005956923947543456663 8532008935385921315184995)
        ·
          refine ⟨12798013403078881972777493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8532008935385921315184995 12798013403078881972777493)
          ·
            refine ⟨599906878269322592473945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12798013403078881972777493 599906878269322592473945)
            ·
              refine ⟨449930158701991944355459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 599906878269322592473945 449930158701991944355459)
              ·
                refine ⟨674895238052987916533189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 449930158701991944355459 674895238052987916533189)
                ·
                  refine ⟨126542857134935234349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 674895238052987916533189 126542857134935234349973)
                  ·
                    rfl

theorem cell21_554493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_554493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554493 prefixEnd_554493 := by exact prefixLift 554493
  have htrace : WordTrace (prefixWord ++ tailWord_554493) baseStart_554493 baseEnd_554493 := by
    simpa [prefixWord, tailWord_554493, baseEnd_554493] using wordTrace_append hprefix tailTrace_554493
  have hstable : (prefixWord ++ tailWord_554493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554493).length < 2 ^ (prefixWord ++ tailWord_554493).sum := by decide
  have hdescent : baseEnd_554493 < baseStart_554493 := by decide
  rcases family_descends (prefixWord ++ tailWord_554493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554504 : List Nat := [2, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_554504 : Nat := 118140960795 + 554504 * 2 ^ 59
def prefixEnd_554504 : Nat := 4983230072969 + 3 ^ 40 * 554504 * 2
def baseEnd_554504 : Nat := 126545367484801659666617

theorem tailTrace_554504 : CollatzResearch.WordTrace tailWord_554504 prefixEnd_554504 126545367484801659666617 := by
  unfold tailWord_554504
  simp only [CollatzResearch.WordTrace]
  refine ⟨10112211191567092294359283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13482948255422789725812377 10112211191567092294359283)
  ·
    refine ⟨15168316787350638441538925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10112211191567092294359283 15168316787350638441538925)
    ·
      refine ⟨5688118795256489415577097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15168316787350638441538925 5688118795256489415577097)
      ·
        refine ⟨4266089096442367061682823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5688118795256489415577097 4266089096442367061682823)
        ·
          refine ⟨6399133644663550592524235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266089096442367061682823 6399133644663550592524235)
          ·
            refine ⟨9598700466995325888786353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6399133644663550592524235 9598700466995325888786353)
            ·
              refine ⟨7199025350246494416589765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9598700466995325888786353 7199025350246494416589765)
              ·
                refine ⟨1349817253171217703110581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7199025350246494416589765 1349817253171217703110581)
                ·
                  refine ⟨126545367484801659666617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1349817253171217703110581 126545367484801659666617)
                  ·
                    rfl

theorem cell21_554504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_554504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554504 prefixEnd_554504 := by exact prefixLift 554504
  have htrace : WordTrace (prefixWord ++ tailWord_554504) baseStart_554504 baseEnd_554504 := by
    simpa [prefixWord, tailWord_554504, baseEnd_554504] using wordTrace_append hprefix tailTrace_554504
  have hstable : (prefixWord ++ tailWord_554504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554504).length < 2 ^ (prefixWord ++ tailWord_554504).sum := by decide
  have hdescent : baseEnd_554504 < baseStart_554504 := by decide
  rcases family_descends (prefixWord ++ tailWord_554504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554538 : List Nat := [3, 1, 4, 1, 1, 1, 3, 4, 3]
def baseStart_554538 : Nat := 118140960795 + 554538 * 2 ^ 59
def prefixEnd_554538 : Nat := 4983230072969 + 3 ^ 40 * 554538 * 2
def baseEnd_554538 : Nat := 126553126748025156099881

theorem tailTrace_554538 : CollatzResearch.WordTrace tailWord_554538 prefixEnd_554538 126553126748025156099881 := by
  unfold tailWord_554538
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056415616252752098864067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13483774976674005596970845 5056415616252752098864067)
  ·
    refine ⟨7584623424379128148296101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056415616252752098864067 7584623424379128148296101)
    ·
      refine ⟨1422116892071086527805519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7584623424379128148296101 1422116892071086527805519)
      ·
        refine ⟨2133175338106629791708279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422116892071086527805519 2133175338106629791708279)
        ·
          refine ⟨3199763007159944687562419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2133175338106629791708279 3199763007159944687562419)
          ·
            refine ⟨4799644510739917031343629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3199763007159944687562419 4799644510739917031343629)
            ·
              refine ⟨1799866691527468886753861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4799644510739917031343629 1799866691527468886753861)
              ·
                refine ⟨337475004661400416266349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1799866691527468886753861 337475004661400416266349)
                ·
                  refine ⟨126553126748025156099881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337475004661400416266349 126553126748025156099881)
                  ·
                    rfl

theorem cell21_554538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 4, 3].length) (baseStart_554538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554538 prefixEnd_554538 := by exact prefixLift 554538
  have htrace : WordTrace (prefixWord ++ tailWord_554538) baseStart_554538 baseEnd_554538 := by
    simpa [prefixWord, tailWord_554538, baseEnd_554538] using wordTrace_append hprefix tailTrace_554538
  have hstable : (prefixWord ++ tailWord_554538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554538).length < 2 ^ (prefixWord ++ tailWord_554538).sum := by decide
  have hdescent : baseEnd_554538 < baseStart_554538 := by decide
  rcases family_descends (prefixWord ++ tailWord_554538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554580 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_554580 : Nat := 118140960795 + 554580 * 2 ^ 59
def prefixEnd_554580 : Nat := 4983230072969 + 3 ^ 40 * 554580 * 2
def baseEnd_554580 : Nat := 126562711720242416399795

theorem tailTrace_554580 : CollatzResearch.WordTrace tailWord_554580 prefixEnd_554580 126562711720242416399795 := by
  unfold tailWord_554580
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113597165429424784242597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13484796220572566378990129 10113597165429424784242597)
  ·
    refine ⟨1896299468518017147045487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10113597165429424784242597 1896299468518017147045487)
    ·
      refine ⟨2844449202777025720568231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1896299468518017147045487 2844449202777025720568231)
      ·
        refine ⟨4266673804165538580852347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2844449202777025720568231 4266673804165538580852347)
        ·
          refine ⟨6400010706248307871278521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4266673804165538580852347 6400010706248307871278521)
          ·
            refine ⟨4800008029686230903458891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6400010706248307871278521 4800008029686230903458891)
            ·
              refine ⟨7200012044529346355188337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4800008029686230903458891 7200012044529346355188337)
              ·
                refine ⟨5400009033397009766391253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7200012044529346355188337 5400009033397009766391253)
                ·
                  refine ⟨126562711720242416399795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5400009033397009766391253 126562711720242416399795)
                  ·
                    rfl

theorem cell21_554580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_554580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554580 prefixEnd_554580 := by exact prefixLift 554580
  have htrace : WordTrace (prefixWord ++ tailWord_554580) baseStart_554580 baseEnd_554580 := by
    simpa [prefixWord, tailWord_554580, baseEnd_554580] using wordTrace_append hprefix tailTrace_554580
  have hstable : (prefixWord ++ tailWord_554580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554580).length < 2 ^ (prefixWord ++ tailWord_554580).sum := by decide
  have hdescent : baseEnd_554580 < baseStart_554580 := by decide
  rcases family_descends (prefixWord ++ tailWord_554580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554597 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_554597 : Nat := 118140960795 + 554597 * 2 ^ 59
def prefixEnd_554597 : Nat := 4983230072969 + 3 ^ 40 * 554597 * 2
def baseEnd_554597 : Nat := 126566591351854164616427

theorem tailTrace_554597 : CollatzResearch.WordTrace tailWord_554597 prefixEnd_554597 126566591351854164616427 := by
  unfold tailWord_554597
  simp only [CollatzResearch.WordTrace]
  refine ⟨20227814371797261471854045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13485209581198174314569363 20227814371797261471854045)
  ·
    refine ⟨7585430389423973051945267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20227814371797261471854045 7585430389423973051945267)
    ·
      refine ⟨11378145584135959577917901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7585430389423973051945267 11378145584135959577917901)
      ·
        refine ⟨4266804594050984841719213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11378145584135959577917901 4266804594050984841719213)
        ·
          refine ⟨1600051722769119315644705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4266804594050984841719213 1600051722769119315644705)
          ·
            refine ⟨1200038792076839486733529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1600051722769119315644705 1200038792076839486733529)
            ·
              refine ⟨900029094057629615050147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200038792076839486733529 900029094057629615050147)
              ·
                refine ⟨1350043641086444422575221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900029094057629615050147 1350043641086444422575221)
                ·
                  refine ⟨126566591351854164616427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1350043641086444422575221 126566591351854164616427)
                  ·
                    rfl

theorem cell21_554597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_554597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554597 prefixEnd_554597 := by exact prefixLift 554597
  have htrace : WordTrace (prefixWord ++ tailWord_554597) baseStart_554597 baseEnd_554597 := by
    simpa [prefixWord, tailWord_554597, baseEnd_554597] using wordTrace_append hprefix tailTrace_554597
  have hstable : (prefixWord ++ tailWord_554597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554597).length < 2 ^ (prefixWord ++ tailWord_554597).sum := by decide
  have hdescent : baseEnd_554597 < baseStart_554597 := by decide
  rcases family_descends (prefixWord ++ tailWord_554597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554746 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_554746 : Nat := 118140960795 + 554746 * 2 ^ 59
def prefixEnd_554746 : Nat := 4983230072969 + 3 ^ 40 * 554746 * 2
def baseEnd_554746 : Nat := 126600595181863016632789

theorem tailTrace_554746 : CollatzResearch.WordTrace tailWord_554746 prefixEnd_554746 126600595181863016632789 := by
  unfold tailWord_554746
  simp only [CollatzResearch.WordTrace]
  refine ⟨5058312212064364979757023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13488832565504973279352061 5058312212064364979757023)
  ·
    refine ⟨7587468318096547469635535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5058312212064364979757023 7587468318096547469635535)
    ·
      refine ⟨11381202477144821204453303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7587468318096547469635535 11381202477144821204453303)
      ·
        refine ⟨17071803715717231806679955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11381202477144821204453303 17071803715717231806679955)
        ·
          refine ⟨25607705573575847710019933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17071803715717231806679955 25607705573575847710019933)
          ·
            refine ⟨9602889590090942891257475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25607705573575847710019933 9602889590090942891257475)
            ·
              refine ⟨14404334385136414336886213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9602889590090942891257475 14404334385136414336886213)
              ·
                refine ⟨2700812697213077688166165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14404334385136414336886213 2700812697213077688166165)
                ·
                  refine ⟨126600595181863016632789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2700812697213077688166165 126600595181863016632789)
                  ·
                    rfl

theorem cell21_554746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_554746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554746 prefixEnd_554746 := by exact prefixLift 554746
  have htrace : WordTrace (prefixWord ++ tailWord_554746) baseStart_554746 baseEnd_554746 := by
    simpa [prefixWord, tailWord_554746, baseEnd_554746] using wordTrace_append hprefix tailTrace_554746
  have hstable : (prefixWord ++ tailWord_554746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554746).length < 2 ^ (prefixWord ++ tailWord_554746).sum := by decide
  have hdescent : baseEnd_554746 < baseStart_554746 := by decide
  rcases family_descends (prefixWord ++ tailWord_554746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554763 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 4]
def baseStart_554763 : Nat := 118140960795 + 554763 * 2 ^ 59
def prefixEnd_554763 : Nat := 4983230072969 + 3 ^ 40 * 554763 * 2
def baseEnd_554763 : Nat := 126604474813474764849421

theorem tailTrace_554763 : CollatzResearch.WordTrace tailWord_554763 prefixEnd_554763 126604474813474764849421 := by
  unfold tailWord_554763
  simp only [CollatzResearch.WordTrace]
  refine ⟨20233868889195871822396943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13489245926130581214931295 20233868889195871822396943)
  ·
    refine ⟨30350803333793807733595415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20233868889195871822396943 30350803333793807733595415)
    ·
      refine ⟨45526205000690711600393123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30350803333793807733595415 45526205000690711600393123)
      ·
        refine ⟨68289307501036067400589685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45526205000690711600393123 68289307501036067400589685)
        ·
          refine ⟨6402122578222131318805283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68289307501036067400589685 6402122578222131318805283)
          ·
            refine ⟨9603183867333196978207925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6402122578222131318805283 9603183867333196978207925)
            ·
              refine ⟨900298487562487216706993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9603183867333196978207925 900298487562487216706993)
              ·
                refine ⟨675223865671865412530245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900298487562487216706993 675223865671865412530245)
                ·
                  refine ⟨126604474813474764849421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675223865671865412530245 126604474813474764849421)
                  ·
                    rfl

theorem cell21_554763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 4].length) (baseStart_554763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554763 prefixEnd_554763 := by exact prefixLift 554763
  have htrace : WordTrace (prefixWord ++ tailWord_554763) baseStart_554763 baseEnd_554763 := by
    simpa [prefixWord, tailWord_554763, baseEnd_554763] using wordTrace_append hprefix tailTrace_554763
  have hstable : (prefixWord ++ tailWord_554763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554763).length < 2 ^ (prefixWord ++ tailWord_554763).sum := by decide
  have hdescent : baseEnd_554763 < baseStart_554763 := by decide
  rcases family_descends (prefixWord ++ tailWord_554763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554780 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_554780 : Nat := 118140960795 + 554780 * 2 ^ 59
def prefixEnd_554780 : Nat := 4983230072969 + 3 ^ 40 * 554780 * 2
def baseEnd_554780 : Nat := 126608354445086513066053

theorem tailTrace_554780 : CollatzResearch.WordTrace tailWord_554780 prefixEnd_554780 126608354445086513066053 := by
  unfold tailWord_554780
  simp only [CollatzResearch.WordTrace]
  refine ⟨10117244465067141862882897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13489659286756189150510529 10117244465067141862882897)
  ·
    refine ⟨7587933348800356397162173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10117244465067141862882897 7587933348800356397162173)
    ·
      refine ⟨2845475005800133648935815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7587933348800356397162173 2845475005800133648935815)
      ·
        refine ⟨4268212508700200473403723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2845475005800133648935815 4268212508700200473403723)
        ·
          refine ⟨6402318763050300710105585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4268212508700200473403723 6402318763050300710105585)
          ·
            refine ⟨4801739072287725532579189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6402318763050300710105585 4801739072287725532579189)
            ·
              refine ⟨450163038026974268679299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4801739072287725532579189 450163038026974268679299)
              ·
                refine ⟨675244557040461403018949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450163038026974268679299 675244557040461403018949)
                ·
                  refine ⟨126608354445086513066053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675244557040461403018949 126608354445086513066053)
                  ·
                    rfl

theorem cell21_554780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_554780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554780 prefixEnd_554780 := by exact prefixLift 554780
  have htrace : WordTrace (prefixWord ++ tailWord_554780) baseStart_554780 baseEnd_554780 := by
    simpa [prefixWord, tailWord_554780, baseEnd_554780] using wordTrace_append hprefix tailTrace_554780
  have hstable : (prefixWord ++ tailWord_554780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554780).length < 2 ^ (prefixWord ++ tailWord_554780).sum := by decide
  have hdescent : baseEnd_554780 < baseStart_554780 := by decide
  rcases family_descends (prefixWord ++ tailWord_554780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554870 : List Nat := [5, 1, 1, 3, 2, 9]
def baseStart_554870 : Nat := 118140960795 + 554870 * 2 ^ 59
def prefixEnd_554870 : Nat := 4983230072969 + 3 ^ 40 * 554870 * 2
def baseEnd_554870 : Nat := 4689959024861716909847

theorem tailTrace_554870 : CollatzResearch.WordTrace tailWord_554870 prefixEnd_554870 4689959024861716909847 := by
  unfold tailWord_554870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264860718738014318533879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 13491847666538819397694709 1264860718738014318533879)
  ·
    refine ⟨1897291078107021477800819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264860718738014318533879 1897291078107021477800819)
    ·
      refine ⟨2845936617160532216701229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1897291078107021477800819 2845936617160532216701229)
      ·
        refine ⟨1067226231435199581262961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2845936617160532216701229 1067226231435199581262961)
        ·
          refine ⟨800419673576399685947221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067226231435199581262961 800419673576399685947221)
          ·
            refine ⟨4689959024861716909847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 800419673576399685947221 4689959024861716909847)
            ·
              rfl

theorem cell21_554870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 9].length) (baseStart_554870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554870 prefixEnd_554870 := by exact prefixLift 554870
  have htrace : WordTrace (prefixWord ++ tailWord_554870) baseStart_554870 baseEnd_554870 := by
    simpa [prefixWord, tailWord_554870, baseEnd_554870] using wordTrace_append hprefix tailTrace_554870
  have hstable : (prefixWord ++ tailWord_554870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554870).length < 2 ^ (prefixWord ++ tailWord_554870).sum := by decide
  have hdescent : baseEnd_554870 < baseStart_554870 := by decide
  rcases family_descends (prefixWord ++ tailWord_554870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554887 : List Nat := [1, 1, 4, 2, 5, 1, 1, 6]
def baseStart_554887 : Nat := 118140960795 + 554887 * 2 ^ 59
def prefixEnd_554887 : Nat := 4983230072969 + 3 ^ 40 * 554887 * 2
def baseEnd_554887 : Nat := 42210924434292701594167

theorem tailTrace_554887 : CollatzResearch.WordTrace tailWord_554887 prefixEnd_554887 42210924434292701594167 := by
  unfold tailWord_554887
  simp only [CollatzResearch.WordTrace]
  refine ⟨20238391540746640999910915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13492261027164427333273943 20238391540746640999910915)
  ·
    refine ⟨30357587311119961499866373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20238391540746640999910915 30357587311119961499866373)
    ·
      refine ⟨5692047620834992781224945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30357587311119961499866373 5692047620834992781224945)
      ·
        refine ⟨4269035715626244585918709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5692047620834992781224945 4269035715626244585918709)
        ·
          refine ⟨400222098339960429929879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4269035715626244585918709 400222098339960429929879)
          ·
            refine ⟨600333147509940644894819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400222098339960429929879 600333147509940644894819)
            ·
              refine ⟨900499721264910967342229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600333147509940644894819 900499721264910967342229)
              ·
                refine ⟨42210924434292701594167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 900499721264910967342229 42210924434292701594167)
                ·
                  rfl

theorem cell21_554887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 6].length) (baseStart_554887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554887 prefixEnd_554887 := by exact prefixLift 554887
  have htrace : WordTrace (prefixWord ++ tailWord_554887) baseStart_554887 baseEnd_554887 := by
    simpa [prefixWord, tailWord_554887, baseEnd_554887] using wordTrace_append hprefix tailTrace_554887
  have hstable : (prefixWord ++ tailWord_554887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554887).length < 2 ^ (prefixWord ++ tailWord_554887).sum := by decide
  have hdescent : baseEnd_554887 < baseStart_554887 := by decide
  rcases family_descends (prefixWord ++ tailWord_554887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554929 : List Nat := [1, 2, 2, 4, 2, 2, 8]
def baseStart_554929 : Nat := 118140960795 + 554929 * 2 ^ 59
def prefixEnd_554929 : Nat := 4983230072969 + 3 ^ 40 * 554929 * 2
def baseEnd_554929 : Nat := 14071373141677262786935

theorem tailTrace_554929 : CollatzResearch.WordTrace tailWord_554929 prefixEnd_554929 14071373141677262786935 := by
  unfold tailWord_554929
  simp only [CollatzResearch.WordTrace]
  refine ⟨20239923406594482172939841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13493282271062988115293227 20239923406594482172939841)
  ·
    refine ⟨15179942554945861629704881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20239923406594482172939841 15179942554945861629704881)
    ·
      refine ⟨11384956916209396222278661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15179942554945861629704881 11384956916209396222278661)
      ·
        refine ⟨2134679421789261791677249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11384956916209396222278661 2134679421789261791677249)
        ·
          refine ⟨1601009566341946343757937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134679421789261791677249 1601009566341946343757937)
          ·
            refine ⟨1200757174756459757818453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601009566341946343757937 1200757174756459757818453)
            ·
              refine ⟨14071373141677262786935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1200757174756459757818453 14071373141677262786935)
              ·
                rfl

theorem cell21_554929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 8].length) (baseStart_554929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554929 prefixEnd_554929 := by exact prefixLift 554929
  have htrace : WordTrace (prefixWord ++ tailWord_554929) baseStart_554929 baseEnd_554929 := by
    simpa [prefixWord, tailWord_554929, baseEnd_554929] using wordTrace_append hprefix tailTrace_554929
  have hstable : (prefixWord ++ tailWord_554929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554929).length < 2 ^ (prefixWord ++ tailWord_554929).sum := by decide
  have hdescent : baseEnd_554929 < baseStart_554929 := by decide
  rcases family_descends (prefixWord ++ tailWord_554929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_554977 : List Nat := [1, 2, 3, 1, 2, 1, 5, 3, 3]
def baseStart_554977 : Nat := 118140960795 + 554977 * 2 ^ 59
def prefixEnd_554977 : Nat := 4983230072969 + 3 ^ 40 * 554977 * 2
def baseEnd_554977 : Nat := 126653312529057948282317

theorem tailTrace_554977 : CollatzResearch.WordTrace tailWord_554977 prefixEnd_554977 126653312529057948282317 := by
  unfold tailWord_554977
  simp only [CollatzResearch.WordTrace]
  refine ⟨20241674110420586370687185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13494449406947057580458123 20241674110420586370687185)
  ·
    refine ⟨15181255582815439778015389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20241674110420586370687185 15181255582815439778015389)
    ·
      refine ⟨5692970843555789916755771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15181255582815439778015389 5692970843555789916755771)
      ·
        refine ⟨8539456265333684875133657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692970843555789916755771 8539456265333684875133657)
        ·
          refine ⟨6404592199000263656350243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8539456265333684875133657 6404592199000263656350243)
          ·
            refine ⟨9606888298500395484525365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6404592199000263656350243 9606888298500395484525365)
            ·
              refine ⟨900645777984412076674253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9606888298500395484525365 900645777984412076674253)
              ·
                refine ⟨337742166744154528752845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 900645777984412076674253 337742166744154528752845)
                ·
                  refine ⟨126653312529057948282317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337742166744154528752845 126653312529057948282317)
                  ·
                    rfl

theorem cell21_554977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_554977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_554977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_554977 prefixEnd_554977 := by exact prefixLift 554977
  have htrace : WordTrace (prefixWord ++ tailWord_554977) baseStart_554977 baseEnd_554977 := by
    simpa [prefixWord, tailWord_554977, baseEnd_554977] using wordTrace_append hprefix tailTrace_554977
  have hstable : (prefixWord ++ tailWord_554977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_554977).length < 2 ^ (prefixWord ++ tailWord_554977).sum := by decide
  have hdescent : baseEnd_554977 < baseStart_554977 := by decide
  rcases family_descends (prefixWord ++ tailWord_554977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555019 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_555019 : Nat := 118140960795 + 555019 * 2 ^ 59
def prefixEnd_555019 : Nat := 4983230072969 + 3 ^ 40 * 555019 * 2
def baseEnd_555019 : Nat := 126662897501275208582231

theorem tailTrace_555019 : CollatzResearch.WordTrace tailWord_555019 prefixEnd_555019 126662897501275208582231 := by
  unfold tailWord_555019
  simp only [CollatzResearch.WordTrace]
  refine ⟨20243205976268427543716111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13495470650845618362477407 20243205976268427543716111)
  ·
    refine ⟨30364808964402641315574167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20243205976268427543716111 30364808964402641315574167)
    ·
      refine ⟨45547213446603961973361251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30364808964402641315574167 45547213446603961973361251)
      ·
        refine ⟨68320820169905942960041877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45547213446603961973361251 68320820169905942960041877)
        ·
          refine ⟨3202538445464341076251963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 68320820169905942960041877 3202538445464341076251963)
          ·
            refine ⟨4803807668196511614377945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3202538445464341076251963 4803807668196511614377945)
            ·
              refine ⟨3602855751147383710783459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4803807668196511614377945 3602855751147383710783459)
              ·
                refine ⟨5404283626721075566175189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602855751147383710783459 5404283626721075566175189)
                ·
                  refine ⟨126662897501275208582231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5404283626721075566175189 126662897501275208582231)
                  ·
                    rfl

theorem cell21_555019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_555019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555019 prefixEnd_555019 := by exact prefixLift 555019
  have htrace : WordTrace (prefixWord ++ tailWord_555019) baseStart_555019 baseEnd_555019 := by
    simpa [prefixWord, tailWord_555019, baseEnd_555019] using wordTrace_append hprefix tailTrace_555019
  have hstable : (prefixWord ++ tailWord_555019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555019).length < 2 ^ (prefixWord ++ tailWord_555019).sum := by decide
  have hdescent : baseEnd_555019 < baseStart_555019 := by decide
  rcases family_descends (prefixWord ++ tailWord_555019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555081 : List Nat := [1, 2, 1, 1, 2, 2, 7, 5]
def baseStart_555081 : Nat := 118140960795 + 555081 * 2 ^ 59
def prefixEnd_555081 : Nat := 4983230072969 + 3 ^ 40 * 555081 * 2
def baseEnd_555081 : Nat := 42225682248658959516257

theorem tailTrace_555081 : CollatzResearch.WordTrace tailWord_555081 prefixEnd_555081 42225682248658959516257 := by
  unfold tailWord_555081
  simp only [CollatzResearch.WordTrace]
  refine ⟨20245467302043812132473097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13496978201362541421648731 20245467302043812132473097)
  ·
    refine ⟨15184100476532859099354823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20245467302043812132473097 15184100476532859099354823)
    ·
      refine ⟨22776150714799288649032235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15184100476532859099354823 22776150714799288649032235)
      ·
        refine ⟨34164226072198932973548353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22776150714799288649032235 34164226072198932973548353)
        ·
          refine ⟨25623169554149199730161265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34164226072198932973548353 25623169554149199730161265)
          ·
            refine ⟨19217377165611899797620949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25623169554149199730161265 19217377165611899797620949)
            ·
              refine ⟨450407277319028901506741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 19217377165611899797620949 450407277319028901506741)
              ·
                refine ⟨42225682248658959516257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 450407277319028901506741 42225682248658959516257)
                ·
                  rfl

theorem cell21_555081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 5].length) (baseStart_555081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555081 prefixEnd_555081 := by exact prefixLift 555081
  have htrace : WordTrace (prefixWord ++ tailWord_555081) baseStart_555081 baseEnd_555081 := by
    simpa [prefixWord, tailWord_555081, baseEnd_555081] using wordTrace_append hprefix tailTrace_555081
  have hstable : (prefixWord ++ tailWord_555081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555081).length < 2 ^ (prefixWord ++ tailWord_555081).sum := by decide
  have hdescent : baseEnd_555081 < baseStart_555081 := by decide
  rcases family_descends (prefixWord ++ tailWord_555081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555101 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 4]
def baseStart_555101 : Nat := 118140960795 + 555101 * 2 ^ 59
def prefixEnd_555101 : Nat := 4983230072969 + 3 ^ 40 * 555101 * 2
def baseEnd_555101 : Nat := 126681611018461288215397

theorem tailTrace_555101 : CollatzResearch.WordTrace tailWord_555101 prefixEnd_555101 126681611018461288215397 := by
  unfold tailWord_555101
  simp only [CollatzResearch.WordTrace]
  refine ⟨20246196761971355548201157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13497464507980903698800771 20246196761971355548201157)
  ·
    refine ⟨3796161892869629165287717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20246196761971355548201157 3796161892869629165287717)
    ·
      refine ⟨711780354913055468491447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3796161892869629165287717 711780354913055468491447)
      ·
        refine ⟨1067670532369583202737171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711780354913055468491447 1067670532369583202737171)
        ·
          refine ⟨1601505798554374804105757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1067670532369583202737171 1601505798554374804105757)
          ·
            refine ⟨600564674457890551539659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1601505798554374804105757 600564674457890551539659)
            ·
              refine ⟨900847011686835827309489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600564674457890551539659 900847011686835827309489)
              ·
                refine ⟨675635258765126870482117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900847011686835827309489 675635258765126870482117)
                ·
                  refine ⟨126681611018461288215397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675635258765126870482117 126681611018461288215397)
                  ·
                    rfl

theorem cell21_555101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_555101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555101 prefixEnd_555101 := by exact prefixLift 555101
  have htrace : WordTrace (prefixWord ++ tailWord_555101) baseStart_555101 baseEnd_555101 := by
    simpa [prefixWord, tailWord_555101, baseEnd_555101] using wordTrace_append hprefix tailTrace_555101
  have hstable : (prefixWord ++ tailWord_555101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555101).length < 2 ^ (prefixWord ++ tailWord_555101).sum := by decide
  have hdescent : baseEnd_555101 < baseStart_555101 := by decide
  rcases family_descends (prefixWord ++ tailWord_555101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555146 : List Nat := [3, 1, 2, 3, 1, 4, 1, 3, 3]
def baseStart_555146 : Nat := 118140960795 + 555146 * 2 ^ 59
def prefixEnd_555146 : Nat := 4983230072969 + 3 ^ 40 * 555146 * 2
def baseEnd_555146 : Nat := 126691880631551209965305

theorem tailTrace_555146 : CollatzResearch.WordTrace tailWord_555146 prefixEnd_555146 126691880631551209965305 := by
  unfold tailWord_555146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5061959511702082058397323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13498558697872218822392861 5061959511702082058397323)
  ·
    refine ⟨7592939267553123087595985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5061959511702082058397323 7592939267553123087595985)
    ·
      refine ⟨5694704450664842315696989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7592939267553123087595985 5694704450664842315696989)
      ·
        refine ⟨2135514168999315868386371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5694704450664842315696989 2135514168999315868386371)
        ·
          refine ⟨3203271253498973802579557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2135514168999315868386371 3203271253498973802579557)
          ·
            refine ⟨600613360031057587983667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3203271253498973802579557 600613360031057587983667)
            ·
              refine ⟨900920040046586381975501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600613360031057587983667 900920040046586381975501)
              ·
                refine ⟨337845015017469893240813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 900920040046586381975501 337845015017469893240813)
                ·
                  refine ⟨126691880631551209965305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337845015017469893240813 126691880631551209965305)
                  ·
                    rfl

theorem cell21_555146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 3, 3].length) (baseStart_555146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555146 prefixEnd_555146 := by exact prefixLift 555146
  have htrace : WordTrace (prefixWord ++ tailWord_555146) baseStart_555146 baseEnd_555146 := by
    simpa [prefixWord, tailWord_555146, baseEnd_555146] using wordTrace_append hprefix tailTrace_555146
  have hstable : (prefixWord ++ tailWord_555146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555146).length < 2 ^ (prefixWord ++ tailWord_555146).sum := by decide
  have hdescent : baseEnd_555146 < baseStart_555146 := by decide
  rcases family_descends (prefixWord ++ tailWord_555146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555247 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_555247 : Nat := 118140960795 + 555247 * 2 ^ 59
def prefixEnd_555247 : Nat := 4983230072969 + 3 ^ 40 * 555247 * 2
def baseEnd_555247 : Nat := 126714930207597478781765

theorem tailTrace_555247 : CollatzResearch.WordTrace tailWord_555247 prefixEnd_555247 126714930207597478781765 := by
  unfold tailWord_555247
  simp only [CollatzResearch.WordTrace]
  refine ⟨20251521819442422483015995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13501014546294948322010663 20251521819442422483015995)
  ·
    refine ⟨30377282729163633724523993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20251521819442422483015995 30377282729163633724523993)
    ·
      refine ⟨22782962046872725293392995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30377282729163633724523993 22782962046872725293392995)
      ·
        refine ⟨34174443070309087940089493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22782962046872725293392995 34174443070309087940089493)
        ·
          refine ⟨1601927018920738497191695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34174443070309087940089493 1601927018920738497191695)
          ·
            refine ⟨2402890528381107745787543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601927018920738497191695 2402890528381107745787543)
            ·
              refine ⟨3604335792571661618681315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2402890528381107745787543 3604335792571661618681315)
              ·
                refine ⟨5406503688857492428021973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3604335792571661618681315 5406503688857492428021973)
                ·
                  refine ⟨126714930207597478781765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5406503688857492428021973 126714930207597478781765)
                  ·
                    rfl

theorem cell21_555247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_555247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555247 prefixEnd_555247 := by exact prefixLift 555247
  have htrace : WordTrace (prefixWord ++ tailWord_555247) baseStart_555247 baseEnd_555247 := by
    simpa [prefixWord, tailWord_555247, baseEnd_555247] using wordTrace_append hprefix tailTrace_555247
  have hstable : (prefixWord ++ tailWord_555247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555247).length < 2 ^ (prefixWord ++ tailWord_555247).sum := by decide
  have hdescent : baseEnd_555247 < baseStart_555247 := by decide
  rcases family_descends (prefixWord ++ tailWord_555247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555250 : List Nat := [3, 2, 1, 3, 2, 2, 3, 5]
def baseStart_555250 : Nat := 118140960795 + 555250 * 2 ^ 59
def prefixEnd_555250 : Nat := 4983230072969 + 3 ^ 40 * 555250 * 2
def baseEnd_555250 : Nat := 42238538282823380077253

theorem tailTrace_555250 : CollatzResearch.WordTrace tailWord_555250 prefixEnd_555250 42238538282823380077253 := by
  unfold tailWord_555250
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062907809607888498843801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 13501087492287702663583469 5062907809607888498843801)
  ·
    refine ⟨3797180857205916374132851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5062907809607888498843801 3797180857205916374132851)
    ·
      refine ⟨5695771285808874561199277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797180857205916374132851 5695771285808874561199277)
      ·
        refine ⟨2135914232178327960449729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5695771285808874561199277 2135914232178327960449729)
        ·
          refine ⟨1601935674133745970337297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2135914232178327960449729 1601935674133745970337297)
          ·
            refine ⟨1201451755600309477752973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1601935674133745970337297 1201451755600309477752973)
            ·
              refine ⟨450544408350116054157365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1201451755600309477752973 450544408350116054157365)
              ·
                refine ⟨42238538282823380077253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 450544408350116054157365 42238538282823380077253)
                ·
                  rfl

theorem cell21_555250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_555250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555250 prefixEnd_555250 := by exact prefixLift 555250
  have htrace : WordTrace (prefixWord ++ tailWord_555250) baseStart_555250 baseEnd_555250 := by
    simpa [prefixWord, tailWord_555250, baseEnd_555250] using wordTrace_append hprefix tailTrace_555250
  have hstable : (prefixWord ++ tailWord_555250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555250).length < 2 ^ (prefixWord ++ tailWord_555250).sum := by decide
  have hdescent : baseEnd_555250 < baseStart_555250 := by decide
  rcases family_descends (prefixWord ++ tailWord_555250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555264 : List Nat := [2, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_555264 : Nat := 118140960795 + 555264 * 2 ^ 59
def prefixEnd_555264 : Nat := 4983230072969 + 3 ^ 40 * 555264 * 2
def baseEnd_555264 : Nat := 126718809839209226998397

theorem tailTrace_555264 : CollatzResearch.WordTrace tailWord_555264 prefixEnd_555264 126718809839209226998397 := by
  unfold tailWord_555264
  simp only [CollatzResearch.WordTrace]
  refine ⟨10126070930190417193192423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13501427906920556257589897 10126070930190417193192423)
  ·
    refine ⟨15189106395285625789788635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10126070930190417193192423 15189106395285625789788635)
    ·
      refine ⟨22783659592928438684682953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15189106395285625789788635 22783659592928438684682953)
      ·
        refine ⟨17087744694696329013512215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22783659592928438684682953 17087744694696329013512215)
        ·
          refine ⟨25631617042044493520268323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17087744694696329013512215 25631617042044493520268323)
          ·
            refine ⟨38447425563066740280402485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25631617042044493520268323 38447425563066740280402485)
            ·
              refine ⟨3604446146537506901287733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38447425563066740280402485 3604446146537506901287733)
              ·
                refine ⟨337916826237891271995725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3604446146537506901287733 337916826237891271995725)
                ·
                  refine ⟨126718809839209226998397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337916826237891271995725 126718809839209226998397)
                  ·
                    rfl

theorem cell21_555264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_555264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555264 prefixEnd_555264 := by exact prefixLift 555264
  have htrace : WordTrace (prefixWord ++ tailWord_555264) baseStart_555264 baseEnd_555264 := by
    simpa [prefixWord, tailWord_555264, baseEnd_555264] using wordTrace_append hprefix tailTrace_555264
  have hstable : (prefixWord ++ tailWord_555264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555264).length < 2 ^ (prefixWord ++ tailWord_555264).sum := by decide
  have hdescent : baseEnd_555264 < baseStart_555264 := by decide
  rcases family_descends (prefixWord ++ tailWord_555264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555278 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_555278 : Nat := 118140960795 + 555278 * 2 ^ 59
def prefixEnd_555278 : Nat := 4983230072969 + 3 ^ 40 * 555278 * 2
def baseEnd_555278 : Nat := 126722004829948313765035

theorem tailTrace_555278 : CollatzResearch.WordTrace tailWord_555278 prefixEnd_555278 126722004829948313765035 := by
  unfold tailWord_555278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531581560291264347174311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13501768321553409851596325 2531581560291264347174311)
  ·
    refine ⟨3797372340436896520761467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2531581560291264347174311 3797372340436896520761467)
    ·
      refine ⟨5696058510655344781142201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797372340436896520761467 5696058510655344781142201)
      ·
        refine ⟨4272043882991508585856651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5696058510655344781142201 4272043882991508585856651)
        ·
          refine ⟨6408065824487262878784977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272043882991508585856651 6408065824487262878784977)
          ·
            refine ⟨4806049368365447159088733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6408065824487262878784977 4806049368365447159088733)
            ·
              refine ⟨1802268513137042684658275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4806049368365447159088733 1802268513137042684658275)
              ·
                refine ⟨2703402769705564026987413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802268513137042684658275 2703402769705564026987413)
                ·
                  refine ⟨126722004829948313765035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2703402769705564026987413 126722004829948313765035)
                  ·
                    rfl

theorem cell21_555278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_555278 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555278 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555278 prefixEnd_555278 := by exact prefixLift 555278
  have htrace : WordTrace (prefixWord ++ tailWord_555278) baseStart_555278 baseEnd_555278 := by
    simpa [prefixWord, tailWord_555278, baseEnd_555278] using wordTrace_append hprefix tailTrace_555278
  have hstable : (prefixWord ++ tailWord_555278).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555278).length < 2 ^ (prefixWord ++ tailWord_555278).sum := by decide
  have hdescent : baseEnd_555278 < baseStart_555278 := by decide
  rcases family_descends (prefixWord ++ tailWord_555278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555292 : List Nat := [2, 2, 3, 1, 1, 1, 1, 10]
def baseStart_555292 : Nat := 118140960795 + 555292 * 2 ^ 59
def prefixEnd_555292 : Nat := 4983230072969 + 3 ^ 40 * 555292 * 2
def baseEnd_555292 : Nat := 42241733273562466843891

theorem tailTrace_555292 : CollatzResearch.WordTrace tailWord_555292 prefixEnd_555292 42241733273562466843891 := by
  unfold tailWord_555292
  simp only [CollatzResearch.WordTrace]
  refine ⟨10126581552139697584202065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13502108736186263445602753 10126581552139697584202065)
  ·
    refine ⟨7594936164104773188151549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10126581552139697584202065 7594936164104773188151549)
    ·
      refine ⟨2848101061539289945556831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7594936164104773188151549 2848101061539289945556831)
      ·
        refine ⟨4272151592308934918335247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2848101061539289945556831 4272151592308934918335247)
        ·
          refine ⟨6408227388463402377502871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4272151592308934918335247 6408227388463402377502871)
          ·
            refine ⟨9612341082695103566254307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6408227388463402377502871 9612341082695103566254307)
            ·
              refine ⟨14418511624042655349381461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9612341082695103566254307 14418511624042655349381461)
              ·
                refine ⟨42241733273562466843891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14418511624042655349381461 42241733273562466843891)
                ·
                  rfl

theorem cell21_555292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_555292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555292 prefixEnd_555292 := by exact prefixLift 555292
  have htrace : WordTrace (prefixWord ++ tailWord_555292) baseStart_555292 baseEnd_555292 := by
    simpa [prefixWord, tailWord_555292, baseEnd_555292] using wordTrace_append hprefix tailTrace_555292
  have hstable : (prefixWord ++ tailWord_555292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555292).length < 2 ^ (prefixWord ++ tailWord_555292).sum := by decide
  have hdescent : baseEnd_555292 < baseStart_555292 := by decide
  rcases family_descends (prefixWord ++ tailWord_555292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555399 : List Nat := [1, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_555399 : Nat := 118140960795 + 555399 * 2 ^ 59
def prefixEnd_555399 : Nat := 4983230072969 + 3 ^ 40 * 555399 * 2
def baseEnd_555399 : Nat := 126749618678478992248121

theorem tailTrace_555399 : CollatzResearch.WordTrace tailWord_555399 prefixEnd_555399 126749618678478992248121 := by
  unfold tailWord_555399
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257065714891752442549251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13504710476594501628366167 20257065714891752442549251)
  ·
    refine ⟨30385598572337628663823877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20257065714891752442549251 30385598572337628663823877)
    ·
      refine ⟨5697299732313305374466977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30385598572337628663823877 5697299732313305374466977)
      ·
        refine ⟨4272974799234979030850233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5697299732313305374466977 4272974799234979030850233)
        ·
          refine ⟨3204731099426234273137675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4272974799234979030850233 3204731099426234273137675)
          ·
            refine ⟨4807096649139351409706513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204731099426234273137675 4807096649139351409706513)
            ·
              refine ⟨3605322486854513557279885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4807096649139351409706513 3605322486854513557279885)
              ·
                refine ⟨1351995932570442583979957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3605322486854513557279885 1351995932570442583979957)
                ·
                  refine ⟨126749618678478992248121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1351995932570442583979957 126749618678478992248121)
                  ·
                    rfl

theorem cell21_555399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_555399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555399 prefixEnd_555399 := by exact prefixLift 555399
  have htrace : WordTrace (prefixWord ++ tailWord_555399) baseStart_555399 baseEnd_555399 := by
    simpa [prefixWord, tailWord_555399, baseEnd_555399] using wordTrace_append hprefix tailTrace_555399
  have hstable : (prefixWord ++ tailWord_555399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555399).length < 2 ^ (prefixWord ++ tailWord_555399).sum := by decide
  have hdescent : baseEnd_555399 < baseStart_555399 := by decide
  rcases family_descends (prefixWord ++ tailWord_555399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555413 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_555413 : Nat := 118140960795 + 555413 * 2 ^ 59
def prefixEnd_555413 : Nat := 4983230072969 + 3 ^ 40 * 555413 * 2
def baseEnd_555413 : Nat := 126752813669218079014759

theorem tailTrace_555413 : CollatzResearch.WordTrace tailWord_555413 prefixEnd_555413 126752813669218079014759 := by
  unfold tailWord_555413
  simp only [CollatzResearch.WordTrace]
  refine ⟨20257576336841032833558893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13505050891227355222372595 20257576336841032833558893)
  ·
    refine ⟨7596591126315387312584585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20257576336841032833558893 7596591126315387312584585)
    ·
      refine ⟨5697443344736540484438439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7596591126315387312584585 5697443344736540484438439)
      ·
        refine ⟨8546165017104810726657659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5697443344736540484438439 8546165017104810726657659)
        ·
          refine ⟨12819247525657216089986489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8546165017104810726657659 12819247525657216089986489)
          ·
            refine ⟨9614435644242912067489867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12819247525657216089986489 9614435644242912067489867)
            ·
              refine ⟨14421653466364368101234801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9614435644242912067489867 14421653466364368101234801)
              ·
                refine ⟨10816240099773276075926101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14421653466364368101234801 10816240099773276075926101)
                ·
                  refine ⟨126752813669218079014759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10816240099773276075926101 126752813669218079014759)
                  ·
                    rfl

theorem cell21_555413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_555413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555413 prefixEnd_555413 := by exact prefixLift 555413
  have htrace : WordTrace (prefixWord ++ tailWord_555413) baseStart_555413 baseEnd_555413 := by
    simpa [prefixWord, tailWord_555413, baseEnd_555413] using wordTrace_append hprefix tailTrace_555413
  have hstable : (prefixWord ++ tailWord_555413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555413).length < 2 ^ (prefixWord ++ tailWord_555413).sum := by decide
  have hdescent : baseEnd_555413 < baseStart_555413 := by decide
  rcases family_descends (prefixWord ++ tailWord_555413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555416 : List Nat := [2, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_555416 : Nat := 118140960795 + 555416 * 2 ^ 59
def prefixEnd_555416 : Nat := 4983230072969 + 3 ^ 40 * 555416 * 2
def baseEnd_555416 : Nat := 126753498310090740464753

theorem tailTrace_555416 : CollatzResearch.WordTrace tailWord_555416 prefixEnd_555416 126753498310090740464753 := by
  unfold tailWord_555416
  simp only [CollatzResearch.WordTrace]
  refine ⟨10128842877915082172959051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13505123837220109563945401 10128842877915082172959051)
  ·
    refine ⟨15193264316872623259438577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10128842877915082172959051 15193264316872623259438577)
    ·
      refine ⟨11394948237654467444578933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15193264316872623259438577 11394948237654467444578933)
      ·
        refine ⟨1068276397280106322929275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11394948237654467444578933 1068276397280106322929275)
        ·
          refine ⟨1602414595920159484393913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068276397280106322929275 1602414595920159484393913)
          ·
            refine ⟨1201810946940119613295435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602414595920159484393913 1201810946940119613295435)
            ·
              refine ⟨1802716420410179419943153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201810946940119613295435 1802716420410179419943153)
              ·
                refine ⟨1352037315307634564957365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1802716420410179419943153 1352037315307634564957365)
                ·
                  refine ⟨126753498310090740464753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1352037315307634564957365 126753498310090740464753)
                  ·
                    rfl

theorem cell21_555416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_555416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555416 prefixEnd_555416 := by exact prefixLift 555416
  have htrace : WordTrace (prefixWord ++ tailWord_555416) baseStart_555416 baseEnd_555416 := by
    simpa [prefixWord, tailWord_555416, baseEnd_555416] using wordTrace_append hprefix tailTrace_555416
  have hstable : (prefixWord ++ tailWord_555416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555416).length < 2 ^ (prefixWord ++ tailWord_555416).sum := by decide
  have hdescent : baseEnd_555416 < baseStart_555416 := by decide
  rcases family_descends (prefixWord ++ tailWord_555416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555447 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 4]
def baseStart_555447 : Nat := 118140960795 + 555447 * 2 ^ 59
def prefixEnd_555447 : Nat := 4983230072969 + 3 ^ 40 * 555447 * 2
def baseEnd_555447 : Nat := 126760572932441575448023

theorem tailTrace_555447 : CollatzResearch.WordTrace tailWord_555447 prefixEnd_555447 126760572932441575448023 := by
  unfold tailWord_555447
  simp only [CollatzResearch.WordTrace]
  refine ⟨20258816418717856640296595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13505877612478571093531063 20258816418717856640296595)
  ·
    refine ⟨30388224628076784960444893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20258816418717856640296595 30388224628076784960444893)
    ·
      refine ⟨11395584235528794360166835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30388224628076784960444893 11395584235528794360166835)
      ·
        refine ⟨17093376353293191540250253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11395584235528794360166835 17093376353293191540250253)
        ·
          refine ⟨6410016132484946827593845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17093376353293191540250253 6410016132484946827593845)
          ·
            refine ⟨600939012420463765086923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6410016132484946827593845 600939012420463765086923)
            ·
              refine ⟨901408518630695647630385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600939012420463765086923 901408518630695647630385)
              ·
                refine ⟨676056388973021735722789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901408518630695647630385 676056388973021735722789)
                ·
                  refine ⟨126760572932441575448023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676056388973021735722789 126760572932441575448023)
                  ·
                    rfl

theorem cell21_555447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 4].length) (baseStart_555447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555447 prefixEnd_555447 := by exact prefixLift 555447
  have htrace : WordTrace (prefixWord ++ tailWord_555447) baseStart_555447 baseEnd_555447 := by
    simpa [prefixWord, tailWord_555447, baseEnd_555447] using wordTrace_append hprefix tailTrace_555447
  have hstable : (prefixWord ++ tailWord_555447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555447).length < 2 ^ (prefixWord ++ tailWord_555447).sum := by decide
  have hdescent : baseEnd_555447 < baseStart_555447 := by decide
  rcases family_descends (prefixWord ++ tailWord_555447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555489 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_555489 : Nat := 118140960795 + 555489 * 2 ^ 59
def prefixEnd_555489 : Nat := 4983230072969 + 3 ^ 40 * 555489 * 2
def baseEnd_555489 : Nat := 126770157904658835747937

theorem tailTrace_555489 : CollatzResearch.WordTrace tailWord_555489 prefixEnd_555489 126770157904658835747937 := by
  unfold tailWord_555489
  simp only [CollatzResearch.WordTrace]
  refine ⟨20260348284565697813325521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13506898856377131875550347 20260348284565697813325521)
  ·
    refine ⟨15195261213424273359994141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20260348284565697813325521 15195261213424273359994141)
    ·
      refine ⟨5698222955034102509997803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15195261213424273359994141 5698222955034102509997803)
      ·
        refine ⟨8547334432551153764996705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698222955034102509997803 8547334432551153764996705)
        ·
          refine ⟨6410500824413365323747529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8547334432551153764996705 6410500824413365323747529)
          ·
            refine ⟨4807875618310023992810647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6410500824413365323747529 4807875618310023992810647)
            ·
              refine ⟨7211813427465035989215971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4807875618310023992810647 7211813427465035989215971)
              ·
                refine ⟨10817720141197553983823957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7211813427465035989215971 10817720141197553983823957)
                ·
                  refine ⟨126770157904658835747937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10817720141197553983823957 126770157904658835747937)
                  ·
                    rfl

theorem cell21_555489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_555489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555489 prefixEnd_555489 := by exact prefixLift 555489
  have htrace : WordTrace (prefixWord ++ tailWord_555489) baseStart_555489 baseEnd_555489 := by
    simpa [prefixWord, tailWord_555489, baseEnd_555489] using wordTrace_append hprefix tailTrace_555489
  have hstable : (prefixWord ++ tailWord_555489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555489).length < 2 ^ (prefixWord ++ tailWord_555489).sum := by decide
  have hdescent : baseEnd_555489 < baseStart_555489 := by decide
  rcases family_descends (prefixWord ++ tailWord_555489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555588 : List Nat := [2, 3, 5, 1, 1, 1, 3, 5]
def baseStart_555588 : Nat := 118140960795 + 555588 * 2 ^ 59
def prefixEnd_555588 : Nat := 4983230072969 + 3 ^ 40 * 555588 * 2
def baseEnd_555588 : Nat := 42264250351152221199245

theorem tailTrace_555588 : CollatzResearch.WordTrace tailWord_555588 prefixEnd_555588 42264250351152221199245 := by
  unfold tailWord_555588
  simp only [CollatzResearch.WordTrace]
  refine ⟨10131979555603518860589709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13509306074138025147452945 10131979555603518860589709)
  ·
    refine ⟨3799492333351319572721141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10131979555603518860589709 3799492333351319572721141)
    ·
      refine ⟨356202406251686209942607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3799492333351319572721141 356202406251686209942607)
      ·
        refine ⟨534303609377529314913911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356202406251686209942607 534303609377529314913911)
        ·
          refine ⟨801455414066293972370867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534303609377529314913911 801455414066293972370867)
          ·
            refine ⟨1202183121099440958556301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 801455414066293972370867 1202183121099440958556301)
            ·
              refine ⟨450818670412290359458613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1202183121099440958556301 450818670412290359458613)
              ·
                refine ⟨42264250351152221199245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 450818670412290359458613 42264250351152221199245)
                ·
                  rfl

theorem cell21_555588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_555588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555588 prefixEnd_555588 := by exact prefixLift 555588
  have htrace : WordTrace (prefixWord ++ tailWord_555588) baseStart_555588 baseEnd_555588 := by
    simpa [prefixWord, tailWord_555588, baseEnd_555588] using wordTrace_append hprefix tailTrace_555588
  have hstable : (prefixWord ++ tailWord_555588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555588).length < 2 ^ (prefixWord ++ tailWord_555588).sum := by decide
  have hdescent : baseEnd_555588 < baseStart_555588 := by decide
  rcases family_descends (prefixWord ++ tailWord_555588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555678 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_555678 : Nat := 118140960795 + 555678 * 2 ^ 59
def prefixEnd_555678 : Nat := 4983230072969 + 3 ^ 40 * 555678 * 2
def baseEnd_555678 : Nat := 126813290279636507097551

theorem tailTrace_555678 : CollatzResearch.WordTrace tailWord_555678 prefixEnd_555678 126813290279636507097551 := by
  unfold tailWord_555678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533405210110122886494461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13511494453920655394637125 2533405210110122886494461)
  ·
    refine ⟨950026953791296082435423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2533405210110122886494461 950026953791296082435423)
    ·
      refine ⟨1425040430686944123653135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950026953791296082435423 1425040430686944123653135)
      ·
        refine ⟨2137560646030416185479703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1425040430686944123653135 2137560646030416185479703)
        ·
          refine ⟨3206340969045624278219555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137560646030416185479703 3206340969045624278219555)
          ·
            refine ⟨4809511453568436417329333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3206340969045624278219555 4809511453568436417329333)
            ·
              refine ⟨450891698772040914124625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4809511453568436417329333 450891698772040914124625)
              ·
                refine ⟨338168774079030685593469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 450891698772040914124625 338168774079030685593469)
                ·
                  refine ⟨126813290279636507097551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338168774079030685593469 126813290279636507097551)
                  ·
                    rfl

theorem cell21_555678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_555678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555678 prefixEnd_555678 := by exact prefixLift 555678
  have htrace : WordTrace (prefixWord ++ tailWord_555678) baseStart_555678 baseEnd_555678 := by
    simpa [prefixWord, tailWord_555678, baseEnd_555678] using wordTrace_append hprefix tailTrace_555678
  have hstable : (prefixWord ++ tailWord_555678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555678).length < 2 ^ (prefixWord ++ tailWord_555678).sum := by decide
  have hdescent : baseEnd_555678 < baseStart_555678 := by decide
  rcases family_descends (prefixWord ++ tailWord_555678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555748 : List Nat := [2, 3, 1, 1, 1, 4, 3, 6]
def baseStart_555748 : Nat := 118140960795 + 555748 * 2 ^ 59
def prefixEnd_555748 : Nat := 4983230072969 + 3 ^ 40 * 555748 * 2
def baseEnd_555748 : Nat := 42276421744443980310247

theorem tailTrace_555748 : CollatzResearch.WordTrace tailWord_555748 prefixEnd_555748 42276421744443980310247 := by
  unfold tailWord_555748
  simp only [CollatzResearch.WordTrace]
  refine ⟨10134897395313692523501949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13513196527084923364669265 10134897395313692523501949)
  ·
    refine ⟨3800586523242634696313231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10134897395313692523501949 3800586523242634696313231)
    ·
      refine ⟨5700879784863952044469847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3800586523242634696313231 5700879784863952044469847)
      ·
        refine ⟨8551319677295928066704771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5700879784863952044469847 8551319677295928066704771)
        ·
          refine ⟨12826979515943892100057157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8551319677295928066704771 12826979515943892100057157)
          ·
            refine ⟨2405058659239479768760717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12826979515943892100057157 2405058659239479768760717)
            ·
              refine ⟨901896997214804913285269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2405058659239479768760717 901896997214804913285269)
              ·
                refine ⟨42276421744443980310247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 901896997214804913285269 42276421744443980310247)
                ·
                  rfl

theorem cell21_555748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_555748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555748 prefixEnd_555748 := by exact prefixLift 555748
  have htrace : WordTrace (prefixWord ++ tailWord_555748) baseStart_555748 baseEnd_555748 := by
    simpa [prefixWord, tailWord_555748, baseEnd_555748] using wordTrace_append hprefix tailTrace_555748
  have hstable : (prefixWord ++ tailWord_555748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555748).length < 2 ^ (prefixWord ++ tailWord_555748).sum := by decide
  have hdescent : baseEnd_555748 < baseStart_555748 := by decide
  rcases family_descends (prefixWord ++ tailWord_555748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555883 : List Nat := [1, 1, 1, 1, 2, 2, 6, 7]
def baseStart_555883 : Nat := 118140960795 + 555883 * 2 ^ 59
def prefixEnd_555883 : Nat := 4983230072969 + 3 ^ 40 * 555883 * 2
def baseEnd_555883 : Nat := 42286691357533902060155

theorem tailTrace_555883 : CollatzResearch.WordTrace tailWord_555883 prefixEnd_555883 42286691357533902060155 := by
  unfold tailWord_555883
  simp only [CollatzResearch.WordTrace]
  refine ⟨20274718645138303103168303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13516479096758868735445535 20274718645138303103168303)
  ·
    refine ⟨30412077967707454654752455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20274718645138303103168303 30412077967707454654752455)
    ·
      refine ⟨45618116951561181982128683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30412077967707454654752455 45618116951561181982128683)
      ·
        refine ⟨68427175427341772973193025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45618116951561181982128683 68427175427341772973193025)
        ·
          refine ⟨51320381570506329729894769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68427175427341772973193025 51320381570506329729894769)
          ·
            refine ⟨38490286177879747297421077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51320381570506329729894769 38490286177879747297421077)
            ·
              refine ⟨1804232164588113154566613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38490286177879747297421077 1804232164588113154566613)
              ·
                refine ⟨42286691357533902060155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1804232164588113154566613 42286691357533902060155)
                ·
                  rfl

theorem cell21_555883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 7].length) (baseStart_555883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555883 prefixEnd_555883 := by exact prefixLift 555883
  have htrace : WordTrace (prefixWord ++ tailWord_555883) baseStart_555883 baseEnd_555883 := by
    simpa [prefixWord, tailWord_555883, baseEnd_555883] using wordTrace_append hprefix tailTrace_555883
  have hstable : (prefixWord ++ tailWord_555883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555883).length < 2 ^ (prefixWord ++ tailWord_555883).sum := by decide
  have hdescent : baseEnd_555883 < baseStart_555883 := by decide
  rcases family_descends (prefixWord ++ tailWord_555883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_555993 : List Nat := [1, 2, 1, 2, 5, 3, 2, 5]
def baseStart_555993 : Nat := 118140960795 + 555993 * 2 ^ 59
def prefixEnd_555993 : Nat := 4983230072969 + 3 ^ 40 * 555993 * 2
def baseEnd_555993 : Nat := 42295059190421986448969

theorem tailTrace_555993 : CollatzResearch.WordTrace tailWord_555993 prefixEnd_555993 42295059190421986448969 := by
  unfold tailWord_555993
  simp only [CollatzResearch.WordTrace]
  refine ⟨20278730674739791889672633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13519153783159861259781755 20278730674739791889672633)
  ·
    refine ⟨15209048006054843917254475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20278730674739791889672633 15209048006054843917254475)
    ·
      refine ⟨22813572009082265875881713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15209048006054843917254475 22813572009082265875881713)
      ·
        refine ⟨17110179006811699406911285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22813572009082265875881713 17110179006811699406911285)
        ·
          refine ⟨1604079281888596819397933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17110179006811699406911285 1604079281888596819397933)
          ·
            refine ⟨601529730708223807274225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1604079281888596819397933 601529730708223807274225)
            ·
              refine ⟨451147298031167855455669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 601529730708223807274225 451147298031167855455669)
              ·
                refine ⟨42295059190421986448969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 451147298031167855455669 42295059190421986448969)
                ·
                  rfl

theorem cell21_555993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 5].length) (baseStart_555993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_555993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_555993 prefixEnd_555993 := by exact prefixLift 555993
  have htrace : WordTrace (prefixWord ++ tailWord_555993) baseStart_555993 baseEnd_555993 := by
    simpa [prefixWord, tailWord_555993, baseEnd_555993] using wordTrace_append hprefix tailTrace_555993
  have hstable : (prefixWord ++ tailWord_555993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_555993).length < 2 ^ (prefixWord ++ tailWord_555993).sum := by decide
  have hdescent : baseEnd_555993 < baseStart_555993 := by decide
  rcases family_descends (prefixWord ++ tailWord_555993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556190 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_556190 : Nat := 118140960795 + 556190 * 2 ^ 59
def prefixEnd_556190 : Nat := 4983230072969 + 3 ^ 40 * 556190 * 2
def baseEnd_556190 : Nat := 126930135655237394563171

theorem tailTrace_556190 : CollatzResearch.WordTrace tailWord_556190 prefixEnd_556190 126930135655237394563171 := by
  unfold tailWord_556190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535739481878261816824253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 13523943903350729689729349 2535739481878261816824253)
  ·
    refine ⟨950902305704348181309095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2535739481878261816824253 950902305704348181309095)
    ·
      refine ⟨1426353458556522271963643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950902305704348181309095 1426353458556522271963643)
      ·
        refine ⟨2139530187834783407945465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1426353458556522271963643 2139530187834783407945465)
        ·
          refine ⟨1604647640876087555959099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2139530187834783407945465 1604647640876087555959099)
          ·
            refine ⟨2406971461314131333938649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604647640876087555959099 2406971461314131333938649)
            ·
              refine ⟨1805228595985598500453987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2406971461314131333938649 1805228595985598500453987)
              ·
                refine ⟨2707842893978397750680981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1805228595985598500453987 2707842893978397750680981)
                ·
                  refine ⟨126930135655237394563171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2707842893978397750680981 126930135655237394563171)
                  ·
                    rfl

theorem cell21_556190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_556190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556190 prefixEnd_556190 := by exact prefixLift 556190
  have htrace : WordTrace (prefixWord ++ tailWord_556190) baseStart_556190 baseEnd_556190 := by
    simpa [prefixWord, tailWord_556190, baseEnd_556190] using wordTrace_append hprefix tailTrace_556190
  have hstable : (prefixWord ++ tailWord_556190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556190).length < 2 ^ (prefixWord ++ tailWord_556190).sum := by decide
  have hdescent : baseEnd_556190 < baseStart_556190 := by decide
  rcases family_descends (prefixWord ++ tailWord_556190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556201 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 11]
def baseStart_556201 : Nat := 118140960795 + 556201 * 2 ^ 59
def prefixEnd_556201 : Nat := 4983230072969 + 3 ^ 40 * 556201 * 2
def baseEnd_556201 : Nat := 126932646005103819879815

theorem tailTrace_556201 : CollatzResearch.WordTrace tailWord_556201 prefixEnd_556201 126932646005103819879815 := by
  unfold tailWord_556201
  simp only [CollatzResearch.WordTrace]
  refine ⟨20286317057986243413244457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13524211371990828942162971 20286317057986243413244457)
  ·
    refine ⟨15214737793489682559933343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20286317057986243413244457 15214737793489682559933343)
    ·
      refine ⟨22822106690234523839900015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15214737793489682559933343 22822106690234523839900015)
      ·
        refine ⟨34233160035351785759850023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22822106690234523839900015 34233160035351785759850023)
        ·
          refine ⟨51349740053027678639775035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34233160035351785759850023 51349740053027678639775035)
          ·
            refine ⟨77024610079541517959662553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51349740053027678639775035 77024610079541517959662553)
            ·
              refine ⟨57768457559656138469746915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77024610079541517959662553 57768457559656138469746915)
              ·
                refine ⟨86652686339484207704620373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57768457559656138469746915 86652686339484207704620373)
                ·
                  refine ⟨126932646005103819879815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 86652686339484207704620373 126932646005103819879815)
                  ·
                    rfl

theorem cell21_556201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_556201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556201 prefixEnd_556201 := by exact prefixLift 556201
  have htrace : WordTrace (prefixWord ++ tailWord_556201) baseStart_556201 baseEnd_556201 := by
    simpa [prefixWord, tailWord_556201, baseEnd_556201] using wordTrace_append hprefix tailTrace_556201
  have hstable : (prefixWord ++ tailWord_556201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556201).length < 2 ^ (prefixWord ++ tailWord_556201).sum := by decide
  have hdescent : baseEnd_556201 < baseStart_556201 := by decide
  rcases family_descends (prefixWord ++ tailWord_556201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556232 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_556232 : Nat := 118140960795 + 556232 * 2 ^ 59
def prefixEnd_556232 : Nat := 4983230072969 + 3 ^ 40 * 556232 * 2
def baseEnd_556232 : Nat := 126939720627454654863085

theorem tailTrace_556232 : CollatzResearch.WordTrace tailWord_556232 prefixEnd_556232 126939720627454654863085 := by
  unfold tailWord_556232
  simp only [CollatzResearch.WordTrace]
  refine ⟨10143723860436967853811475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13524965147249290471748633 10143723860436967853811475)
  ·
    refine ⟨15215585790655451780717213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10143723860436967853811475 15215585790655451780717213)
    ·
      refine ⟨5705844671495794417768955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15215585790655451780717213 5705844671495794417768955)
      ·
        refine ⟨8558767007243691626653433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5705844671495794417768955 8558767007243691626653433)
        ·
          refine ⟨6419075255432768719990075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8558767007243691626653433 6419075255432768719990075)
          ·
            refine ⟨9628612883149153079985113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6419075255432768719990075 9628612883149153079985113)
            ·
              refine ⟨7221459662361864809988835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9628612883149153079985113 7221459662361864809988835)
              ·
                refine ⟨10832189493542797214983253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7221459662361864809988835 10832189493542797214983253)
                ·
                  refine ⟨126939720627454654863085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10832189493542797214983253 126939720627454654863085)
                  ·
                    rfl

theorem cell21_556232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_556232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556232 prefixEnd_556232 := by exact prefixLift 556232
  have htrace : WordTrace (prefixWord ++ tailWord_556232) baseStart_556232 baseEnd_556232 := by
    simpa [prefixWord, tailWord_556232, baseEnd_556232] using wordTrace_append hprefix tailTrace_556232
  have hstable : (prefixWord ++ tailWord_556232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556232).length < 2 ^ (prefixWord ++ tailWord_556232).sum := by decide
  have hdescent : baseEnd_556232 < baseStart_556232 := by decide
  rcases family_descends (prefixWord ++ tailWord_556232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556311 : List Nat := [1, 1, 3, 4, 1, 1, 1, 6, 3]
def baseStart_556311 : Nat := 118140960795 + 556311 * 2 ^ 59
def prefixEnd_556311 : Nat := 4983230072969 + 3 ^ 40 * 556311 * 2
def baseEnd_556311 : Nat := 126957749503768073046257

theorem tailTrace_556311 : CollatzResearch.WordTrace tailWord_556311 prefixEnd_556311 126957749503768073046257 := by
  unfold tailWord_556311
  simp only [CollatzResearch.WordTrace]
  refine ⟨20290329087587732199748787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13526886058391821466499191 20290329087587732199748787)
  ·
    refine ⟨30435493631381598299623181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20290329087587732199748787 30435493631381598299623181)
    ·
      refine ⟨11413310111768099362358693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30435493631381598299623181 11413310111768099362358693)
      ·
        refine ⟨2139995645956518630442255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11413310111768099362358693 2139995645956518630442255)
        ·
          refine ⟨3209993468934777945663383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2139995645956518630442255 3209993468934777945663383)
          ·
            refine ⟨4814990203402166918495075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3209993468934777945663383 4814990203402166918495075)
            ·
              refine ⟨7222485305103250377742613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4814990203402166918495075 7222485305103250377742613)
              ·
                refine ⟨338553998676714861456685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7222485305103250377742613 338553998676714861456685)
                ·
                  refine ⟨126957749503768073046257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338553998676714861456685 126957749503768073046257)
                  ·
                    rfl

theorem cell21_556311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 6, 3].length) (baseStart_556311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556311 prefixEnd_556311 := by exact prefixLift 556311
  have htrace : WordTrace (prefixWord ++ tailWord_556311) baseStart_556311 baseEnd_556311 := by
    simpa [prefixWord, tailWord_556311, baseEnd_556311] using wordTrace_append hprefix tailTrace_556311
  have hstable : (prefixWord ++ tailWord_556311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556311).length < 2 ^ (prefixWord ++ tailWord_556311).sum := by decide
  have hdescent : baseEnd_556311 < baseStart_556311 := by decide
  rcases family_descends (prefixWord ++ tailWord_556311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556339 : List Nat := [1, 1, 1, 2, 5, 3, 1, 7]
def baseStart_556339 : Nat := 118140960795 + 556339 * 2 ^ 59
def prefixEnd_556339 : Nat := 4983230072969 + 3 ^ 40 * 556339 * 2
def baseEnd_556339 : Nat := 42321379828415415526511

theorem tailTrace_556339 : CollatzResearch.WordTrace tailWord_556339 prefixEnd_556339 42321379828415415526511 := by
  unfold tailWord_556339
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291350331486292981768071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13527566887657528654512047 20291350331486292981768071)
  ·
    refine ⟨30437025497229439472652107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20291350331486292981768071 30437025497229439472652107)
    ·
      refine ⟨45655538245844159208978161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30437025497229439472652107 45655538245844159208978161)
      ·
        refine ⟨34241653684383119406733621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45655538245844159208978161 34241653684383119406733621)
        ·
          refine ⟨3210155032910917444381277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34241653684383119406733621 3210155032910917444381277)
          ·
            refine ⟨1203808137341594041642979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3210155032910917444381277 1203808137341594041642979)
            ·
              refine ⟨1805712206012391062464469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203808137341594041642979 1805712206012391062464469)
              ·
                refine ⟨42321379828415415526511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1805712206012391062464469 42321379828415415526511)
                ·
                  rfl

theorem cell21_556339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 7].length) (baseStart_556339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556339 prefixEnd_556339 := by exact prefixLift 556339
  have htrace : WordTrace (prefixWord ++ tailWord_556339) baseStart_556339 baseEnd_556339 := by
    simpa [prefixWord, tailWord_556339, baseEnd_556339] using wordTrace_append hprefix tailTrace_556339
  have hstable : (prefixWord ++ tailWord_556339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556339).length < 2 ^ (prefixWord ++ tailWord_556339).sum := by decide
  have hdescent : baseEnd_556339 < baseStart_556339 := by decide
  rcases family_descends (prefixWord ++ tailWord_556339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556345 : List Nat := [1, 2, 1, 6, 2, 2, 1, 3, 3]
def baseStart_556345 : Nat := 118140960795 + 556345 * 2 ^ 59
def prefixEnd_556345 : Nat := 4983230072969 + 3 ^ 40 * 556345 * 2
def baseEnd_556345 : Nat := 126965508766991569479521

theorem tailTrace_556345 : CollatzResearch.WordTrace tailWord_556345 prefixEnd_556345 126965508766991569479521 := by
  unfold tailWord_556345
  simp only [CollatzResearch.WordTrace]
  refine ⟨20291569169464556006486489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13527712779643037337657659 20291569169464556006486489)
  ·
    refine ⟨15218676877098417004864867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20291569169464556006486489 15218676877098417004864867)
    ·
      refine ⟨22828015315647625507297301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15218676877098417004864867 22828015315647625507297301)
      ·
        refine ⟨1070063217920982445654561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22828015315647625507297301 1070063217920982445654561)
        ·
          refine ⟨802547413440736834240921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070063217920982445654561 802547413440736834240921)
          ·
            refine ⟨601910560080552625680691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802547413440736834240921 601910560080552625680691)
            ·
              refine ⟨902865840120828938521037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601910560080552625680691 902865840120828938521037)
              ·
                refine ⟨338574690045310851945389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902865840120828938521037 338574690045310851945389)
                ·
                  refine ⟨126965508766991569479521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338574690045310851945389 126965508766991569479521)
                  ·
                    rfl

theorem cell21_556345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_556345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556345 prefixEnd_556345 := by exact prefixLift 556345
  have htrace : WordTrace (prefixWord ++ tailWord_556345) baseStart_556345 baseEnd_556345 := by
    simpa [prefixWord, tailWord_556345, baseEnd_556345] using wordTrace_append hprefix tailTrace_556345
  have hstable : (prefixWord ++ tailWord_556345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556345).length < 2 ^ (prefixWord ++ tailWord_556345).sum := by decide
  have hdescent : baseEnd_556345 < baseStart_556345 := by decide
  rcases family_descends (prefixWord ++ tailWord_556345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556356 : List Nat := [2, 3, 4, 1, 1, 1, 9]
def baseStart_556356 : Nat := 118140960795 + 556356 * 2 ^ 59
def prefixEnd_556356 : Nat := 4983230072969 + 3 ^ 40 * 556356 * 2
def baseEnd_556356 : Nat := 14107557679650888310685

theorem tailTrace_556356 : CollatzResearch.WordTrace tailWord_556356 prefixEnd_556356 14107557679650888310685 := by
  unfold tailWord_556356
  simp only [CollatzResearch.WordTrace]
  refine ⟨10145985186212352442568461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13527980248283136590091281 10145985186212352442568461)
  ·
    refine ⟨3804744444829632165963173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10145985186212352442568461 3804744444829632165963173)
    ·
      refine ⟨713389583405556031118095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3804744444829632165963173 713389583405556031118095)
      ·
        refine ⟨1070084375108334046677143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 713389583405556031118095 1070084375108334046677143)
        ·
          refine ⟨1605126562662501070015715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1070084375108334046677143 1605126562662501070015715)
          ·
            refine ⟨2407689843993751605023573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1605126562662501070015715 2407689843993751605023573)
            ·
              refine ⟨14107557679650888310685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2407689843993751605023573 14107557679650888310685)
              ·
                rfl

theorem cell21_556356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 9].length) (baseStart_556356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556356 prefixEnd_556356 := by exact prefixLift 556356
  have htrace : WordTrace (prefixWord ++ tailWord_556356) baseStart_556356 baseEnd_556356 := by
    simpa [prefixWord, tailWord_556356, baseEnd_556356] using wordTrace_append hprefix tailTrace_556356
  have hstable : (prefixWord ++ tailWord_556356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556356).length < 2 ^ (prefixWord ++ tailWord_556356).sum := by decide
  have hdescent : baseEnd_556356 < baseStart_556356 := by decide
  rcases family_descends (prefixWord ++ tailWord_556356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556525 : List Nat := [1, 5, 1, 3, 3, 1, 7]
def baseStart_556525 : Nat := 118140960795 + 556525 * 2 ^ 59
def prefixEnd_556525 : Nat := 4983230072969 + 3 ^ 40 * 556525 * 2
def baseEnd_556525 : Nat := 14111843024372361831017

theorem tailTrace_556525 : CollatzResearch.WordTrace tailWord_556525 prefixEnd_556525 14111843024372361831017 := by
  unfold tailWord_556525
  simp only [CollatzResearch.WordTrace]
  refine ⟨20298134308812446748039029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13532089539208297832026019 20298134308812446748039029)
  ·
    refine ⟨1902950091451166882628659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20298134308812446748039029 1902950091451166882628659)
    ·
      refine ⟨2854425137176750323942989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902950091451166882628659 2854425137176750323942989)
      ·
        refine ⟨1070409426441281371478621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2854425137176750323942989 1070409426441281371478621)
        ·
          refine ⟨401403534915480514304483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1070409426441281371478621 401403534915480514304483)
          ·
            refine ⟨602105302373220771456725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 401403534915480514304483 602105302373220771456725)
            ·
              refine ⟨14111843024372361831017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 602105302373220771456725 14111843024372361831017)
              ·
                rfl

theorem cell21_556525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 7].length) (baseStart_556525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556525 prefixEnd_556525 := by exact prefixLift 556525
  have htrace : WordTrace (prefixWord ++ tailWord_556525) baseStart_556525 baseEnd_556525 := by
    simpa [prefixWord, tailWord_556525, baseEnd_556525] using wordTrace_append hprefix tailTrace_556525
  have hstable : (prefixWord ++ tailWord_556525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556525).length < 2 ^ (prefixWord ++ tailWord_556525).sum := by decide
  have hdescent : baseEnd_556525 < baseStart_556525 := by decide
  rcases family_descends (prefixWord ++ tailWord_556525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556536 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 6]
def baseStart_556536 : Nat := 118140960795 + 556536 * 2 ^ 59
def prefixEnd_556536 : Nat := 4983230072969 + 3 ^ 40 * 556536 * 2
def baseEnd_556536 : Nat := 127009097569217681795797

theorem tailTrace_556536 : CollatzResearch.WordTrace tailWord_556536 prefixEnd_556536 127009097569217681795797 := by
  unfold tailWord_556536
  simp only [CollatzResearch.WordTrace]
  refine ⟨10149267755886297813344731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13532357007848397084459641 10149267755886297813344731)
  ·
    refine ⟨15223901633829446720017097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10149267755886297813344731 15223901633829446720017097)
    ·
      refine ⟨11417926225372085040012823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15223901633829446720017097 11417926225372085040012823)
      ·
        refine ⟨17126889338058127560019235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11417926225372085040012823 17126889338058127560019235)
        ·
          refine ⟨25690334007087191340028853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17126889338058127560019235 25690334007087191340028853)
          ·
            refine ⟨2408468813164424188127705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25690334007087191340028853 2408468813164424188127705)
            ·
              refine ⟨1806351609873318141095779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2408468813164424188127705 1806351609873318141095779)
              ·
                refine ⟨2709527414809977211643669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1806351609873318141095779 2709527414809977211643669)
                ·
                  refine ⟨127009097569217681795797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2709527414809977211643669 127009097569217681795797)
                  ·
                    rfl

theorem cell21_556536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_556536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556536 prefixEnd_556536 := by exact prefixLift 556536
  have htrace : WordTrace (prefixWord ++ tailWord_556536) baseStart_556536 baseEnd_556536 := by
    simpa [prefixWord, tailWord_556536, baseEnd_556536] using wordTrace_append hprefix tailTrace_556536
  have hstable : (prefixWord ++ tailWord_556536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556536).length < 2 ^ (prefixWord ++ tailWord_556536).sum := by decide
  have hdescent : baseEnd_556536 < baseStart_556536 := by decide
  rcases family_descends (prefixWord ++ tailWord_556536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556584 : List Nat := [2, 1, 5, 2, 3, 8]
def baseStart_556584 : Nat := 118140960795 + 556584 * 2 ^ 59
def prefixEnd_556584 : Nat := 4983230072969 + 3 ^ 40 * 556584 * 2
def baseEnd_556584 : Nat := 4704446363821491296137

theorem tailTrace_556584 : CollatzResearch.WordTrace tailWord_556584 prefixEnd_556584 4704446363821491296137 := by
  unfold tailWord_556584
  simp only [CollatzResearch.WordTrace]
  refine ⟨10150143107799349912218403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13533524143732466549624537 10150143107799349912218403)
  ·
    refine ⟨15225214661699024868327605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10150143107799349912218403 15225214661699024868327605)
    ·
      refine ⟨1427363874534283581405713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15225214661699024868327605 1427363874534283581405713)
      ·
        refine ⟨1070522905900712686054285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1427363874534283581405713 1070522905900712686054285)
        ·
          refine ⟨401446089712767257270357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1070522905900712686054285 401446089712767257270357)
          ·
            refine ⟨4704446363821491296137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 401446089712767257270357 4704446363821491296137)
            ·
              rfl

theorem cell21_556584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 8].length) (baseStart_556584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556584 prefixEnd_556584 := by exact prefixLift 556584
  have htrace : WordTrace (prefixWord ++ tailWord_556584) baseStart_556584 baseEnd_556584 := by
    simpa [prefixWord, tailWord_556584, baseEnd_556584] using wordTrace_append hprefix tailTrace_556584
  have hstable : (prefixWord ++ tailWord_556584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556584).length < 2 ^ (prefixWord ++ tailWord_556584).sum := by decide
  have hdescent : baseEnd_556584 < baseStart_556584 := by decide
  rcases family_descends (prefixWord ++ tailWord_556584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556708 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_556708 : Nat := 118140960795 + 556708 * 2 ^ 59
def prefixEnd_556708 : Nat := 4983230072969 + 3 ^ 40 * 556708 * 2
def baseEnd_556708 : Nat := 127048350312583604928779

theorem tailTrace_556708 : CollatzResearch.WordTrace tailWord_556708 prefixEnd_556708 127048350312583604928779 := by
  unfold tailWord_556708
  simp only [CollatzResearch.WordTrace]
  refine ⟨10152404433574734500975389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 13536539244766312667967185 10152404433574734500975389)
  ·
    refine ⟨3807151662590525437865771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10152404433574734500975389 3807151662590525437865771)
    ·
      refine ⟨5710727493885788156798657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807151662590525437865771 5710727493885788156798657)
      ·
        refine ⟨4283045620414341117598993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5710727493885788156798657 4283045620414341117598993)
        ·
          refine ⟨3212284215310755838199245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4283045620414341117598993 3212284215310755838199245)
          ·
            refine ⟨1204606580741533439324717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3212284215310755838199245 1204606580741533439324717)
            ·
              refine ⟨451727467778075039746769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1204606580741533439324717 451727467778075039746769)
              ·
                refine ⟨338795600833556279810077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 451727467778075039746769 338795600833556279810077)
                ·
                  refine ⟨127048350312583604928779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338795600833556279810077 127048350312583604928779)
                  ·
                    rfl

theorem cell21_556708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_556708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556708 prefixEnd_556708 := by exact prefixLift 556708
  have htrace : WordTrace (prefixWord ++ tailWord_556708) baseStart_556708 baseEnd_556708 := by
    simpa [prefixWord, tailWord_556708, baseEnd_556708] using wordTrace_append hprefix tailTrace_556708
  have hstable : (prefixWord ++ tailWord_556708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556708).length < 2 ^ (prefixWord ++ tailWord_556708).sum := by decide
  have hdescent : baseEnd_556708 < baseStart_556708 := by decide
  rcases family_descends (prefixWord ++ tailWord_556708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556733 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 7]
def baseStart_556733 : Nat := 118140960795 + 556733 * 2 ^ 59
def prefixEnd_556733 : Nat := 4983230072969 + 3 ^ 40 * 556733 * 2
def baseEnd_556733 : Nat := 127054055653189117012061

theorem tailTrace_556733 : CollatzResearch.WordTrace tailWord_556733 prefixEnd_556733 127054055653189117012061 := by
  unfold tailWord_556733
  simp only [CollatzResearch.WordTrace]
  refine ⟨20305720692058898271610853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13537147128039265514407235 20305720692058898271610853)
  ·
    refine ⟨3807322629761043425927035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20305720692058898271610853 3807322629761043425927035)
    ·
      refine ⟨5710983944641565138890553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807322629761043425927035 5710983944641565138890553)
      ·
        refine ⟨4283237958481173854167915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5710983944641565138890553 4283237958481173854167915)
        ·
          refine ⟨6424856937721760781251873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4283237958481173854167915 6424856937721760781251873)
          ·
            refine ⟨4818642703291320585938905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6424856937721760781251873 4818642703291320585938905)
            ·
              refine ⟨3613982027468490439454179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4818642703291320585938905 3613982027468490439454179)
              ·
                refine ⟨5420973041202735659181269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3613982027468490439454179 5420973041202735659181269)
                ·
                  refine ⟨127054055653189117012061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5420973041202735659181269 127054055653189117012061)
                  ·
                    rfl

theorem cell21_556733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_556733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556733 prefixEnd_556733 := by exact prefixLift 556733
  have htrace : WordTrace (prefixWord ++ tailWord_556733) baseStart_556733 baseEnd_556733 := by
    simpa [prefixWord, tailWord_556733, baseEnd_556733] using wordTrace_append hprefix tailTrace_556733
  have hstable : (prefixWord ++ tailWord_556733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556733).length < 2 ^ (prefixWord ++ tailWord_556733).sum := by decide
  have hdescent : baseEnd_556733 < baseStart_556733 := by decide
  rcases family_descends (prefixWord ++ tailWord_556733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556747 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 8]
def baseStart_556747 : Nat := 118140960795 + 556747 * 2 ^ 59
def prefixEnd_556747 : Nat := 4983230072969 + 3 ^ 40 * 556747 * 2
def baseEnd_556747 : Nat := 127057250643928203778699

theorem tailTrace_556747 : CollatzResearch.WordTrace tailWord_556747 prefixEnd_556747 127057250643928203778699 := by
  unfold tailWord_556747
  simp only [CollatzResearch.WordTrace]
  refine ⟨20306231314008178662620495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13537487542672119108413663 20306231314008178662620495)
  ·
    refine ⟨30459346971012267993930743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20306231314008178662620495 30459346971012267993930743)
    ·
      refine ⟨45689020456518401990896115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30459346971012267993930743 45689020456518401990896115)
      ·
        refine ⟨68533530684777602986344173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45689020456518401990896115 68533530684777602986344173)
        ·
          refine ⟨25700074006791601119879065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68533530684777602986344173 25700074006791601119879065)
          ·
            refine ⟨19275055505093700839909299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25700074006791601119879065 19275055505093700839909299)
            ·
              refine ⟨28912583257640551259863949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19275055505093700839909299 28912583257640551259863949)
              ·
                refine ⟨10842218721615206722448981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28912583257640551259863949 10842218721615206722448981)
                ·
                  refine ⟨127057250643928203778699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10842218721615206722448981 127057250643928203778699)
                  ·
                    rfl

theorem cell21_556747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 8].length) (baseStart_556747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556747 prefixEnd_556747 := by exact prefixLift 556747
  have htrace : WordTrace (prefixWord ++ tailWord_556747) baseStart_556747 baseEnd_556747 := by
    simpa [prefixWord, tailWord_556747, baseEnd_556747] using wordTrace_append hprefix tailTrace_556747
  have hstable : (prefixWord ++ tailWord_556747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556747).length < 2 ^ (prefixWord ++ tailWord_556747).sum := by decide
  have hdescent : baseEnd_556747 < baseStart_556747 := by decide
  rcases family_descends (prefixWord ++ tailWord_556747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_556781 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_556781 : Nat := 118140960795 + 556781 * 2 ^ 59
def prefixEnd_556781 : Nat := 4983230072969 + 3 ^ 40 * 556781 * 2
def baseEnd_556781 : Nat := 127065009907151700211963

theorem tailTrace_556781 : CollatzResearch.WordTrace tailWord_556781 prefixEnd_556781 127065009907151700211963 := by
  unfold tailWord_556781
  simp only [CollatzResearch.WordTrace]
  refine ⟨20307471395885002469358197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 13538314263923334979572131 20307471395885002469358197)
  ·
    refine ⟨1903825443364218981502331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20307471395885002469358197 1903825443364218981502331)
    ·
      refine ⟨2855738165046328472253497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1903825443364218981502331 2855738165046328472253497)
      ·
        refine ⟨2141803623784746354190123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2855738165046328472253497 2141803623784746354190123)
        ·
          refine ⟨3212705435677119531285185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2141803623784746354190123 3212705435677119531285185)
          ·
            refine ⟨2409529076757839648463889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3212705435677119531285185 2409529076757839648463889)
            ·
              refine ⟨1807146807568379736347917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2409529076757839648463889 1807146807568379736347917)
              ·
                refine ⟨677680052838142401130469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1807146807568379736347917 677680052838142401130469)
                ·
                  refine ⟨127065009907151700211963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 677680052838142401130469 127065009907151700211963)
                  ·
                    rfl

theorem cell21_556781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_556781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_556781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_556781 prefixEnd_556781 := by exact prefixLift 556781
  have htrace : WordTrace (prefixWord ++ tailWord_556781) baseStart_556781 baseEnd_556781 := by
    simpa [prefixWord, tailWord_556781, baseEnd_556781] using wordTrace_append hprefix tailTrace_556781
  have hstable : (prefixWord ++ tailWord_556781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_556781).length < 2 ^ (prefixWord ++ tailWord_556781).sum := by decide
  have hdescent : baseEnd_556781 < baseStart_556781 := by decide
  rcases family_descends (prefixWord ++ tailWord_556781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
