import V185TrunkScan23Chunk0726

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4300546 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4300546 : Nat := 118140960795 + 4300546 * 2 ^ 59
def prefixEnd_4300546 : Nat := 4983230072969 + 3 ^ 40 * 4300546 * 2
def baseEnd_4300546 : Nat := 736082391590212109232385

theorem tailTrace_4300546 : CollatzResearch.WordTrace tailWord_4300546 prefixEnd_4300546 736082391590212109232385 := by
  unfold tailWord_4300546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39213449669465947906846373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104569199118575861084923661 39213449669465947906846373)
  ·
    refine ⟨7352521813024865232533695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39213449669465947906846373 7352521813024865232533695)
    ·
      refine ⟨11028782719537297848800543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7352521813024865232533695 11028782719537297848800543)
      ·
        refine ⟨16543174079305946773200815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11028782719537297848800543 16543174079305946773200815)
        ·
          refine ⟨24814761118958920159801223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16543174079305946773200815 24814761118958920159801223)
          ·
            refine ⟨37222141678438380239701835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24814761118958920159801223 37222141678438380239701835)
            ·
              refine ⟨55833212517657570359552753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37222141678438380239701835 55833212517657570359552753)
              ·
                refine ⟨41874909388243177769664565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55833212517657570359552753 41874909388243177769664565)
                ·
                  refine ⟨3925772755147797915906053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41874909388243177769664565 3925772755147797915906053)
                  ·
                    refine ⟨736082391590212109232385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925772755147797915906053 736082391590212109232385)
                    ·
                      rfl

theorem cell23_4300546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4300546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300546 prefixEnd_4300546 := by exact prefixLift 4300546
  have htrace : WordTrace (prefixWord ++ tailWord_4300546) baseStart_4300546 baseEnd_4300546 := by
    simpa [prefixWord, tailWord_4300546, baseEnd_4300546] using wordTrace_append hprefix tailTrace_4300546
  have hstable : (prefixWord ++ tailWord_4300546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300546).length < 2 ^ (prefixWord ++ tailWord_4300546).sum := by decide
  have hdescent : baseEnd_4300546 < baseStart_4300546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300576 : List Nat := [2, 1, 1, 5, 1, 1, 5, 1, 6]
def baseStart_4300576 : Nat := 118140960795 + 4300576 * 2 ^ 59
def prefixEnd_4300576 : Nat := 4983230072969 + 3 ^ 40 * 4300576 * 2
def baseEnd_4300576 : Nat := 245362508798919023369113

theorem tailTrace_4300576 : CollatzResearch.WordTrace tailWord_4300576 prefixEnd_4300576 245362508798919023369113 := by
  unfold tailWord_4300576
  simp only [CollatzResearch.WordTrace]
  refine ⟨78427446433877553375488791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104569928578503404500651721 78427446433877553375488791)
  ·
    refine ⟨117641169650816330063233187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78427446433877553375488791 117641169650816330063233187)
    ·
      refine ⟨176461754476224495094849781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117641169650816330063233187 176461754476224495094849781)
      ·
        refine ⟨16543289482146046415142167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176461754476224495094849781 16543289482146046415142167)
        ·
          refine ⟨24814934223219069622713251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16543289482146046415142167 24814934223219069622713251)
          ·
            refine ⟨37222401334828604434069877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24814934223219069622713251 37222401334828604434069877)
            ·
              refine ⟨3489600125140181665694051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37222401334828604434069877 3489600125140181665694051)
              ·
                refine ⟨5234400187710272498541077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489600125140181665694051 5234400187710272498541077)
                ·
                  refine ⟨245362508798919023369113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5234400187710272498541077 245362508798919023369113)
                  ·
                    rfl

theorem cell23_4300576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 6].length) (baseStart_4300576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300576 prefixEnd_4300576 := by exact prefixLift 4300576
  have htrace : WordTrace (prefixWord ++ tailWord_4300576) baseStart_4300576 baseEnd_4300576 := by
    simpa [prefixWord, tailWord_4300576, baseEnd_4300576] using wordTrace_append hprefix tailTrace_4300576
  have hstable : (prefixWord ++ tailWord_4300576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300576).length < 2 ^ (prefixWord ++ tailWord_4300576).sum := by decide
  have hdescent : baseEnd_4300576 < baseStart_4300576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300597 : List Nat := [1, 3, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_4300597 : Nat := 118140960795 + 4300597 * 2 ^ 59
def prefixEnd_4300597 : Nat := 4983230072969 + 3 ^ 40 * 4300597 * 2
def baseEnd_4300597 : Nat := 736091120761338542719807

theorem tailTrace_4300597 : CollatzResearch.WordTrace tailWord_4300597 prefixEnd_4300597 736091120761338542719807 := by
  unfold tailWord_4300597
  simp only [CollatzResearch.WordTrace]
  refine ⟨156855658800679027337492045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104570439200452684891661363 156855658800679027337492045)
  ·
    refine ⟨58820872050254635251559517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156855658800679027337492045 58820872050254635251559517)
    ·
      refine ⟨22057827018845488219334819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58820872050254635251559517 22057827018845488219334819)
      ·
        refine ⟨33086740528268232329002229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22057827018845488219334819 33086740528268232329002229)
        ·
          refine ⟨3101881924525146780843959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33086740528268232329002229 3101881924525146780843959)
          ·
            refine ⟨4652822886787720171265939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3101881924525146780843959 4652822886787720171265939)
            ·
              refine ⟨6979234330181580256898909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652822886787720171265939 6979234330181580256898909)
              ·
                refine ⟨2617212873818092596337091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6979234330181580256898909 2617212873818092596337091)
                ·
                  refine ⟨3925819310727138894505637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617212873818092596337091 3925819310727138894505637)
                  ·
                    refine ⟨736091120761338542719807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925819310727138894505637 736091120761338542719807)
                    ·
                      rfl

theorem cell23_4300597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_4300597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300597 prefixEnd_4300597 := by exact prefixLift 4300597
  have htrace : WordTrace (prefixWord ++ tailWord_4300597) baseStart_4300597 baseEnd_4300597 := by
    simpa [prefixWord, tailWord_4300597, baseEnd_4300597] using wordTrace_append hprefix tailTrace_4300597
  have hstable : (prefixWord ++ tailWord_4300597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300597).length < 2 ^ (prefixWord ++ tailWord_4300597).sum := by decide
  have hdescent : baseEnd_4300597 < baseStart_4300597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300614 : List Nat := [6, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_4300614 : Nat := 118140960795 + 4300614 * 2 ^ 59
def prefixEnd_4300614 : Nat := 4983230072969 + 3 ^ 40 * 4300614 * 2
def baseEnd_4300614 : Nat := 736094030485047353882281

theorem tailTrace_4300614 : CollatzResearch.WordTrace tailWord_4300614 prefixEnd_4300614 736094030485047353882281 := by
  unfold tailWord_4300614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4901758713800544976276903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104570852561078292827240597 4901758713800544976276903)
  ·
    refine ⟨7352638070700817464415355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4901758713800544976276903 7352638070700817464415355)
    ·
      refine ⟨11028957106051226196623033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7352638070700817464415355 11028957106051226196623033)
      ·
        refine ⟨8271717829538419647467275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11028957106051226196623033 8271717829538419647467275)
        ·
          refine ⟨12407576744307629471200913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8271717829538419647467275 12407576744307629471200913)
          ·
            refine ⟨9305682558230722103400685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12407576744307629471200913 9305682558230722103400685)
            ·
              refine ⟨3489630959336520788775257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9305682558230722103400685 3489630959336520788775257)
              ·
                refine ⟨2617223219502390591581443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3489630959336520788775257 2617223219502390591581443)
                ·
                  refine ⟨3925834829253585887372165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617223219502390591581443 3925834829253585887372165)
                  ·
                    refine ⟨736094030485047353882281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925834829253585887372165 736094030485047353882281)
                    ·
                      rfl

theorem cell23_4300614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_4300614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300614 prefixEnd_4300614 := by exact prefixLift 4300614
  have htrace : WordTrace (prefixWord ++ tailWord_4300614) baseStart_4300614 baseEnd_4300614 := by
    simpa [prefixWord, tailWord_4300614, baseEnd_4300614] using wordTrace_append hprefix tailTrace_4300614
  have hstable : (prefixWord ++ tailWord_4300614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300614).length < 2 ^ (prefixWord ++ tailWord_4300614).sum := by decide
  have hdescent : baseEnd_4300614 < baseStart_4300614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300620 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4300620 : Nat := 118140960795 + 4300620 * 2 ^ 59
def prefixEnd_4300620 : Nat := 4983230072969 + 3 ^ 40 * 4300620 * 2
def baseEnd_4300620 : Nat := 2208285172339069038171815

theorem tailTrace_4300620 : CollatzResearch.WordTrace tailWord_4300620 prefixEnd_4300620 2208285172339069038171815 := by
  unfold tailWord_4300620
  simp only [CollatzResearch.WordTrace]
  refine ⟨78428248839797851132789657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104570998453063801510386209 78428248839797851132789657)
  ·
    refine ⟨58821186629848388349592243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78428248839797851132789657 58821186629848388349592243)
    ·
      refine ⟨88231779944772582524388365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58821186629848388349592243 88231779944772582524388365)
      ·
        refine ⟨33086917479289718446645637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88231779944772582524388365 33086917479289718446645637)
        ·
          refine ⟨6203797027366822208746057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33086917479289718446645637 6203797027366822208746057)
          ·
            refine ⟨4652847770525116656559543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6203797027366822208746057 4652847770525116656559543)
            ·
              refine ⟨6979271655787674984839315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4652847770525116656559543 6979271655787674984839315)
              ·
                refine ⟨10468907483681512477258973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6979271655787674984839315 10468907483681512477258973)
                ·
                  refine ⟨3925840306380567178972115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10468907483681512477258973 3925840306380567178972115)
                  ·
                    refine ⟨5888760459570850768458173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3925840306380567178972115 5888760459570850768458173)
                    ·
                      refine ⟨2208285172339069038171815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888760459570850768458173 2208285172339069038171815)
                      ·
                        rfl

theorem cell23_4300620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4300620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300620 prefixEnd_4300620 := by exact prefixLift 4300620
  have htrace : WordTrace (prefixWord ++ tailWord_4300620) baseStart_4300620 baseEnd_4300620 := by
    simpa [prefixWord, tailWord_4300620, baseEnd_4300620] using wordTrace_append hprefix tailTrace_4300620
  have hstable : (prefixWord ++ tailWord_4300620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300620).length < 2 ^ (prefixWord ++ tailWord_4300620).sum := by decide
  have hdescent : baseEnd_4300620 < baseStart_4300620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300639 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6]
def baseStart_4300639 : Nat := 118140960795 + 4300639 * 2 ^ 59
def prefixEnd_4300639 : Nat := 4983230072969 + 3 ^ 40 * 4300639 * 2
def baseEnd_4300639 : Nat := 2208294928471504463834227

theorem tailTrace_4300639 : CollatzResearch.WordTrace tailWord_4300639 prefixEnd_4300639 2208294928471504463834227 := by
  unfold tailWord_4300639
  simp only [CollatzResearch.WordTrace]
  refine ⟨156857190666526868510520971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104571460444351245673680647 156857190666526868510520971)
  ·
    refine ⟨235285785999790302765781457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156857190666526868510520971 235285785999790302765781457)
    ·
      refine ⟨176464339499842727074336093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235285785999790302765781457 176464339499842727074336093)
      ·
        refine ⟨66174127312441022652876035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176464339499842727074336093 66174127312441022652876035)
        ·
          refine ⟨99261190968661533979314053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66174127312441022652876035 99261190968661533979314053)
          ·
            refine ⟨18611473306624037621121385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99261190968661533979314053 18611473306624037621121385)
            ·
              refine ⟨13958604979968028215841039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18611473306624037621121385 13958604979968028215841039)
              ·
                refine ⟨20937907469952042323761559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13958604979968028215841039 20937907469952042323761559)
                ·
                  refine ⟨31406861204928063485642339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20937907469952042323761559 31406861204928063485642339)
                  ·
                    refine ⟨47110291807392095228463509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31406861204928063485642339 47110291807392095228463509)
                    ·
                      refine ⟨2208294928471504463834227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47110291807392095228463509 2208294928471504463834227)
                      ·
                        rfl

theorem cell23_4300639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_4300639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300639 prefixEnd_4300639 := by exact prefixLift 4300639
  have htrace : WordTrace (prefixWord ++ tailWord_4300639) baseStart_4300639 baseEnd_4300639 := by
    simpa [prefixWord, tailWord_4300639, baseEnd_4300639] using wordTrace_append hprefix tailTrace_4300639
  have hstable : (prefixWord ++ tailWord_4300639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300639).length < 2 ^ (prefixWord ++ tailWord_4300639).sum := by decide
  have hdescent : baseEnd_4300639 < baseStart_4300639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300670 : List Nat := [4, 2, 3, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4300670 : Nat := 118140960795 + 4300670 * 2 ^ 59
def prefixEnd_4300670 : Nat := 4983230072969 + 3 ^ 40 * 4300670 * 2
def baseEnd_4300670 : Nat := 736103615457264614182195

theorem tailTrace_4300670 : CollatzResearch.WordTrace tailWord_4300670 prefixEnd_4300670 736103615457264614182195 := by
  unfold tailWord_4300670
  simp only [CollatzResearch.WordTrace]
  refine ⟨19607290166176820100612433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104572214219609707203266309 19607290166176820100612433)
  ·
    refine ⟨14705467624632615075459325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19607290166176820100612433 14705467624632615075459325)
    ·
      refine ⟨5514550359237230653297247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14705467624632615075459325 5514550359237230653297247)
      ·
        refine ⟨8271825538855845979945871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514550359237230653297247 8271825538855845979945871)
        ·
          refine ⟨12407738308283768969918807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8271825538855845979945871 12407738308283768969918807)
          ·
            refine ⟨18611607462425653454878211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12407738308283768969918807 18611607462425653454878211)
            ·
              refine ⟨27917411193638480182317317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18611607462425653454878211 27917411193638480182317317)
              ·
                refine ⟨5234514598807215034184497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27917411193638480182317317 5234514598807215034184497)
                ·
                  refine ⟨3925885949105411275638373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5234514598807215034184497 3925885949105411275638373)
                  ·
                    refine ⟨736103615457264614182195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3925885949105411275638373 736103615457264614182195)
                    ·
                      rfl

theorem cell23_4300670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4300670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300670 prefixEnd_4300670 := by exact prefixLift 4300670
  have htrace : WordTrace (prefixWord ++ tailWord_4300670) baseStart_4300670 baseEnd_4300670 := by
    simpa [prefixWord, tailWord_4300670, baseEnd_4300670] using wordTrace_append hprefix tailTrace_4300670
  have hstable : (prefixWord ++ tailWord_4300670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300670).length < 2 ^ (prefixWord ++ tailWord_4300670).sum := by decide
  have hdescent : baseEnd_4300670 < baseStart_4300670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300693 : List Nat := [1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_4300693 : Nat := 118140960795 + 4300693 * 2 ^ 59
def prefixEnd_4300693 : Nat := 4983230072969 + 3 ^ 40 * 4300693 * 2
def baseEnd_4300693 : Nat := 2208322656426847252558979

theorem tailTrace_4300693 : CollatzResearch.WordTrace tailWord_4300693 prefixEnd_4300693 2208322656426847252558979 := by
  unfold tailWord_4300693
  simp only [CollatzResearch.WordTrace]
  refine ⟨156859160208331235732986733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104572773472220823821991155 156859160208331235732986733)
  ·
    refine ⟨58822185078124213399870025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156859160208331235732986733 58822185078124213399870025)
    ·
      refine ⟨44116638808593160049902519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58822185078124213399870025 44116638808593160049902519)
      ·
        refine ⟨66174958212889740074853779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44116638808593160049902519 66174958212889740074853779)
        ·
          refine ⟨99262437319334610112280669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66174958212889740074853779 99262437319334610112280669)
          ·
            refine ⟨37223413994750478792105251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99262437319334610112280669 37223413994750478792105251)
            ·
              refine ⟨55835120992125718188157877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37223413994750478792105251 55835120992125718188157877)
              ·
                refine ⟨5234542593011786080139801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55835120992125718188157877 5234542593011786080139801)
                ·
                  refine ⟨3925906944758839560104851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5234542593011786080139801 3925906944758839560104851)
                  ·
                    refine ⟨5888860417138259340157277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3925906944758839560104851 5888860417138259340157277)
                    ·
                      refine ⟨2208322656426847252558979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5888860417138259340157277 2208322656426847252558979)
                      ·
                        rfl

theorem cell23_4300693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_4300693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300693 prefixEnd_4300693 := by exact prefixLift 4300693
  have htrace : WordTrace (prefixWord ++ tailWord_4300693) baseStart_4300693 baseEnd_4300693 := by
    simpa [prefixWord, tailWord_4300693, baseEnd_4300693] using wordTrace_append hprefix tailTrace_4300693
  have hstable : (prefixWord ++ tailWord_4300693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300693).length < 2 ^ (prefixWord ++ tailWord_4300693).sum := by decide
  have hdescent : baseEnd_4300693 < baseStart_4300693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300719 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5]
def baseStart_4300719 : Nat := 118140960795 + 4300719 * 2 ^ 59
def prefixEnd_4300719 : Nat := 4983230072969 + 3 ^ 40 * 4300719 * 2
def baseEnd_4300719 : Nat := 2208336006923864150833859

theorem tailTrace_4300719 : CollatzResearch.WordTrace tailWord_4300719 prefixEnd_4300719 2208336006923864150833859 := by
  unfold tailWord_4300719
  simp only [CollatzResearch.WordTrace]
  refine ⟨156860108506237042173433211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104573405670824694782288807 156860108506237042173433211)
  ·
    refine ⟨235290162759355563260149817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156860108506237042173433211 235290162759355563260149817)
    ·
      refine ⟨176467622069516672445112363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235290162759355563260149817 176467622069516672445112363)
      ·
        refine ⟨264701433104275008667668545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176467622069516672445112363 264701433104275008667668545)
        ·
          refine ⟨198526074828206256500751409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264701433104275008667668545 198526074828206256500751409)
          ·
            refine ⟨148894556121154692375563557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198526074828206256500751409 148894556121154692375563557)
            ·
              refine ⟨27917729272716504820418167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 148894556121154692375563557 27917729272716504820418167)
              ·
                refine ⟨41876593909074757230627251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27917729272716504820418167 41876593909074757230627251)
                ·
                  refine ⟨62814890863612135845940877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41876593909074757230627251 62814890863612135845940877)
                  ·
                    refine ⟨23555584073854550942227829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 62814890863612135845940877 23555584073854550942227829)
                    ·
                      refine ⟨2208336006923864150833859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23555584073854550942227829 2208336006923864150833859)
                      ·
                        rfl

theorem cell23_4300719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 5].length) (baseStart_4300719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300719 prefixEnd_4300719 := by exact prefixLift 4300719
  have htrace : WordTrace (prefixWord ++ tailWord_4300719) baseStart_4300719 baseEnd_4300719 := by
    simpa [prefixWord, tailWord_4300719, baseEnd_4300719] using wordTrace_append hprefix tailTrace_4300719
  have hstable : (prefixWord ++ tailWord_4300719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300719).length < 2 ^ (prefixWord ++ tailWord_4300719).sum := by decide
  have hdescent : baseEnd_4300719 < baseStart_4300719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300746 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_4300746 : Nat := 118140960795 + 4300746 * 2 ^ 59
def prefixEnd_4300746 : Nat := 4983230072969 + 3 ^ 40 * 4300746 * 2
def baseEnd_4300746 : Nat := 2208349870901535545196235

theorem tailTrace_4300746 : CollatzResearch.WordTrace tailWord_4300746 prefixEnd_4300746 2208349870901535545196235 := by
  unfold tailWord_4300746
  simp only [CollatzResearch.WordTrace]
  refine ⟨39215273319284806446166523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104574062184759483856444061 39215273319284806446166523)
  ·
    refine ⟨58822909978927209669249785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39215273319284806446166523 58822909978927209669249785)
    ·
      refine ⟨44117182484195407251937339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58822909978927209669249785 44117182484195407251937339)
      ·
        refine ⟨66175773726293110877906009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44117182484195407251937339 66175773726293110877906009)
        ·
          refine ⟨49631830294719833158429507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66175773726293110877906009 49631830294719833158429507)
          ·
            refine ⟨74447745442079749737644261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49631830294719833158429507 74447745442079749737644261)
            ·
              refine ⟨13958952270389953075808299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74447745442079749737644261 13958952270389953075808299)
              ·
                refine ⟨20938428405584929613712449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13958952270389953075808299 20938428405584929613712449)
                ·
                  refine ⟨15703821304188697210284337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20938428405584929613712449 15703821304188697210284337)
                  ·
                    refine ⟨11777865978141522907713253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15703821304188697210284337 11777865978141522907713253)
                    ·
                      refine ⟨2208349870901535545196235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11777865978141522907713253 2208349870901535545196235)
                      ·
                        rfl

theorem cell23_4300746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_4300746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300746 prefixEnd_4300746 := by exact prefixLift 4300746
  have htrace : WordTrace (prefixWord ++ tailWord_4300746) baseStart_4300746 baseEnd_4300746 := by
    simpa [prefixWord, tailWord_4300746, baseEnd_4300746] using wordTrace_append hprefix tailTrace_4300746
  have hstable : (prefixWord ++ tailWord_4300746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300746).length < 2 ^ (prefixWord ++ tailWord_4300746).sum := by decide
  have hdescent : baseEnd_4300746 < baseStart_4300746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300756 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 7]
def baseStart_4300756 : Nat := 118140960795 + 4300756 * 2 ^ 59
def prefixEnd_4300756 : Nat := 4983230072969 + 3 ^ 40 * 4300756 * 2
def baseEnd_4300756 : Nat := 245372778412008945119021

theorem tailTrace_4300756 : CollatzResearch.WordTrace tailWord_4300756 prefixEnd_4300756 245372778412008945119021 := by
  unfold tailWord_4300756
  simp only [CollatzResearch.WordTrace]
  refine ⟨78430729003551498746265061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104574305338068664995020081 78430729003551498746265061)
  ·
    refine ⟨14705761688165906014924699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78430729003551498746265061 14705761688165906014924699)
    ·
      refine ⟨22058642532248859022387049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14705761688165906014924699 22058642532248859022387049)
      ·
        refine ⟨16543981899186644266790287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22058642532248859022387049 16543981899186644266790287)
        ·
          refine ⟨24815972848779966400185431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16543981899186644266790287 24815972848779966400185431)
          ·
            refine ⟨37223959273169949600278147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24815972848779966400185431 37223959273169949600278147)
            ·
              refine ⟨55835938909754924400417221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37223959273169949600278147 55835938909754924400417221)
              ·
                refine ⟨10469238545579048325078229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55835938909754924400417221 10469238545579048325078229)
                ·
                  refine ⟨245372778412008945119021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10469238545579048325078229 245372778412008945119021)
                  ·
                    rfl

theorem cell23_4300756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_4300756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300756 prefixEnd_4300756 := by exact prefixLift 4300756
  have htrace : WordTrace (prefixWord ++ tailWord_4300756) baseStart_4300756 baseEnd_4300756 := by
    simpa [prefixWord, tailWord_4300756, baseEnd_4300756] using wordTrace_append hprefix tailTrace_4300756
  have hstable : (prefixWord ++ tailWord_4300756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300756).length < 2 ^ (prefixWord ++ tailWord_4300756).sum := by decide
  have hdescent : baseEnd_4300756 < baseStart_4300756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300770 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4300770 : Nat := 118140960795 + 4300770 * 2 ^ 59
def prefixEnd_4300770 : Nat := 4983230072969 + 3 ^ 40 * 4300770 * 2
def baseEnd_4300770 : Nat := 2208362194437243451296125

theorem tailTrace_4300770 : CollatzResearch.WordTrace tailWord_4300770 prefixEnd_4300770 2208362194437243451296125 := by
  unfold tailWord_4300770
  simp only [CollatzResearch.WordTrace]
  refine ⟨39215492157263069470884941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104574645752701518589026509 39215492157263069470884941)
  ·
    refine ⟨14705809558973651051581853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39215492157263069470884941 14705809558973651051581853)
    ·
      refine ⟨5514678584615119144343195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14705809558973651051581853 5514678584615119144343195)
      ·
        refine ⟨8272017876922678716514793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514678584615119144343195 8272017876922678716514793)
        ·
          refine ⟨6204013407692009037386095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8272017876922678716514793 6204013407692009037386095)
          ·
            refine ⟨9306020111538013556079143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204013407692009037386095 9306020111538013556079143)
            ·
              refine ⟨13959030167307020334118715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9306020111538013556079143 13959030167307020334118715)
              ·
                refine ⟨20938545250960530501178073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13959030167307020334118715 20938545250960530501178073)
                ·
                  refine ⟨15703908938220397875883555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20938545250960530501178073 15703908938220397875883555)
                  ·
                    refine ⟨23555863407330596813825333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15703908938220397875883555 23555863407330596813825333)
                    ·
                      refine ⟨2208362194437243451296125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23555863407330596813825333 2208362194437243451296125)
                      ·
                        rfl

theorem cell23_4300770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4300770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300770 prefixEnd_4300770 := by exact prefixLift 4300770
  have htrace : WordTrace (prefixWord ++ tailWord_4300770) baseStart_4300770 baseEnd_4300770 := by
    simpa [prefixWord, tailWord_4300770, baseEnd_4300770] using wordTrace_append hprefix tailTrace_4300770
  have hstable : (prefixWord ++ tailWord_4300770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300770).length < 2 ^ (prefixWord ++ tailWord_4300770).sum := by decide
  have hdescent : baseEnd_4300770 < baseStart_4300770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300779 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_4300779 : Nat := 118140960795 + 4300779 * 2 ^ 59
def prefixEnd_4300779 : Nat := 4983230072969 + 3 ^ 40 * 4300779 * 2
def baseEnd_4300779 : Nat := 2208366815763133916083583

theorem tailTrace_4300779 : CollatzResearch.WordTrace tailWord_4300779 prefixEnd_4300779 2208366815763133916083583 := by
  unfold tailWord_4300779
  simp only [CollatzResearch.WordTrace]
  refine ⟨156862296886019672420617391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104574864590679781613744927 156862296886019672420617391)
  ·
    refine ⟨235293445329029508630926087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156862296886019672420617391 235293445329029508630926087)
    ·
      refine ⟨352940167993544262946389131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235293445329029508630926087 352940167993544262946389131)
      ·
        refine ⟨529410251990316394419583697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352940167993544262946389131 529410251990316394419583697)
        ·
          refine ⟨397057688992737295814687773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529410251990316394419583697 397057688992737295814687773)
          ·
            refine ⟨148896633372276485930507915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397057688992737295814687773 148896633372276485930507915)
            ·
              refine ⟨223344950058414728895761873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148896633372276485930507915 223344950058414728895761873)
              ·
                refine ⟨167508712543811046671821405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223344950058414728895761873 167508712543811046671821405)
                ·
                  refine ⟨62815767203929142501933027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167508712543811046671821405 62815767203929142501933027)
                  ·
                    refine ⟨94223650805893713752899541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62815767203929142501933027 94223650805893713752899541)
                    ·
                      refine ⟨2208366815763133916083583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94223650805893713752899541 2208366815763133916083583)
                      ·
                        rfl

theorem cell23_4300779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_4300779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300779 prefixEnd_4300779 := by exact prefixLift 4300779
  have htrace : WordTrace (prefixWord ++ tailWord_4300779) baseStart_4300779 baseEnd_4300779 := by
    simpa [prefixWord, tailWord_4300779, baseEnd_4300779] using wordTrace_append hprefix tailTrace_4300779
  have hstable : (prefixWord ++ tailWord_4300779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300779).length < 2 ^ (prefixWord ++ tailWord_4300779).sum := by decide
  have hdescent : baseEnd_4300779 < baseStart_4300779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300790 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_4300790 : Nat := 118140960795 + 4300790 * 2 ^ 59
def prefixEnd_4300790 : Nat := 4983230072969 + 3 ^ 40 * 4300790 * 2
def baseEnd_4300790 : Nat := 245374718227814819227337

theorem tailTrace_4300790 : CollatzResearch.WordTrace tailWord_4300790 prefixEnd_4300790 245374718227814819227337 := by
  unfold tailWord_4300790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9803918630561238831204239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104575132059319880866178549 9803918630561238831204239)
  ·
    refine ⟨14705877945841858246806359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9803918630561238831204239 14705877945841858246806359)
    ·
      refine ⟨22058816918762787370209539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14705877945841858246806359 22058816918762787370209539)
      ·
        refine ⟨33088225378144181055314309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22058816918762787370209539 33088225378144181055314309)
        ·
          refine ⟨6204042258402033947871433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33088225378144181055314309 6204042258402033947871433)
          ·
            refine ⟨4653031693801525460903575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6204042258402033947871433 4653031693801525460903575)
            ·
              refine ⟨6979547540702288191355363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653031693801525460903575 6979547540702288191355363)
              ·
                refine ⟨10469321311053432287033045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6979547540702288191355363 10469321311053432287033045)
                ·
                  refine ⟨245374718227814819227337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10469321311053432287033045 245374718227814819227337)
                  ·
                    rfl

theorem cell23_4300790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_4300790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300790 prefixEnd_4300790 := by exact prefixLift 4300790
  have htrace : WordTrace (prefixWord ++ tailWord_4300790) baseStart_4300790 baseEnd_4300790 := by
    simpa [prefixWord, tailWord_4300790, baseEnd_4300790] using wordTrace_append hprefix tailTrace_4300790
  have hstable : (prefixWord ++ tailWord_4300790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300790).length < 2 ^ (prefixWord ++ tailWord_4300790).sum := by decide
  have hdescent : baseEnd_4300790 < baseStart_4300790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300796 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_4300796 : Nat := 118140960795 + 4300796 * 2 ^ 59
def prefixEnd_4300796 : Nat := 4983230072969 + 3 ^ 40 * 4300796 * 2
def baseEnd_4300796 : Nat := 2208375544934260349571005

theorem tailTrace_4300796 : CollatzResearch.WordTrace tailWord_4300796 prefixEnd_4300796 2208375544934260349571005 := by
  unfold tailWord_4300796
  simp only [CollatzResearch.WordTrace]
  refine ⟨78431458463479042161993121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104575277951305389549324161 78431458463479042161993121)
  ·
    refine ⟨58823593847609281621494841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78431458463479042161993121 58823593847609281621494841)
    ·
      refine ⟨44117695385706961216121131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58823593847609281621494841 44117695385706961216121131)
      ·
        refine ⟨66176543078560441824181697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44117695385706961216121131 66176543078560441824181697)
        ·
          refine ⟨49632407308920331368136273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66176543078560441824181697 49632407308920331368136273)
          ·
            refine ⟨37224305481690248526102205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49632407308920331368136273 37224305481690248526102205)
            ·
              refine ⟨13959114555633843197288327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37224305481690248526102205 13959114555633843197288327)
              ·
                refine ⟨20938671833450764795932491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13959114555633843197288327 20938671833450764795932491)
                ·
                  refine ⟨31408007750176147193898737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20938671833450764795932491 31408007750176147193898737)
                  ·
                    refine ⟨23556005812632110395424053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31408007750176147193898737 23556005812632110395424053)
                    ·
                      refine ⟨2208375544934260349571005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23556005812632110395424053 2208375544934260349571005)
                      ·
                        rfl

theorem cell23_4300796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_4300796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300796 prefixEnd_4300796 := by exact prefixLift 4300796
  have htrace : WordTrace (prefixWord ++ tailWord_4300796) baseStart_4300796 baseEnd_4300796 := by
    simpa [prefixWord, tailWord_4300796, baseEnd_4300796] using wordTrace_append hprefix tailTrace_4300796
  have hstable : (prefixWord ++ tailWord_4300796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300796).length < 2 ^ (prefixWord ++ tailWord_4300796).sum := by decide
  have hdescent : baseEnd_4300796 < baseStart_4300796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300900 : List Nat := [2, 3, 1, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_4300900 : Nat := 118140960795 + 4300900 * 2 ^ 59
def prefixEnd_4300900 : Nat := 4983230072969 + 3 ^ 40 * 4300900 * 2
def baseEnd_4300900 : Nat := 2208428946922327942670527

theorem tailTrace_4300900 : CollatzResearch.WordTrace tailWord_4300900 prefixEnd_4300900 2208428946922327942670527 := by
  unfold tailWord_4300900
  simp only [CollatzResearch.WordTrace]
  refine ⟨78433355059290655042886077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104577806745720873390514769 78433355059290655042886077)
  ·
    refine ⟨29412508147233995641082279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78433355059290655042886077 29412508147233995641082279)
    ·
      refine ⟨44118762220850993461623419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29412508147233995641082279 44118762220850993461623419)
      ·
        refine ⟨66178143331276490192435129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44118762220850993461623419 66178143331276490192435129)
        ·
          refine ⟨49633607498457367644326347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66178143331276490192435129 49633607498457367644326347)
          ·
            refine ⟨74450411247686051466489521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49633607498457367644326347 74450411247686051466489521)
            ·
              refine ⟨55837808435764538599867141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74450411247686051466489521 55837808435764538599867141)
              ·
                refine ⟨10469589081705850987475089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55837808435764538599867141 10469589081705850987475089)
                ·
                  refine ⟨7852191811279388240606317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10469589081705850987475089 7852191811279388240606317)
                  ·
                    refine ⟨2944571929229770590227369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7852191811279388240606317 2944571929229770590227369)
                    ·
                      refine ⟨2208428946922327942670527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944571929229770590227369 2208428946922327942670527)
                      ·
                        rfl

theorem cell23_4300900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_4300900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300900 prefixEnd_4300900 := by exact prefixLift 4300900
  have htrace : WordTrace (prefixWord ++ tailWord_4300900) baseStart_4300900 baseEnd_4300900 := by
    simpa [prefixWord, tailWord_4300900, baseEnd_4300900] using wordTrace_append hprefix tailTrace_4300900
  have hstable : (prefixWord ++ tailWord_4300900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300900).length < 2 ^ (prefixWord ++ tailWord_4300900).sum := by decide
  have hdescent : baseEnd_4300900 < baseStart_4300900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300958 : List Nat := [4, 3, 1, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_4300958 : Nat := 118140960795 + 4300958 * 2 ^ 59
def prefixEnd_4300958 : Nat := 4983230072969 + 3 ^ 40 * 4300958 * 2
def baseEnd_4300958 : Nat := 2208458728800288715745261

theorem tailTrace_4300958 : CollatzResearch.WordTrace tailWord_4300958 prefixEnd_4300958 2208458728800288715745261 := by
  unfold tailWord_4300958
  simp only [CollatzResearch.WordTrace]
  refine ⟨19608603194046398248922941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104579217034914123994255685 19608603194046398248922941)
  ·
    refine ⟨7353226197767399343346103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19608603194046398248922941 7353226197767399343346103)
    ·
      refine ⟨11029839296651099015019155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353226197767399343346103 11029839296651099015019155)
      ·
        refine ⟨16544758944976648522528733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11029839296651099015019155 16544758944976648522528733)
        ·
          refine ⟨6204284604366243195948275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16544758944976648522528733 6204284604366243195948275)
          ·
            refine ⟨9306426906549364793922413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204284604366243195948275 9306426906549364793922413)
            ·
              refine ⟨3489910089956011797720905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9306426906549364793922413 3489910089956011797720905)
              ·
                refine ⟨2617432567467008848290679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3489910089956011797720905 2617432567467008848290679)
                ·
                  refine ⟨3926148851200513272436019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617432567467008848290679 3926148851200513272436019)
                  ·
                    refine ⟨5889223276800769908654029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3926148851200513272436019 5889223276800769908654029)
                    ·
                      refine ⟨2208458728800288715745261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5889223276800769908654029 2208458728800288715745261)
                      ·
                        rfl

theorem cell23_4300958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_4300958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300958 prefixEnd_4300958 := by exact prefixLift 4300958
  have htrace : WordTrace (prefixWord ++ tailWord_4300958) baseStart_4300958 baseEnd_4300958 := by
    simpa [prefixWord, tailWord_4300958, baseEnd_4300958] using wordTrace_append hprefix tailTrace_4300958
  have hstable : (prefixWord ++ tailWord_4300958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300958).length < 2 ^ (prefixWord ++ tailWord_4300958).sum := by decide
  have hdescent : baseEnd_4300958 < baseStart_4300958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300981 : List Nat := [1, 3, 3, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4300981 : Nat := 118140960795 + 4300981 * 2 ^ 59
def prefixEnd_4300981 : Nat := 4983230072969 + 3 ^ 40 * 4300981 * 2
def baseEnd_4300981 : Nat := 2208470538855342125757655

theorem tailTrace_4300981 : CollatzResearch.WordTrace tailWord_4300981 prefixEnd_4300981 2208470538855342125757655 := by
  unfold tailWord_4300981
  simp only [CollatzResearch.WordTrace]
  refine ⟨156869664431287860919470797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104579776287525240612980531 156869664431287860919470797)
  ·
    refine ⟨58826124161732947844801549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156869664431287860919470797 58826124161732947844801549)
    ·
      refine ⟨22059796560649855441800581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58826124161732947844801549 22059796560649855441800581)
      ·
        refine ⟨4136211855121847895337609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22059796560649855441800581 4136211855121847895337609)
        ·
          refine ⟨3102158891341385921503207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4136211855121847895337609 3102158891341385921503207)
          ·
            refine ⟨4653238337012078882254811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102158891341385921503207 4653238337012078882254811)
            ·
              refine ⟨6979857505518118323382217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4653238337012078882254811 6979857505518118323382217)
              ·
                refine ⟨5234893129138588742536663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6979857505518118323382217 5234893129138588742536663)
                ·
                  refine ⟨7852339693707883113804995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5234893129138588742536663 7852339693707883113804995)
                  ·
                    refine ⟨11778509540561824670707493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7852339693707883113804995 11778509540561824670707493)
                    ·
                      refine ⟨2208470538855342125757655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11778509540561824670707493 2208470538855342125757655)
                      ·
                        rfl

theorem cell23_4300981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4300981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300981 prefixEnd_4300981 := by exact prefixLift 4300981
  have htrace : WordTrace (prefixWord ++ tailWord_4300981) baseStart_4300981 baseEnd_4300981 := by
    simpa [prefixWord, tailWord_4300981, baseEnd_4300981] using wordTrace_append hprefix tailTrace_4300981
  have hstable : (prefixWord ++ tailWord_4300981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300981).length < 2 ^ (prefixWord ++ tailWord_4300981).sum := by decide
  have hdescent : baseEnd_4300981 < baseStart_4300981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4300994 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4300994 : Nat := 118140960795 + 4300994 * 2 ^ 59
def prefixEnd_4300994 : Nat := 4983230072969 + 3 ^ 40 * 4300994 * 2
def baseEnd_4300994 : Nat := 2208477214103850574895095

theorem tailTrace_4300994 : CollatzResearch.WordTrace tailWord_4300994 prefixEnd_4300994 2208477214103850574895095 := by
  unfold tailWord_4300994
  simp only [CollatzResearch.WordTrace]
  refine ⟨39217534645060191034923509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104580092386827176093129357 39217534645060191034923509)
  ·
    refine ⟨3676643872974392909524079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39217534645060191034923509 3676643872974392909524079)
    ·
      refine ⟨5514965809461589364286119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3676643872974392909524079 5514965809461589364286119)
      ·
        refine ⟨8272448714192384046429179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5514965809461589364286119 8272448714192384046429179)
        ·
          refine ⟨12408673071288576069643769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8272448714192384046429179 12408673071288576069643769)
          ·
            refine ⟨9306504803466432052232827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12408673071288576069643769 9306504803466432052232827)
            ·
              refine ⟨13959757205199648078349241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9306504803466432052232827 13959757205199648078349241)
              ·
                refine ⟨10469817903899736058761931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13959757205199648078349241 10469817903899736058761931)
                ·
                  refine ⟨15704726855849604088142897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10469817903899736058761931 15704726855849604088142897)
                  ·
                    refine ⟨11778545141887203066107173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15704726855849604088142897 11778545141887203066107173)
                    ·
                      refine ⟨2208477214103850574895095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11778545141887203066107173 2208477214103850574895095)
                      ·
                        rfl

theorem cell23_4300994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4300994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4300994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4300994 prefixEnd_4300994 := by exact prefixLift 4300994
  have htrace : WordTrace (prefixWord ++ tailWord_4300994) baseStart_4300994 baseEnd_4300994 := by
    simpa [prefixWord, tailWord_4300994, baseEnd_4300994] using wordTrace_append hprefix tailTrace_4300994
  have hstable : (prefixWord ++ tailWord_4300994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4300994).length < 2 ^ (prefixWord ++ tailWord_4300994).sum := by decide
  have hdescent : baseEnd_4300994 < baseStart_4300994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4300994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301033 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 4]
def baseStart_4301033 : Nat := 118140960795 + 4301033 * 2 ^ 59
def prefixEnd_4301033 : Nat := 4983230072969 + 3 ^ 40 * 4301033 * 2
def baseEnd_4301033 : Nat := 2208497239849375922307415

theorem tailTrace_4301033 : CollatzResearch.WordTrace tailWord_4301033 prefixEnd_4301033 2208497239849375922307415 := by
  unfold tailWord_4301033
  simp only [CollatzResearch.WordTrace]
  refine ⟨156871561027099473800363753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104581040684732982533575835 156871561027099473800363753)
  ·
    refine ⟨117653670770324605350272815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156871561027099473800363753 117653670770324605350272815)
    ·
      refine ⟨176480506155486908025409223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117653670770324605350272815 176480506155486908025409223)
      ·
        refine ⟨264720759233230362038113835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176480506155486908025409223 264720759233230362038113835)
        ·
          refine ⟨397081138849845543057170753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264720759233230362038113835 397081138849845543057170753)
          ·
            refine ⟨297810854137384157292878065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397081138849845543057170753 297810854137384157292878065)
            ·
              refine ⟨223358140603038117969658549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297810854137384157292878065 223358140603038117969658549)
              ·
                refine ⟨20939825681534823559655489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223358140603038117969658549 20939825681534823559655489)
                ·
                  refine ⟨15704869261151117669741617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20939825681534823559655489 15704869261151117669741617)
                  ·
                    refine ⟨11778651945863338252306213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15704869261151117669741617 11778651945863338252306213)
                    ·
                      refine ⟨2208497239849375922307415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11778651945863338252306213 2208497239849375922307415)
                      ·
                        rfl

theorem cell23_4301033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 2, 2, 4].length) (baseStart_4301033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301033 prefixEnd_4301033 := by exact prefixLift 4301033
  have htrace : WordTrace (prefixWord ++ tailWord_4301033) baseStart_4301033 baseEnd_4301033 := by
    simpa [prefixWord, tailWord_4301033, baseEnd_4301033] using wordTrace_append hprefix tailTrace_4301033
  have hstable : (prefixWord ++ tailWord_4301033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301033).length < 2 ^ (prefixWord ++ tailWord_4301033).sum := by decide
  have hdescent : baseEnd_4301033 < baseStart_4301033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301043 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 7]
def baseStart_4301043 : Nat := 118140960795 + 4301043 * 2 ^ 59
def prefixEnd_4301043 : Nat := 4983230072969 + 3 ^ 40 * 4301043 * 2
def baseEnd_4301043 : Nat := 245389152739546764798041

theorem tailTrace_4301043 : CollatzResearch.WordTrace tailWord_4301043 prefixEnd_4301043 245389152739546764798041 := by
  unfold tailWord_4301043
  simp only [CollatzResearch.WordTrace]
  refine ⟨156871925757063245508227783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104581283838042163672151855 156871925757063245508227783)
  ·
    refine ⟨235307888635594868262341675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156871925757063245508227783 235307888635594868262341675)
    ·
      refine ⟨352961832953392302393512513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235307888635594868262341675 352961832953392302393512513)
      ·
        refine ⟨264721374715044226795134385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352961832953392302393512513 264721374715044226795134385)
        ·
          refine ⟨198541031036283170096350789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264721374715044226795134385 198541031036283170096350789)
          ·
            refine ⟨37226443319303094393065773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198541031036283170096350789 37226443319303094393065773)
            ·
              refine ⟨13959916244738660397399665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37226443319303094393065773 13959916244738660397399665)
              ·
                refine ⟨10469937183553995298049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13959916244738660397399665 10469937183553995298049749)
                ·
                  refine ⟨245389152739546764798041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10469937183553995298049749 245389152739546764798041)
                  ·
                    rfl

theorem cell23_4301043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 7].length) (baseStart_4301043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301043 prefixEnd_4301043 := by exact prefixLift 4301043
  have htrace : WordTrace (prefixWord ++ tailWord_4301043) baseStart_4301043 baseEnd_4301043 := by
    simpa [prefixWord, tailWord_4301043, baseEnd_4301043] using wordTrace_append hprefix tailTrace_4301043
  have hstable : (prefixWord ++ tailWord_4301043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301043).length < 2 ^ (prefixWord ++ tailWord_4301043).sum := by decide
  have hdescent : baseEnd_4301043 < baseStart_4301043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301054 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_4301054 : Nat := 118140960795 + 4301054 * 2 ^ 59
def prefixEnd_4301054 : Nat := 4983230072969 + 3 ^ 40 * 4301054 * 2
def baseEnd_4301054 : Nat := 2208508022943120340144819

theorem tailTrace_4301054 : CollatzResearch.WordTrace tailWord_4301054 prefixEnd_4301054 2208508022943120340144819 := by
  unfold tailWord_4301054
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609040870002924298359777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104581551306682262924585477 19609040870002924298359777)
  ·
    refine ⟨14706780652502193223769833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19609040870002924298359777 14706780652502193223769833)
    ·
      refine ⟨11030085489376644917827375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14706780652502193223769833 11030085489376644917827375)
      ·
        refine ⟨16545128234064967376741063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11030085489376644917827375 16545128234064967376741063)
        ·
          refine ⟨24817692351097451065111595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16545128234064967376741063 24817692351097451065111595)
          ·
            refine ⟨37226538526646176597667393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24817692351097451065111595 37226538526646176597667393)
            ·
              refine ⟨27919903894984632448250545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37226538526646176597667393 27919903894984632448250545)
              ·
                refine ⟨20939927921238474336187909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27919903894984632448250545 20939927921238474336187909)
                ·
                  refine ⟨3926236485232213938035233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20939927921238474336187909 3926236485232213938035233)
                  ·
                    refine ⟨2944677363924160453526425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3926236485232213938035233 2944677363924160453526425)
                    ·
                      refine ⟨2208508022943120340144819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944677363924160453526425 2208508022943120340144819)
                      ·
                        rfl

theorem cell23_4301054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_4301054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301054 prefixEnd_4301054 := by exact prefixLift 4301054
  have htrace : WordTrace (prefixWord ++ tailWord_4301054) baseStart_4301054 baseEnd_4301054 := by
    simpa [prefixWord, tailWord_4301054, baseEnd_4301054] using wordTrace_append hprefix tailTrace_4301054
  have hstable : (prefixWord ++ tailWord_4301054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301054).length < 2 ^ (prefixWord ++ tailWord_4301054).sum := by decide
  have hdescent : baseEnd_4301054 < baseStart_4301054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301058 : List Nat := [3, 4, 1, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4301058 : Nat := 118140960795 + 4301058 * 2 ^ 59
def prefixEnd_4301058 : Nat := 4983230072969 + 3 ^ 40 * 4301058 * 2
def baseEnd_4301058 : Nat := 2208510076865738324494801

theorem tailTrace_4301058 : CollatzResearch.WordTrace tailWord_4301058 prefixEnd_4301058 2208510076865738324494801 := by
  unfold tailWord_4301058
  simp only [CollatzResearch.WordTrace]
  refine ⟨39218118213002225767505957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104581648568005935380015885 39218118213002225767505957)
  ·
    refine ⟨7353397164937917331407367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39218118213002225767505957 7353397164937917331407367)
    ·
      refine ⟨11030095747406875997111051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353397164937917331407367 11030095747406875997111051)
      ·
        refine ⟨16545143621110313995666577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11030095747406875997111051 16545143621110313995666577)
        ·
          refine ⟨12408857715832735496749933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16545143621110313995666577 12408857715832735496749933)
          ·
            refine ⟨4653321643437275811281225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12408857715832735496749933 4653321643437275811281225)
            ·
              refine ⟨3489991232577956858460919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4653321643437275811281225 3489991232577956858460919)
              ·
                refine ⟨5234986848866935287691379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3489991232577956858460919 5234986848866935287691379)
                ·
                  refine ⟨7852480273300402931537069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5234986848866935287691379 7852480273300402931537069)
                  ·
                    refine ⟨2944680102487651099326401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7852480273300402931537069 2944680102487651099326401)
                    ·
                      refine ⟨2208510076865738324494801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944680102487651099326401 2208510076865738324494801)
                      ·
                        rfl

theorem cell23_4301058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4301058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301058 prefixEnd_4301058 := by exact prefixLift 4301058
  have htrace : WordTrace (prefixWord ++ tailWord_4301058) baseStart_4301058 baseEnd_4301058 := by
    simpa [prefixWord, tailWord_4301058, baseEnd_4301058] using wordTrace_append hprefix tailTrace_4301058
  have hstable : (prefixWord ++ tailWord_4301058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301058).length < 2 ^ (prefixWord ++ tailWord_4301058).sum := by decide
  have hdescent : baseEnd_4301058 < baseStart_4301058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301070 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4301070 : Nat := 118140960795 + 4301070 * 2 ^ 59
def prefixEnd_4301070 : Nat := 4983230072969 + 3 ^ 40 * 4301070 * 2
def baseEnd_4301070 : Nat := 2208516238633592277544745

theorem tailTrace_4301070 : CollatzResearch.WordTrace tailWord_4301070 prefixEnd_4301070 2208516238633592277544745 := by
  unfold tailWord_4301070
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609113815995678639932583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104581940351976952746307109 19609113815995678639932583)
  ·
    refine ⟨29413670723993517959898875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19609113815995678639932583 29413670723993517959898875)
    ·
      refine ⟨44120506085990276939848313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29413670723993517959898875 44120506085990276939848313)
      ·
        refine ⟨33090379564492707704886235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44120506085990276939848313 33090379564492707704886235)
        ·
          refine ⟨49635569346739061557329353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33090379564492707704886235 49635569346739061557329353)
          ·
            refine ⟨37226677010054296167997015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49635569346739061557329353 37226677010054296167997015)
            ·
              refine ⟨55840015515081444251995523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37226677010054296167997015 55840015515081444251995523)
              ·
                refine ⟨83760023272622166377993285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55840015515081444251995523 83760023272622166377993285)
                ·
                  refine ⟨15705004363616656195873741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83760023272622166377993285 15705004363616656195873741)
                  ·
                    refine ⟨5889376636356246073452653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15705004363616656195873741 5889376636356246073452653)
                    ·
                      refine ⟨2208516238633592277544745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5889376636356246073452653 2208516238633592277544745)
                      ·
                        rfl

theorem cell23_4301070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4301070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301070 prefixEnd_4301070 := by exact prefixLift 4301070
  have htrace : WordTrace (prefixWord ++ tailWord_4301070) baseStart_4301070 baseEnd_4301070 := by
    simpa [prefixWord, tailWord_4301070, baseEnd_4301070] using wordTrace_append hprefix tailTrace_4301070
  have hstable : (prefixWord ++ tailWord_4301070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301070).length < 2 ^ (prefixWord ++ tailWord_4301070).sum := by decide
  have hdescent : baseEnd_4301070 < baseStart_4301070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301083 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5]
def baseStart_4301083 : Nat := 118140960795 + 4301083 * 2 ^ 59
def prefixEnd_4301083 : Nat := 4983230072969 + 3 ^ 40 * 4301083 * 2
def baseEnd_4301083 : Nat := 2208522913882100726682185

theorem tailTrace_4301083 : CollatzResearch.WordTrace tailWord_4301083 prefixEnd_4301083 2208522913882100726682185 := by
  unfold tailWord_4301083
  simp only [CollatzResearch.WordTrace]
  refine ⟨156873384676918332339683903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104582256451278888226455935 156873384676918332339683903)
  ·
    refine ⟨235310077015377498509525855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156873384676918332339683903 235310077015377498509525855)
    ·
      refine ⟨352965115523066247764288783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235310077015377498509525855 352965115523066247764288783)
      ·
        refine ⟨529447673284599371646433175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352965115523066247764288783 529447673284599371646433175)
        ·
          refine ⟨794171509926899057469649763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529447673284599371646433175 794171509926899057469649763)
          ·
            refine ⟨1191257264890348586204474645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794171509926899057469649763 1191257264890348586204474645)
            ·
              refine ⟨55840184291735089978334749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1191257264890348586204474645 55840184291735089978334749)
              ·
                refine ⟨20940069109400658741875531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55840184291735089978334749 20940069109400658741875531)
                ·
                  refine ⟨31410103664100988112813297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20940069109400658741875531 31410103664100988112813297)
                  ·
                    refine ⟨23557577748075741084609973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31410103664100988112813297 23557577748075741084609973)
                    ·
                      refine ⟨2208522913882100726682185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23557577748075741084609973 2208522913882100726682185)
                      ·
                        rfl

theorem cell23_4301083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 5].length) (baseStart_4301083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301083 prefixEnd_4301083 := by exact prefixLift 4301083
  have htrace : WordTrace (prefixWord ++ tailWord_4301083) baseStart_4301083 baseEnd_4301083 := by
    simpa [prefixWord, tailWord_4301083, baseEnd_4301083] using wordTrace_append hprefix tailTrace_4301083
  have hstable : (prefixWord ++ tailWord_4301083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301083).length < 2 ^ (prefixWord ++ tailWord_4301083).sum := by decide
  have hdescent : baseEnd_4301083 < baseStart_4301083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301090 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 1, 7]
def baseStart_4301090 : Nat := 118140960795 + 4301090 * 2 ^ 59
def prefixEnd_4301090 : Nat := 4983230072969 + 3 ^ 40 * 4301090 * 2
def baseEnd_4301090 : Nat := 736175502748894066431551

theorem tailTrace_4301090 : CollatzResearch.WordTrace tailWord_4301090 prefixEnd_4301090 736175502748894066431551 := by
  unfold tailWord_4301090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39218409996973243133797181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104582426658595315023459149 39218409996973243133797181)
  ·
    refine ⟨14706903748864966175173943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39218409996973243133797181 14706903748864966175173943)
    ·
      refine ⟨22060355623297449262760915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14706903748864966175173943 22060355623297449262760915)
      ·
        refine ⟨33090533434946173894141373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22060355623297449262760915 33090533434946173894141373)
        ·
          refine ⟨12408950038104815210303015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33090533434946173894141373 12408950038104815210303015)
          ·
            refine ⟨18613425057157222815454523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12408950038104815210303015 18613425057157222815454523)
            ·
              refine ⟨27920137585735834223181785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18613425057157222815454523 27920137585735834223181785)
              ·
                refine ⟨20940103189301875667386339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27920137585735834223181785 20940103189301875667386339)
                ·
                  refine ⟨31410154783952813501079509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20940103189301875667386339 31410154783952813501079509)
                  ·
                    refine ⟨736175502748894066431551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31410154783952813501079509 736175502748894066431551)
                    ·
                      rfl

theorem cell23_4301090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_4301090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301090 prefixEnd_4301090 := by exact prefixLift 4301090
  have htrace : WordTrace (prefixWord ++ tailWord_4301090) baseStart_4301090 baseEnd_4301090 := by
    simpa [prefixWord, tailWord_4301090, baseEnd_4301090] using wordTrace_append hprefix tailTrace_4301090
  have hstable : (prefixWord ++ tailWord_4301090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301090).length < 2 ^ (prefixWord ++ tailWord_4301090).sum := by decide
  have hdescent : baseEnd_4301090 < baseStart_4301090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301123 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6]
def baseStart_4301123 : Nat := 118140960795 + 4301123 * 2 ^ 59
def prefixEnd_4301123 : Nat := 4983230072969 + 3 ^ 40 * 4301123 * 2
def baseEnd_4301123 : Nat := 2208543453108280570182001

theorem tailTrace_4301123 : CollatzResearch.WordTrace tailWord_4301123 prefixEnd_4301123 2208543453108280570182001 := by
  unfold tailWord_4301123
  simp only [CollatzResearch.WordTrace]
  refine ⟨156874843596773419171140023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104583229064515612780760015 156874843596773419171140023)
  ·
    refine ⟨235312265395160128756710035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156874843596773419171140023 235312265395160128756710035)
    ·
      refine ⟨352968398092740193135065053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235312265395160128756710035 352968398092740193135065053)
      ·
        refine ⟨132363149284777572425649395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352968398092740193135065053 132363149284777572425649395)
        ·
          refine ⟨198544723927166358638474093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132363149284777572425649395 198544723927166358638474093)
          ·
            refine ⟨74454271472687384489427785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198544723927166358638474093 74454271472687384489427785)
            ·
              refine ⟨55840703604515538367070839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74454271472687384489427785 55840703604515538367070839)
              ·
                refine ⟨83761055406773307550606259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55840703604515538367070839 83761055406773307550606259)
                ·
                  refine ⟨125641583110159961325909389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83761055406773307550606259 125641583110159961325909389)
                  ·
                    refine ⟨47115593666309985497216021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125641583110159961325909389 47115593666309985497216021)
                    ·
                      refine ⟨2208543453108280570182001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47115593666309985497216021 2208543453108280570182001)
                      ·
                        rfl

theorem cell23_4301123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_4301123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301123 prefixEnd_4301123 := by exact prefixLift 4301123
  have htrace : WordTrace (prefixWord ++ tailWord_4301123) baseStart_4301123 baseEnd_4301123 := by
    simpa [prefixWord, tailWord_4301123, baseEnd_4301123] using wordTrace_append hprefix tailTrace_4301123
  have hstable : (prefixWord ++ tailWord_4301123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301123).length < 2 ^ (prefixWord ++ tailWord_4301123).sum := by decide
  have hdescent : baseEnd_4301123 < baseStart_4301123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301124 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4301124 : Nat := 118140960795 + 4301124 * 2 ^ 59
def prefixEnd_4301124 : Nat := 4983230072969 + 3 ^ 40 * 4301124 * 2
def baseEnd_4301124 : Nat := 736181322196311688756499

theorem tailTrace_4301124 : CollatzResearch.WordTrace tailWord_4301124 prefixEnd_4301124 736181322196311688756499 := by
  unfold tailWord_4301124
  simp only [CollatzResearch.WordTrace]
  refine ⟨78437440034884898170963213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104583253379846530894617617 78437440034884898170963213)
  ·
    refine ⟨29414040013081836814111205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78437440034884898170963213 29414040013081836814111205)
    ·
      refine ⟨5515132502452844402645851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29414040013081836814111205 5515132502452844402645851)
      ·
        refine ⟨8272698753679266603968777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515132502452844402645851 8272698753679266603968777)
        ·
          refine ⟨6204524065259449952976583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8272698753679266603968777 6204524065259449952976583)
          ·
            refine ⟨9306786097889174929464875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204524065259449952976583 9306786097889174929464875)
            ·
              refine ⟨13960179146833762394197313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9306786097889174929464875 13960179146833762394197313)
              ·
                refine ⟨10470134360125321795647985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13960179146833762394197313 10470134360125321795647985)
                ·
                  refine ⟨7852600770093991346735989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470134360125321795647985 7852600770093991346735989)
                  ·
                    refine ⟨736181322196311688756499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7852600770093991346735989 736181322196311688756499)
                    ·
                      rfl

theorem cell23_4301124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4301124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301124 prefixEnd_4301124 := by exact prefixLift 4301124
  have htrace : WordTrace (prefixWord ++ tailWord_4301124) baseStart_4301124 baseEnd_4301124 := by
    simpa [prefixWord, tailWord_4301124, baseEnd_4301124] using wordTrace_append hprefix tailTrace_4301124
  have hstable : (prefixWord ++ tailWord_4301124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301124).length < 2 ^ (prefixWord ++ tailWord_4301124).sum := by decide
  have hdescent : baseEnd_4301124 < baseStart_4301124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301137 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 3, 4]
def baseStart_4301137 : Nat := 118140960795 + 4301137 * 2 ^ 59
def prefixEnd_4301137 : Nat := 4983230072969 + 3 ^ 40 * 4301137 * 2
def baseEnd_4301137 : Nat := 736183547279147838468979

theorem tailTrace_4301137 : CollatzResearch.WordTrace tailWord_4301137 prefixEnd_4301137 736183547279147838468979 := by
  unfold tailWord_4301137
  simp only [CollatzResearch.WordTrace]
  refine ⟨156875354218722699562149665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104583569479148466374766443 156875354218722699562149665)
  ·
    refine ⟨117656515664042024671612249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156875354218722699562149665 117656515664042024671612249)
    ·
      refine ⟨88242386748031518503709187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117656515664042024671612249 88242386748031518503709187)
      ·
        refine ⟨132363580122047277755563781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88242386748031518503709187 132363580122047277755563781)
        ·
          refine ⟨24818171272883864579168209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132363580122047277755563781 24818171272883864579168209)
          ·
            refine ⟨18613628454662898434376157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24818171272883864579168209 18613628454662898434376157)
            ·
              refine ⟨6980110670498586912891059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18613628454662898434376157 6980110670498586912891059)
              ·
                refine ⟨10470166005747880369336589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980110670498586912891059 10470166005747880369336589)
                ·
                  refine ⟨3926312252155455138501221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10470166005747880369336589 3926312252155455138501221)
                  ·
                    refine ⟨736183547279147838468979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3926312252155455138501221 736183547279147838468979)
                    ·
                      rfl

theorem cell23_4301137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_4301137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301137 prefixEnd_4301137 := by exact prefixLift 4301137
  have htrace : WordTrace (prefixWord ++ tailWord_4301137) baseStart_4301137 baseEnd_4301137 := by
    simpa [prefixWord, tailWord_4301137, baseEnd_4301137] using wordTrace_append hprefix tailTrace_4301137
  have hstable : (prefixWord ++ tailWord_4301137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301137).length < 2 ^ (prefixWord ++ tailWord_4301137).sum := by decide
  have hdescent : baseEnd_4301137 < baseStart_4301137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301163 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 2, 9]
def baseStart_4301163 : Nat := 118140960795 + 4301163 * 2 ^ 59
def prefixEnd_4301163 : Nat := 4983230072969 + 3 ^ 40 * 4301163 * 2
def baseEnd_4301163 : Nat := 736187997444820137893939

theorem tailTrace_4301163 : CollatzResearch.WordTrace tailWord_4301163 prefixEnd_4301163 736187997444820137893939 := by
  unfold tailWord_4301163
  simp only [CollatzResearch.WordTrace]
  refine ⟨156876302516628506002596143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104584201677752337335064095 156876302516628506002596143)
  ·
    refine ⟨235314453774942759003894215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156876302516628506002596143 235314453774942759003894215)
    ·
      refine ⟨352971680662414138505841323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235314453774942759003894215 352971680662414138505841323)
      ·
        refine ⟨529457520993621207758761985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352971680662414138505841323 529457520993621207758761985)
        ·
          refine ⟨397093140745215905819071489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529457520993621207758761985 397093140745215905819071489)
          ·
            refine ⟨297819855558911929364303617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397093140745215905819071489 297819855558911929364303617)
            ·
              refine ⟨223364891669183947023227713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297819855558911929364303617 223364891669183947023227713)
              ·
                refine ⟨167523668751887960267420785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223364891669183947023227713 167523668751887960267420785)
                ·
                  refine ⟨125642751563915970200565589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167523668751887960267420785 125642751563915970200565589)
                  ·
                    refine ⟨736187997444820137893939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 125642751563915970200565589 736187997444820137893939)
                    ·
                      rfl

theorem cell23_4301163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 9].length) (baseStart_4301163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301163 prefixEnd_4301163 := by exact prefixLift 4301163
  have htrace : WordTrace (prefixWord ++ tailWord_4301163) baseStart_4301163 baseEnd_4301163 := by
    simpa [prefixWord, tailWord_4301163, baseEnd_4301163] using wordTrace_append hprefix tailTrace_4301163
  have hstable : (prefixWord ++ tailWord_4301163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301163).length < 2 ^ (prefixWord ++ tailWord_4301163).sum := by decide
  have hdescent : baseEnd_4301163 < baseStart_4301163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301164 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_4301164 : Nat := 118140960795 + 4301164 * 2 ^ 59
def prefixEnd_4301164 : Nat := 4983230072969 + 3 ^ 40 * 4301164 * 2
def baseEnd_4301164 : Nat := 2208564505815114909769313

theorem tailTrace_4301164 : CollatzResearch.WordTrace tailWord_4301164 prefixEnd_4301164 2208564505815114909769313 := by
  unfold tailWord_4301164
  simp only [CollatzResearch.WordTrace]
  refine ⟨78438169494812441586691273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104584225993083255448921697 78438169494812441586691273)
  ·
    refine ⟨58828627121109331190018455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78438169494812441586691273 58828627121109331190018455)
    ·
      refine ⟨88242940681663996785027683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58828627121109331190018455 88242940681663996785027683)
      ·
        refine ⟨132364411022495995177541525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88242940681663996785027683 132364411022495995177541525)
        ·
          refine ⟨6204581766679499773947259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132364411022495995177541525 6204581766679499773947259)
          ·
            refine ⟨9306872650019249660920889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6204581766679499773947259 9306872650019249660920889)
            ·
              refine ⟨6980154487514437245690667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9306872650019249660920889 6980154487514437245690667)
              ·
                refine ⟨10470231731271655868536001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980154487514437245690667 10470231731271655868536001)
                ·
                  refine ⟨7852673798453741901402001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10470231731271655868536001 7852673798453741901402001)
                  ·
                    refine ⟨5889505348840306426051501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7852673798453741901402001 5889505348840306426051501)
                    ·
                      refine ⟨2208564505815114909769313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5889505348840306426051501 2208564505815114909769313)
                      ·
                        rfl

theorem cell23_4301164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_4301164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301164 prefixEnd_4301164 := by exact prefixLift 4301164
  have htrace : WordTrace (prefixWord ++ tailWord_4301164) baseStart_4301164 baseEnd_4301164 := by
    simpa [prefixWord, tailWord_4301164, baseEnd_4301164] using wordTrace_append hprefix tailTrace_4301164
  have hstable : (prefixWord ++ tailWord_4301164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301164).length < 2 ^ (prefixWord ++ tailWord_4301164).sum := by decide
  have hdescent : baseEnd_4301164 < baseStart_4301164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301214 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4301214 : Nat := 118140960795 + 4301214 * 2 ^ 59
def prefixEnd_4301214 : Nat := 4983230072969 + 3 ^ 40 * 4301214 * 2
def baseEnd_4301214 : Nat := 736196726615946571381361

theorem tailTrace_4301214 : CollatzResearch.WordTrace tailWord_4301214 prefixEnd_4301214 736196726615946571381361 := by
  unfold tailWord_4301214
  simp only [CollatzResearch.WordTrace]
  refine ⟨19609770329930467714087837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104585441759629161141801797 19609770329930467714087837)
  ·
    refine ⟨7353663873723925392782939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19609770329930467714087837 7353663873723925392782939)
    ·
      refine ⟨11030495810585888089174409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7353663873723925392782939 11030495810585888089174409)
      ·
        refine ⟨8272871857939416066880807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11030495810585888089174409 8272871857939416066880807)
        ·
          refine ⟨12409307786909124100321211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8272871857939416066880807 12409307786909124100321211)
          ·
            refine ⟨18613961680363686150481817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12409307786909124100321211 18613961680363686150481817)
            ·
              refine ⟨13960471260272764612861363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18613961680363686150481817 13960471260272764612861363)
              ·
                refine ⟨20940706890409146919292045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13960471260272764612861363 20940706890409146919292045)
                ·
                  refine ⟨7852765083903430094734517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20940706890409146919292045 7852765083903430094734517)
                  ·
                    refine ⟨736196726615946571381361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7852765083903430094734517 736196726615946571381361)
                    ·
                      rfl

theorem cell23_4301214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4301214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301214 prefixEnd_4301214 := by exact prefixLift 4301214
  have htrace : WordTrace (prefixWord ++ tailWord_4301214) baseStart_4301214 baseEnd_4301214 := by
    simpa [prefixWord, tailWord_4301214, baseEnd_4301214] using wordTrace_append hprefix tailTrace_4301214
  have hstable : (prefixWord ++ tailWord_4301214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301214).length < 2 ^ (prefixWord ++ tailWord_4301214).sum := by decide
  have hdescent : baseEnd_4301214 < baseStart_4301214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301234 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_4301234 : Nat := 118140960795 + 4301234 * 2 ^ 59
def prefixEnd_4301234 : Nat := 4983230072969 + 3 ^ 40 * 4301234 * 2
def baseEnd_4301234 : Nat := 2208600449460929635893991

theorem tailTrace_4301234 : CollatzResearch.WordTrace tailWord_4301234 prefixEnd_4301234 2208600449460929635893991 := by
  unfold tailWord_4301234
  simp only [CollatzResearch.WordTrace]
  refine ⟨39219723024842821282107689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104585928066247523418953837 39219723024842821282107689)
  ·
    refine ⟨29414792268632115961580767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39219723024842821282107689 29414792268632115961580767)
    ·
      refine ⟨44122188402948173942371151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29414792268632115961580767 44122188402948173942371151)
      ·
        refine ⟨66183282604422260913556727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44122188402948173942371151 66183282604422260913556727)
        ·
          refine ⟨99274923906633391370335091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66183282604422260913556727 99274923906633391370335091)
          ·
            refine ⟨148912385859950087055502637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99274923906633391370335091 148912385859950087055502637)
            ·
              refine ⟨55842144697481282645813489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148912385859950087055502637 55842144697481282645813489)
              ·
                refine ⟨41881608523110961984360117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55842144697481282645813489 41881608523110961984360117)
                ·
                  refine ⟨3926400799041652686033761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41881608523110961984360117 3926400799041652686033761)
                  ·
                    refine ⟨2944800599281239514525321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3926400799041652686033761 2944800599281239514525321)
                    ·
                      refine ⟨2208600449460929635893991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944800599281239514525321 2208600449460929635893991)
                      ·
                        rfl

theorem cell23_4301234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_4301234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301234 prefixEnd_4301234 := by exact prefixLift 4301234
  have htrace : WordTrace (prefixWord ++ tailWord_4301234) baseStart_4301234 baseEnd_4301234 := by
    simpa [prefixWord, tailWord_4301234, baseEnd_4301234] using wordTrace_append hprefix tailTrace_4301234
  have hstable : (prefixWord ++ tailWord_4301234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301234).length < 2 ^ (prefixWord ++ tailWord_4301234).sum := by decide
  have hdescent : baseEnd_4301234 < baseStart_4301234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301244 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_4301244 : Nat := 118140960795 + 4301244 * 2 ^ 59
def prefixEnd_4301244 : Nat := 4983230072969 + 3 ^ 40 * 4301244 * 2
def baseEnd_4301244 : Nat := 736201861422491532256315

theorem tailTrace_4301244 : CollatzResearch.WordTrace tailWord_4301244 prefixEnd_4301244 736201861422491532256315 := by
  unfold tailWord_4301244
  simp only [CollatzResearch.WordTrace]
  refine ⟨78439628414667528418147393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104586171219556704557529857 78439628414667528418147393)
  ·
    refine ⟨58829721311000646313610545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78439628414667528418147393 58829721311000646313610545)
    ·
      refine ⟨44122290983250484735207909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58829721311000646313610545 44122290983250484735207909)
      ·
        refine ⟨8272929559359465887851483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44122290983250484735207909 8272929559359465887851483)
        ·
          refine ⟨12409394339039198831777225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8272929559359465887851483 12409394339039198831777225)
          ·
            refine ⟨9307045754279399123832919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12409394339039198831777225 9307045754279399123832919)
            ·
              refine ⟨13960568631419098685749379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9307045754279399123832919 13960568631419098685749379)
              ·
                refine ⟨20940852947128648028624069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13960568631419098685749379 20940852947128648028624069)
                ·
                  refine ⟨3926409927586621505367013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20940852947128648028624069 3926409927586621505367013)
                  ·
                    refine ⟨736201861422491532256315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3926409927586621505367013 736201861422491532256315)
                    ·
                      rfl

theorem cell23_4301244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_4301244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301244 prefixEnd_4301244 := by exact prefixLift 4301244
  have htrace : WordTrace (prefixWord ++ tailWord_4301244) baseStart_4301244 baseEnd_4301244 := by
    simpa [prefixWord, tailWord_4301244, baseEnd_4301244] using wordTrace_append hprefix tailTrace_4301244
  have hstable : (prefixWord ++ tailWord_4301244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301244).length < 2 ^ (prefixWord ++ tailWord_4301244).sum := by decide
  have hdescent : baseEnd_4301244 < baseStart_4301244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301280 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_4301280 : Nat := 118140960795 + 4301280 * 2 ^ 59
def prefixEnd_4301280 : Nat := 4983230072969 + 3 ^ 40 * 4301280 * 2
def baseEnd_4301280 : Nat := 2208624069571036455918779

theorem tailTrace_4301280 : CollatzResearch.WordTrace tailWord_4301280 prefixEnd_4301280 2208624069571036455918779 := by
  unfold tailWord_4301280
  simp only [CollatzResearch.WordTrace]
  refine ⟨78440284928602317492302647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104587046571469756656403529 78440284928602317492302647)
  ·
    refine ⟨117660427392903476238453971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78440284928602317492302647 117660427392903476238453971)
    ·
      refine ⟨176490641089355214357680957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117660427392903476238453971 176490641089355214357680957)
      ·
        refine ⟨66183990408508205384130359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176490641089355214357680957 66183990408508205384130359)
        ·
          refine ⟨99275985612762308076195539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66183990408508205384130359 99275985612762308076195539)
          ·
            refine ⟨148913978419143462114293309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99275985612762308076195539 148913978419143462114293309)
            ·
              refine ⟨55842741907178798292859991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148913978419143462114293309 55842741907178798292859991)
              ·
                refine ⟨83764112860768197439289987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55842741907178798292859991 83764112860768197439289987)
                ·
                  refine ⟨125646169291152296158934981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83764112860768197439289987 125646169291152296158934981)
                  ·
                    refine ⟨23558656742091055529800309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125646169291152296158934981 23558656742091055529800309)
                    ·
                      refine ⟨2208624069571036455918779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23558656742091055529800309 2208624069571036455918779)
                      ·
                        rfl

theorem cell23_4301280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_4301280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301280 prefixEnd_4301280 := by exact prefixLift 4301280
  have htrace : WordTrace (prefixWord ++ tailWord_4301280) baseStart_4301280 baseEnd_4301280 := by
    simpa [prefixWord, tailWord_4301280, baseEnd_4301280] using wordTrace_append hprefix tailTrace_4301280
  have hstable : (prefixWord ++ tailWord_4301280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301280).length < 2 ^ (prefixWord ++ tailWord_4301280).sum := by decide
  have hdescent : baseEnd_4301280 < baseStart_4301280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301307 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 2, 8, 2]
def baseStart_4301307 : Nat := 118140960795 + 4301307 * 2 ^ 59
def prefixEnd_4301307 : Nat := 4983230072969 + 3 ^ 40 * 4301307 * 2
def baseEnd_4301307 : Nat := 2208637933548707850281155

theorem tailTrace_4301307 : CollatzResearch.WordTrace tailWord_4301307 prefixEnd_4301307 2208637933548707850281155 := by
  unfold tailWord_4301307
  simp only [CollatzResearch.WordTrace]
  refine ⟨156881554628106818595838175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104587703085404545730558783 156881554628106818595838175)
  ·
    refine ⟨235322331942160227893757263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156881554628106818595838175 235322331942160227893757263)
    ·
      refine ⟨352983497913240341840635895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235322331942160227893757263 352983497913240341840635895)
      ·
        refine ⟨529475246869860512760953843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352983497913240341840635895 529475246869860512760953843)
        ·
          refine ⟨794212870304790769141430765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529475246869860512760953843 794212870304790769141430765)
          ·
            refine ⟨297829826364296538428036537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 794212870304790769141430765 297829826364296538428036537)
            ·
              refine ⟨223372369773222403821027403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297829826364296538428036537 223372369773222403821027403)
              ·
                refine ⟨335058554659833605731541105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223372369773222403821027403 335058554659833605731541105)
                ·
                  refine ⟨251293915994875204298655829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335058554659833605731541105 251293915994875204298655829)
                  ·
                    refine ⟨2944850578064943800374873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 251293915994875204298655829 2944850578064943800374873)
                    ·
                      refine ⟨2208637933548707850281155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944850578064943800374873 2208637933548707850281155)
                      ·
                        rfl

theorem cell23_4301307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8, 2].length) (baseStart_4301307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301307 prefixEnd_4301307 := by exact prefixLift 4301307
  have htrace : WordTrace (prefixWord ++ tailWord_4301307) baseStart_4301307 baseEnd_4301307 := by
    simpa [prefixWord, tailWord_4301307, baseEnd_4301307] using wordTrace_append hprefix tailTrace_4301307
  have hstable : (prefixWord ++ tailWord_4301307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301307).length < 2 ^ (prefixWord ++ tailWord_4301307).sum := by decide
  have hdescent : baseEnd_4301307 < baseStart_4301307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301341 : List Nat := [1, 4, 2, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_4301341 : Nat := 118140960795 + 4301341 * 2 ^ 59
def prefixEnd_4301341 : Nat := 4983230072969 + 3 ^ 40 * 4301341 * 2
def baseEnd_4301341 : Nat := 2208655391890960717255999

theorem tailTrace_4301341 : CollatzResearch.WordTrace tailWord_4301341 prefixEnd_4301341 2208655391890960717255999 := by
  unfold tailWord_4301341
  simp only [CollatzResearch.WordTrace]
  refine ⟨156882794709983642402575877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104588529806655761601717251 156882794709983642402575877)
  ·
    refine ⟨29415524008121932950482977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156882794709983642402575877 29415524008121932950482977)
    ·
      refine ⟨22061643006091449712862233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29415524008121932950482977 22061643006091449712862233)
      ·
        refine ⟨16546232254568587284646675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22061643006091449712862233 16546232254568587284646675)
        ·
          refine ⟨24819348381852880926970013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16546232254568587284646675 24819348381852880926970013)
          ·
            refine ⟨9307255643194830347613755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24819348381852880926970013 9307255643194830347613755)
            ·
              refine ⟨13960883464792245521420633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9307255643194830347613755 13960883464792245521420633)
              ·
                refine ⟨10470662598594184141065475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13960883464792245521420633 10470662598594184141065475)
                ·
                  refine ⟨15705993897891276211598213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10470662598594184141065475 15705993897891276211598213)
                  ·
                    refine ⟨2944873855854614289674665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15705993897891276211598213 2944873855854614289674665)
                    ·
                      refine ⟨2208655391890960717255999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944873855854614289674665 2208655391890960717255999)
                      ·
                        rfl

theorem cell23_4301341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_4301341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301341 prefixEnd_4301341 := by exact prefixLift 4301341
  have htrace : WordTrace (prefixWord ++ tailWord_4301341) baseStart_4301341 baseEnd_4301341 := by
    simpa [prefixWord, tailWord_4301341, baseEnd_4301341] using wordTrace_append hprefix tailTrace_4301341
  have hstable : (prefixWord ++ tailWord_4301341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301341).length < 2 ^ (prefixWord ++ tailWord_4301341).sum := by decide
  have hdescent : baseEnd_4301341 < baseStart_4301341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301477 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_4301477 : Nat := 118140960795 + 4301477 * 2 ^ 59
def prefixEnd_4301477 : Nat := 4983230072969 + 3 ^ 40 * 4301477 * 2
def baseEnd_4301477 : Nat := 2208725225259972185155373

theorem tailTrace_4301477 : CollatzResearch.WordTrace tailWord_4301477 prefixEnd_4301477 2208725225259972185155373 := by
  unfold tailWord_4301477
  simp only [CollatzResearch.WordTrace]
  refine ⟨156887755037490937629526685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104591836691660625086351123 156887755037490937629526685)
  ·
    refine ⟨58832908139059101611072507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156887755037490937629526685 58832908139059101611072507)
    ·
      refine ⟨88249362208588652416608761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58832908139059101611072507 88249362208588652416608761)
      ·
        refine ⟨66187021656441489312456571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88249362208588652416608761 66187021656441489312456571)
        ·
          refine ⟨99280532484662233968684857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66187021656441489312456571 99280532484662233968684857)
          ·
            refine ⟨74460399363496675476513643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99280532484662233968684857 74460399363496675476513643)
            ·
              refine ⟨111690599045245013214770465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74460399363496675476513643 111690599045245013214770465)
              ·
                refine ⟨83767949283933759911077849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111690599045245013214770465 83767949283933759911077849)
                ·
                  refine ⟨62825961962950319933308387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83767949283933759911077849 62825961962950319933308387)
                  ·
                    refine ⟨94238942944425479899962581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62825961962950319933308387 94238942944425479899962581)
                    ·
                      refine ⟨2208725225259972185155373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94238942944425479899962581 2208725225259972185155373)
                      ·
                        rfl

theorem cell23_4301477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_4301477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301477 prefixEnd_4301477 := by exact prefixLift 4301477
  have htrace : WordTrace (prefixWord ++ tailWord_4301477) baseStart_4301477 baseEnd_4301477 := by
    simpa [prefixWord, tailWord_4301477, baseEnd_4301477] using wordTrace_append hprefix tailTrace_4301477
  have hstable : (prefixWord ++ tailWord_4301477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301477).length < 2 ^ (prefixWord ++ tailWord_4301477).sum := by decide
  have hdescent : baseEnd_4301477 < baseStart_4301477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301501 : List Nat := [1, 4, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_4301501 : Nat := 118140960795 + 4301501 * 2 ^ 59
def prefixEnd_4301501 : Nat := 4983230072969 + 3 ^ 40 * 4301501 * 2
def baseEnd_4301501 : Nat := 736245849598560030418421

theorem tailTrace_4301501 : CollatzResearch.WordTrace tailWord_4301501 prefixEnd_4301501 736245849598560030418421 := by
  unfold tailWord_4301501
  simp only [CollatzResearch.WordTrace]
  refine ⟨156888630389403989728400357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104592420259602659818933571 156888630389403989728400357)
  ·
    refine ⟨29416618198013248074075067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156888630389403989728400357 29416618198013248074075067)
    ·
      refine ⟨44124927297019872111112601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29416618198013248074075067 44124927297019872111112601)
      ·
        refine ⟨33093695472764904083334451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44124927297019872111112601 33093695472764904083334451)
        ·
          refine ⟨49640543209147356125001677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33093695472764904083334451 49640543209147356125001677)
          ·
            refine ⟨18615203703430258546875629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49640543209147356125001677 18615203703430258546875629)
            ·
              refine ⟨6980701388786346955078361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18615203703430258546875629 6980701388786346955078361)
              ·
                refine ⟨5235526041589760216308771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6980701388786346955078361 5235526041589760216308771)
                ·
                  refine ⟨7853289062384640324463157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235526041589760216308771 7853289062384640324463157)
                  ·
                    refine ⟨736245849598560030418421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7853289062384640324463157 736245849598560030418421)
                    ·
                      rfl

theorem cell23_4301501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_4301501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301501 prefixEnd_4301501 := by exact prefixLift 4301501
  have htrace : WordTrace (prefixWord ++ tailWord_4301501) baseStart_4301501 baseEnd_4301501 := by
    simpa [prefixWord, tailWord_4301501, baseEnd_4301501] using wordTrace_append hprefix tailTrace_4301501
  have hstable : (prefixWord ++ tailWord_4301501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301501).length < 2 ^ (prefixWord ++ tailWord_4301501).sum := by decide
  have hdescent : baseEnd_4301501 < baseStart_4301501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301507 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5]
def baseStart_4301507 : Nat := 118140960795 + 4301507 * 2 ^ 59
def prefixEnd_4301507 : Nat := 4983230072969 + 3 ^ 40 * 4301507 * 2
def baseEnd_4301507 : Nat := 2208740629679607067780235

theorem tailTrace_4301507 : CollatzResearch.WordTrace tailWord_4301507 prefixEnd_4301507 2208740629679607067780235 := by
  unfold tailWord_4301507
  simp only [CollatzResearch.WordTrace]
  refine ⟨156888849227382252753118775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104592566151588168502079183 156888849227382252753118775)
  ·
    refine ⟨235333273841073379129678163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156888849227382252753118775 235333273841073379129678163)
    ·
      refine ⟨352999910761610068694517245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235333273841073379129678163 352999910761610068694517245)
      ·
        refine ⟨132374966535603775760443967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352999910761610068694517245 132374966535603775760443967)
        ·
          refine ⟨198562449803405663640665951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132374966535603775760443967 198562449803405663640665951)
          ·
            refine ⟨297843674705108495460998927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198562449803405663640665951 297843674705108495460998927)
            ·
              refine ⟨446765512057662743191498391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297843674705108495460998927 446765512057662743191498391)
              ·
                refine ⟨670148268086494114787247587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446765512057662743191498391 670148268086494114787247587)
                ·
                  refine ⟨1005222402129741172180871381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670148268086494114787247587 1005222402129741172180871381)
                  ·
                    refine ⟨23559900049915808722989173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1005222402129741172180871381 23559900049915808722989173)
                    ·
                      refine ⟨2208740629679607067780235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23559900049915808722989173 2208740629679607067780235)
                      ·
                        rfl

theorem cell23_4301507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_4301507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301507 prefixEnd_4301507 := by exact prefixLift 4301507
  have htrace : WordTrace (prefixWord ++ tailWord_4301507) baseStart_4301507 baseEnd_4301507 := by
    simpa [prefixWord, tailWord_4301507, baseEnd_4301507] using wordTrace_append hprefix tailTrace_4301507
  have hstable : (prefixWord ++ tailWord_4301507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301507).length < 2 ^ (prefixWord ++ tailWord_4301507).sum := by decide
  have hdescent : baseEnd_4301507 < baseStart_4301507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301508 : List Nat := [2, 3, 3, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_4301508 : Nat := 118140960795 + 4301508 * 2 ^ 59
def prefixEnd_4301508 : Nat := 4983230072969 + 3 ^ 40 * 4301508 * 2
def baseEnd_4301508 : Nat := 2208741143160261563867731

theorem tailTrace_4301508 : CollatzResearch.WordTrace tailWord_4301508 prefixEnd_4301508 2208741143160261563867731 := by
  unfold tailWord_4301508
  simp only [CollatzResearch.WordTrace]
  refine ⟨78444442850189314961952589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104592590466919086615936785 78444442850189314961952589)
  ·
    refine ⟨29416666068820993110732221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78444442850189314961952589 29416666068820993110732221)
    ·
      refine ⟨11031249775807872416524583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29416666068820993110732221 11031249775807872416524583)
      ·
        refine ⟨16546874663711808624786875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11031249775807872416524583 16546874663711808624786875)
        ·
          refine ⟨24820311995567712937180313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16546874663711808624786875 24820311995567712937180313)
          ·
            refine ⟨18615233996675784702885235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24820311995567712937180313 18615233996675784702885235)
            ·
              refine ⟨27922850995013677054327853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18615233996675784702885235 27922850995013677054327853)
              ·
                refine ⟨10471069123130128895372945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27922850995013677054327853 10471069123130128895372945)
                ·
                  refine ⟨7853301842347596671529709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10471069123130128895372945 7853301842347596671529709)
                  ·
                    refine ⟨2944988190880348751823641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7853301842347596671529709 2944988190880348751823641)
                    ·
                      refine ⟨2208741143160261563867731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2944988190880348751823641 2208741143160261563867731)
                      ·
                        rfl

theorem cell23_4301508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_4301508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301508 prefixEnd_4301508 := by exact prefixLift 4301508
  have htrace : WordTrace (prefixWord ++ tailWord_4301508) baseStart_4301508 baseEnd_4301508 := by
    simpa [prefixWord, tailWord_4301508, baseEnd_4301508] using wordTrace_append hprefix tailTrace_4301508
  have hstable : (prefixWord ++ tailWord_4301508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301508).length < 2 ^ (prefixWord ++ tailWord_4301508).sum := by decide
  have hdescent : baseEnd_4301508 < baseStart_4301508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301514 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 3, 6]
def baseStart_4301514 : Nat := 118140960795 + 4301514 * 2 ^ 59
def prefixEnd_4301514 : Nat := 4983230072969 + 3 ^ 40 * 4301514 * 2
def baseEnd_4301514 : Nat := 736248074681396180130901

theorem tailTrace_4301514 : CollatzResearch.WordTrace tailWord_4301514 prefixEnd_4301514 736248074681396180130901 := by
  unfold tailWord_4301514
  simp only [CollatzResearch.WordTrace]
  refine ⟨39222276134589223237155899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104592736358904595299082397 39222276134589223237155899)
  ·
    refine ⟨58833414201883834855733849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39222276134589223237155899 58833414201883834855733849)
    ·
      refine ⟨44125060651412876141800387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58833414201883834855733849 44125060651412876141800387)
      ·
        refine ⟨66187590977119314212700581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44125060651412876141800387 66187590977119314212700581)
        ·
          refine ⟨12410173308209871414881359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66187590977119314212700581 12410173308209871414881359)
          ·
            refine ⟨18615259962314807122322039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410173308209871414881359 18615259962314807122322039)
            ·
              refine ⟨27922889943472210683483059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18615259962314807122322039 27922889943472210683483059)
              ·
                refine ⟨41884334915208316025224589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27922889943472210683483059 41884334915208316025224589)
                ·
                  refine ⟨15706625593203118509459221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41884334915208316025224589 15706625593203118509459221)
                  ·
                    refine ⟨736248074681396180130901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15706625593203118509459221 736248074681396180130901)
                    ·
                      rfl

theorem cell23_4301514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_4301514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301514 prefixEnd_4301514 := by exact prefixLift 4301514
  have htrace : WordTrace (prefixWord ++ tailWord_4301514) baseStart_4301514 baseEnd_4301514 := by
    simpa [prefixWord, tailWord_4301514, baseEnd_4301514] using wordTrace_append hprefix tailTrace_4301514
  have hstable : (prefixWord ++ tailWord_4301514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301514).length < 2 ^ (prefixWord ++ tailWord_4301514).sum := by decide
  have hdescent : baseEnd_4301514 < baseStart_4301514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301518 : List Nat := [4, 1, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_4301518 : Nat := 118140960795 + 4301518 * 2 ^ 59
def prefixEnd_4301518 : Nat := 4983230072969 + 3 ^ 40 * 4301518 * 2
def baseEnd_4301518 : Nat := 736248759322268841580895

theorem tailTrace_4301518 : CollatzResearch.WordTrace tailWord_4301518 prefixEnd_4301518 736248759322268841580895 := by
  unfold tailWord_4301518
  simp only [CollatzResearch.WordTrace]
  refine ⟨19611156303792800203971151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104592833620228267754512805 19611156303792800203971151)
  ·
    refine ⟨29416734455689200305956727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19611156303792800203971151 29416734455689200305956727)
    ·
      refine ⟨44125101683533800458935091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29416734455689200305956727 44125101683533800458935091)
      ·
        refine ⟨66187652525300700688402637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44125101683533800458935091 66187652525300700688402637)
        ·
          refine ⟨24820369696987762758150989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66187652525300700688402637 24820369696987762758150989)
          ·
            refine ⟨9307638636370411034306621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24820369696987762758150989 9307638636370411034306621)
            ·
              refine ⟨3490364488638904137864983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9307638636370411034306621 3490364488638904137864983)
              ·
                refine ⟨5235546732958356206797475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490364488638904137864983 5235546732958356206797475)
                ·
                  refine ⟨7853320099437534310196213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235546732958356206797475 7853320099437534310196213)
                  ·
                    refine ⟨736248759322268841580895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7853320099437534310196213 736248759322268841580895)
                    ·
                      rfl

theorem cell23_4301518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_4301518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301518 prefixEnd_4301518 := by exact prefixLift 4301518
  have htrace : WordTrace (prefixWord ++ tailWord_4301518) baseStart_4301518 baseEnd_4301518 := by
    simpa [prefixWord, tailWord_4301518, baseEnd_4301518] using wordTrace_append hprefix tailTrace_4301518
  have hstable : (prefixWord ++ tailWord_4301518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301518).length < 2 ^ (prefixWord ++ tailWord_4301518).sum := by decide
  have hdescent : baseEnd_4301518 < baseStart_4301518 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301527 : List Nat := [1, 1, 3, 2, 1, 15]
def baseStart_4301527 : Nat := 118140960795 + 4301527 * 2 ^ 59
def prefixEnd_4301527 : Nat := 4983230072969 + 3 ^ 40 * 4301527 * 2
def baseEnd_4301527 : Nat := 9089509873632497899301

theorem tailTrace_4301527 : CollatzResearch.WordTrace tailWord_4301527 prefixEnd_4301527 9089509873632497899301 := by
  unfold tailWord_4301527
  simp only [CollatzResearch.WordTrace]
  refine ⟨156889578687309796168846835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104593052458206530779231223 156889578687309796168846835)
  ·
    refine ⟨235334368030964694253270253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156889578687309796168846835 235334368030964694253270253)
    ·
      refine ⟨88250388011611760344976345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235334368030964694253270253 88250388011611760344976345)
      ·
        refine ⟨66187791008708820258732259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88250388011611760344976345 66187791008708820258732259)
        ·
          refine ⟨99281686513063230388098389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66187791008708820258732259 99281686513063230388098389)
          ·
            refine ⟨9089509873632497899301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 99281686513063230388098389 9089509873632497899301)
            ·
              rfl

theorem cell23_4301527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 15].length) (baseStart_4301527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301527 prefixEnd_4301527 := by exact prefixLift 4301527
  have htrace : WordTrace (prefixWord ++ tailWord_4301527) baseStart_4301527 baseEnd_4301527 := by
    simpa [prefixWord, tailWord_4301527, baseEnd_4301527] using wordTrace_append hprefix tailTrace_4301527
  have hstable : (prefixWord ++ tailWord_4301527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301527).length < 2 ^ (prefixWord ++ tailWord_4301527).sum := by decide
  have hdescent : baseEnd_4301527 < baseStart_4301527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301532 : List Nat := [2, 2, 5, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4301532 : Nat := 118140960795 + 4301532 * 2 ^ 59
def prefixEnd_4301532 : Nat := 4983230072969 + 3 ^ 40 * 4301532 * 2
def baseEnd_4301532 : Nat := 2208753466695969469967621

theorem tailTrace_4301532 : CollatzResearch.WordTrace tailWord_4301532 prefixEnd_4301532 2208753466695969469967621 := by
  unfold tailWord_4301532
  simp only [CollatzResearch.WordTrace]
  refine ⟨78444880526145841011389425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104593174034861121348519233 78444880526145841011389425)
  ·
    refine ⟨58833660394609380758542069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78444880526145841011389425 58833660394609380758542069)
    ·
      refine ⟨5515655661994629446113319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58833660394609380758542069 5515655661994629446113319)
      ·
        refine ⟨8273483492991944169169979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5515655661994629446113319 8273483492991944169169979)
        ·
          refine ⟨12410225239487916253754969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8273483492991944169169979 12410225239487916253754969)
          ·
            refine ⟨9307668929615937190316227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12410225239487916253754969 9307668929615937190316227)
            ·
              refine ⟨13961503394423905785474341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9307668929615937190316227 13961503394423905785474341)
              ·
                refine ⟨2617781886454482334776439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13961503394423905785474341 2617781886454482334776439)
                ·
                  refine ⟨3926672829681723502164659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617781886454482334776439 3926672829681723502164659)
                  ·
                    refine ⟨5890009244522585253246989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3926672829681723502164659 5890009244522585253246989)
                    ·
                      refine ⟨2208753466695969469967621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890009244522585253246989 2208753466695969469967621)
                      ·
                        rfl

theorem cell23_4301532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4301532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301532 prefixEnd_4301532 := by exact prefixLift 4301532
  have htrace : WordTrace (prefixWord ++ tailWord_4301532) baseStart_4301532 baseEnd_4301532 := by
    simpa [prefixWord, tailWord_4301532, baseEnd_4301532] using wordTrace_append hprefix tailTrace_4301532
  have hstable : (prefixWord ++ tailWord_4301532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301532).length < 2 ^ (prefixWord ++ tailWord_4301532).sum := by decide
  have hdescent : baseEnd_4301532 < baseStart_4301532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301541 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4301541 : Nat := 118140960795 + 4301541 * 2 ^ 59
def prefixEnd_4301541 : Nat := 4983230072969 + 3 ^ 40 * 4301541 * 2
def baseEnd_4301541 : Nat := 2208758088021859934755079

theorem tailTrace_4301541 : CollatzResearch.WordTrace tailWord_4301541 prefixEnd_4301541 2208758088021859934755079 := by
  unfold tailWord_4301541
  simp only [CollatzResearch.WordTrace]
  refine ⟨156890089309259076559856477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104593392872839384373237651 156890089309259076559856477)
  ·
    refine ⟨58833783490972153709946179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156890089309259076559856477 58833783490972153709946179)
    ·
      refine ⟨88250675236458230564919269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58833783490972153709946179 88250675236458230564919269)
      ·
        refine ⟨16547001606835918230922363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88250675236458230564919269 16547001606835918230922363)
        ·
          refine ⟨24820502410253877346383545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16547001606835918230922363 24820502410253877346383545)
          ·
            refine ⟨18615376807690408009787659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24820502410253877346383545 18615376807690408009787659)
            ·
              refine ⟨27923065211535612014681489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18615376807690408009787659 27923065211535612014681489)
              ·
                refine ⟨20942298908651709011011117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27923065211535612014681489 20942298908651709011011117)
                ·
                  refine ⟨7853362090744390879129169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20942298908651709011011117 7853362090744390879129169)
                  ·
                    refine ⟨5890021568058293159346877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7853362090744390879129169 5890021568058293159346877)
                    ·
                      refine ⟨2208758088021859934755079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890021568058293159346877 2208758088021859934755079)
                      ·
                        rfl

theorem cell23_4301541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4301541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301541 prefixEnd_4301541 := by exact prefixLift 4301541
  have htrace : WordTrace (prefixWord ++ tailWord_4301541) baseStart_4301541 baseEnd_4301541 := by
    simpa [prefixWord, tailWord_4301541, baseEnd_4301541] using wordTrace_append hprefix tailTrace_4301541
  have hstable : (prefixWord ++ tailWord_4301541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301541).length < 2 ^ (prefixWord ++ tailWord_4301541).sum := by decide
  have hdescent : baseEnd_4301541 < baseStart_4301541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301551 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4]
def baseStart_4301551 : Nat := 118140960795 + 4301551 * 2 ^ 59
def prefixEnd_4301551 : Nat := 4983230072969 + 3 ^ 40 * 4301551 * 2
def baseEnd_4301551 : Nat := 2208763222828404895630033

theorem tailTrace_4301551 : CollatzResearch.WordTrace tailWord_4301551 prefixEnd_4301551 2208763222828404895630033 := by
  unfold tailWord_4301551
  simp only [CollatzResearch.WordTrace]
  refine ⟨156890454039222848267720507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104593636026148565511813671 156890454039222848267720507)
  ·
    refine ⟨235335681058834272401580761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156890454039222848267720507 235335681058834272401580761)
    ·
      refine ⟨176501760794125704301185571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235335681058834272401580761 176501760794125704301185571)
      ·
        refine ⟨264752641191188556451778357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176501760794125704301185571 264752641191188556451778357)
        ·
          refine ⟨24820560111673927167354221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264752641191188556451778357 24820560111673927167354221)
          ·
            refine ⟨9307710041877722687757833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24820560111673927167354221 9307710041877722687757833)
            ·
              refine ⟨6980782531408292015818375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9307710041877722687757833 6980782531408292015818375)
              ·
                refine ⟨10471173797112438023727563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6980782531408292015818375 10471173797112438023727563)
                ·
                  refine ⟨15706760695668657035591345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10471173797112438023727563 15706760695668657035591345)
                  ·
                    refine ⟨11780070521751492776693509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15706760695668657035591345 11780070521751492776693509)
                    ·
                      refine ⟨2208763222828404895630033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11780070521751492776693509 2208763222828404895630033)
                      ·
                        rfl

theorem cell23_4301551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 4].length) (baseStart_4301551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301551 prefixEnd_4301551 := by exact prefixLift 4301551
  have htrace : WordTrace (prefixWord ++ tailWord_4301551) baseStart_4301551 baseEnd_4301551 := by
    simpa [prefixWord, tailWord_4301551, baseEnd_4301551] using wordTrace_append hprefix tailTrace_4301551
  have hstable : (prefixWord ++ tailWord_4301551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301551).length < 2 ^ (prefixWord ++ tailWord_4301551).sum := by decide
  have hdescent : baseEnd_4301551 < baseStart_4301551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301558 : List Nat := [5, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4301558 : Nat := 118140960795 + 4301558 * 2 ^ 59
def prefixEnd_4301558 : Nat := 4983230072969 + 3 ^ 40 * 4301558 * 2
def baseEnd_4301558 : Nat := 2208766817192986368242501

theorem tailTrace_4301558 : CollatzResearch.WordTrace tailWord_4301558 prefixEnd_4301558 2208766817192986368242501 := by
  unfold tailWord_4301558
  simp only [CollatzResearch.WordTrace]
  refine ⟨9805669334387343028951583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104593806233464992308816885 9805669334387343028951583)
  ·
    refine ⟨14708504001581014543427375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9805669334387343028951583 14708504001581014543427375)
    ·
      refine ⟨22062756002371521815141063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14708504001581014543427375 22062756002371521815141063)
      ·
        refine ⟨33094134003557282722711595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22062756002371521815141063 33094134003557282722711595)
        ·
          refine ⟨49641201005335924084067393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33094134003557282722711595 49641201005335924084067393)
          ·
            refine ⟨37230900754001943063050545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49641201005335924084067393 37230900754001943063050545)
            ·
              refine ⟨27923175565501457297287909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37230900754001943063050545 27923175565501457297287909)
              ·
                refine ⟨5235595418531523243241483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27923175565501457297287909 5235595418531523243241483)
                ·
                  refine ⟨7853393127797284864862225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235595418531523243241483 7853393127797284864862225)
                  ·
                    refine ⟨5890044845847963648646669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7853393127797284864862225 5890044845847963648646669)
                    ·
                      refine ⟨2208766817192986368242501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890044845847963648646669 2208766817192986368242501)
                      ·
                        rfl

theorem cell23_4301558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4301558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301558 prefixEnd_4301558 := by exact prefixLift 4301558
  have htrace : WordTrace (prefixWord ++ tailWord_4301558) baseStart_4301558 baseEnd_4301558 := by
    simpa [prefixWord, tailWord_4301558, baseEnd_4301558] using wordTrace_append hprefix tailTrace_4301558
  have hstable : (prefixWord ++ tailWord_4301558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301558).length < 2 ^ (prefixWord ++ tailWord_4301558).sum := by decide
  have hdescent : baseEnd_4301558 < baseStart_4301558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301571 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 3]
def baseStart_4301571 : Nat := 118140960795 + 4301571 * 2 ^ 59
def prefixEnd_4301571 : Nat := 4983230072969 + 3 ^ 40 * 4301571 * 2
def baseEnd_4301571 : Nat := 2208773492441494817379941

theorem tailTrace_4301571 : CollatzResearch.WordTrace tailWord_4301571 prefixEnd_4301571 2208773492441494817379941 := by
  unfold tailWord_4301571
  simp only [CollatzResearch.WordTrace]
  refine ⟨156891183499150391683448567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104594122332766927788965711 156891183499150391683448567)
  ·
    refine ⟨235336775248725587525172851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156891183499150391683448567 235336775248725587525172851)
    ·
      refine ⟨353005162873088381287759277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235336775248725587525172851 353005162873088381287759277)
      ·
        refine ⟨132376936077408142982909729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353005162873088381287759277 132376936077408142982909729)
        ·
          refine ⟨99282702058056107237182297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132376936077408142982909729 99282702058056107237182297)
          ·
            refine ⟨74462026543542080427886723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99282702058056107237182297 74462026543542080427886723)
            ·
              refine ⟨111693039815313120641830085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74462026543542080427886723 111693039815313120641830085)
              ·
                refine ⟨20942444965371210120343141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111693039815313120641830085 20942444965371210120343141)
                ·
                  refine ⟨3926708431007101897564339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20942444965371210120343141 3926708431007101897564339)
                  ·
                    refine ⟨5890062646510652846346509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3926708431007101897564339 5890062646510652846346509)
                    ·
                      refine ⟨2208773492441494817379941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890062646510652846346509 2208773492441494817379941)
                      ·
                        rfl

theorem cell23_4301571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_4301571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301571 prefixEnd_4301571 := by exact prefixLift 4301571
  have htrace : WordTrace (prefixWord ++ tailWord_4301571) baseStart_4301571 baseEnd_4301571 := by
    simpa [prefixWord, tailWord_4301571, baseEnd_4301571] using wordTrace_append hprefix tailTrace_4301571
  have hstable : (prefixWord ++ tailWord_4301571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301571).length < 2 ^ (prefixWord ++ tailWord_4301571).sum := by decide
  have hdescent : baseEnd_4301571 < baseStart_4301571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301572 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_4301572 : Nat := 118140960795 + 4301572 * 2 ^ 59
def prefixEnd_4301572 : Nat := 4983230072969 + 3 ^ 40 * 4301572 * 2
def baseEnd_4301572 : Nat := 2208774005922149313467437

theorem tailTrace_4301572 : CollatzResearch.WordTrace tailWord_4301572 prefixEnd_4301572 2208774005922149313467437 := by
  unfold tailWord_4301572
  simp only [CollatzResearch.WordTrace]
  refine ⟨78445609986073384427117485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104594146648097845902823313 78445609986073384427117485)
  ·
    refine ⟨29417103744777519160169057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78445609986073384427117485 29417103744777519160169057)
    ·
      refine ⟨22062827808583139370126793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29417103744777519160169057 22062827808583139370126793)
      ·
        refine ⟨16547120856437354527595095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22062827808583139370126793 16547120856437354527595095)
        ·
          refine ⟨24820681284656031791392643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16547120856437354527595095 24820681284656031791392643)
          ·
            refine ⟨37231021926984047687088965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24820681284656031791392643 37231021926984047687088965)
            ·
              refine ⟨6980816611309508941329181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37231021926984047687088965 6980816611309508941329181)
              ·
                refine ⟨2617806229241065852998443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6980816611309508941329181 2617806229241065852998443)
                ·
                  refine ⟨3926709343861598779497665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2617806229241065852998443 3926709343861598779497665)
                  ·
                    refine ⟨2945032007896199084623249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3926709343861598779497665 2945032007896199084623249)
                    ·
                      refine ⟨2208774005922149313467437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945032007896199084623249 2208774005922149313467437)
                      ·
                        rfl

theorem cell23_4301572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_4301572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301572 prefixEnd_4301572 := by exact prefixLift 4301572
  have htrace : WordTrace (prefixWord ++ tailWord_4301572) baseStart_4301572 baseEnd_4301572 := by
    simpa [prefixWord, tailWord_4301572, baseEnd_4301572] using wordTrace_append hprefix tailTrace_4301572
  have hstable : (prefixWord ++ tailWord_4301572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301572).length < 2 ^ (prefixWord ++ tailWord_4301572).sum := by decide
  have hdescent : baseEnd_4301572 < baseStart_4301572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301575 : List Nat := [1, 1, 4, 4, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4301575 : Nat := 118140960795 + 4301575 * 2 ^ 59
def prefixEnd_4301575 : Nat := 4983230072969 + 3 ^ 40 * 4301575 * 2
def baseEnd_4301575 : Nat := 2208775546364112801729923

theorem tailTrace_4301575 : CollatzResearch.WordTrace tailWord_4301575 prefixEnd_4301575 2208775546364112801729923 := by
  unfold tailWord_4301575
  simp only [CollatzResearch.WordTrace]
  refine ⟨156891329391135900366594179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104594219594090600244396119 156891329391135900366594179)
  ·
    refine ⟨235336994086703850549891269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156891329391135900366594179 235336994086703850549891269)
    ·
      refine ⟨44125686391256971978104613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235336994086703850549891269 44125686391256971978104613)
      ·
        refine ⟨8273566198360682245894615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44125686391256971978104613 8273566198360682245894615)
        ·
          refine ⟨12410349297541023368841923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8273566198360682245894615 12410349297541023368841923)
          ·
            refine ⟨18615523946311535053262885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410349297541023368841923 18615523946311535053262885)
            ·
              refine ⟨3490410739933412822486791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18615523946311535053262885 3490410739933412822486791)
              ·
                refine ⟨5235616109900119233730187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490410739933412822486791 5235616109900119233730187)
                ·
                  refine ⟨7853424164850178850595281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5235616109900119233730187 7853424164850178850595281)
                  ·
                    refine ⟨5890068123637634137946461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7853424164850178850595281 5890068123637634137946461)
                    ·
                      refine ⟨2208775546364112801729923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890068123637634137946461 2208775546364112801729923)
                      ·
                        rfl

theorem cell23_4301575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4301575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301575 prefixEnd_4301575 := by exact prefixLift 4301575
  have htrace : WordTrace (prefixWord ++ tailWord_4301575) baseStart_4301575 baseEnd_4301575 := by
    simpa [prefixWord, tailWord_4301575, baseEnd_4301575] using wordTrace_append hprefix tailTrace_4301575
  have hstable : (prefixWord ++ tailWord_4301575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301575).length < 2 ^ (prefixWord ++ tailWord_4301575).sum := by decide
  have hdescent : baseEnd_4301575 < baseStart_4301575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301605 : List Nat := [1, 3, 1, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_4301605 : Nat := 118140960795 + 4301605 * 2 ^ 59
def prefixEnd_4301605 : Nat := 4983230072969 + 3 ^ 40 * 4301605 * 2
def baseEnd_4301605 : Nat := 2208790950783747684354785

theorem tailTrace_4301605 : CollatzResearch.WordTrace tailWord_4301605 prefixEnd_4301605 2208790950783747684354785 := by
  unfold tailWord_4301605
  simp only [CollatzResearch.WordTrace]
  refine ⟨156892423581027215490186269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104594949054018143660124179 156892423581027215490186269)
  ·
    refine ⟨58834658842885205808819851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156892423581027215490186269 58834658842885205808819851)
    ·
      refine ⟨88251988264327808713229777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58834658842885205808819851 88251988264327808713229777)
      ·
        refine ⟨66188991198245856534922333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88251988264327808713229777 66188991198245856534922333)
        ·
          refine ⟨24820871699342196200595875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66188991198245856534922333 24820871699342196200595875)
          ·
            refine ⟨37231307549013294300893813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24820871699342196200595875 37231307549013294300893813)
            ·
              refine ⟨3490435082719996340708795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37231307549013294300893813 3490435082719996340708795)
              ·
                refine ⟨5235652624079994511063193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490435082719996340708795 5235652624079994511063193)
                ·
                  refine ⟨3926739468059995883297395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5235652624079994511063193 3926739468059995883297395)
                  ·
                    refine ⟨5890109202089993824946093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3926739468059995883297395 5890109202089993824946093)
                    ·
                      refine ⟨2208790950783747684354785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890109202089993824946093 2208790950783747684354785)
                      ·
                        rfl

theorem cell23_4301605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_4301605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301605 prefixEnd_4301605 := by exact prefixLift 4301605
  have htrace : WordTrace (prefixWord ++ tailWord_4301605) baseStart_4301605 baseEnd_4301605 := by
    simpa [prefixWord, tailWord_4301605, baseEnd_4301605] using wordTrace_append hprefix tailTrace_4301605
  have hstable : (prefixWord ++ tailWord_4301605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301605).length < 2 ^ (prefixWord ++ tailWord_4301605).sum := by decide
  have hdescent : baseEnd_4301605 < baseStart_4301605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301631 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5]
def baseStart_4301631 : Nat := 118140960795 + 4301631 * 2 ^ 59
def prefixEnd_4301631 : Nat := 4983230072969 + 3 ^ 40 * 4301631 * 2
def baseEnd_4301631 : Nat := 2208804301280764582629665

theorem tailTrace_4301631 : CollatzResearch.WordTrace tailWord_4301631 prefixEnd_4301631 2208804301280764582629665 := by
  unfold tailWord_4301631
  simp only [CollatzResearch.WordTrace]
  refine ⟨156893371878933021930632747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104595581252622014620421831 156893371878933021930632747)
  ·
    refine ⟨235340057818399532895949121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156893371878933021930632747 235340057818399532895949121)
    ·
      refine ⟨176505043363799649671961841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235340057818399532895949121 176505043363799649671961841)
      ·
        refine ⟨132378782522849737253971381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176505043363799649671961841 132378782522849737253971381)
        ·
          refine ⟨12410510861517162867559817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132378782522849737253971381 12410510861517162867559817)
          ·
            refine ⟨9307883146137872150669863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12410510861517162867559817 9307883146137872150669863)
            ·
              refine ⟨13961824719206808226004795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9307883146137872150669863 13961824719206808226004795)
              ·
                refine ⟨20942737078810212339007193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13961824719206808226004795 20942737078810212339007193)
                ·
                  refine ⟨15707052809107659254255395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20942737078810212339007193 15707052809107659254255395)
                  ·
                    refine ⟨23560579213661488881383093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15707052809107659254255395 23560579213661488881383093)
                    ·
                      refine ⟨2208804301280764582629665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23560579213661488881383093 2208804301280764582629665)
                      ·
                        rfl

theorem cell23_4301631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_4301631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301631 prefixEnd_4301631 := by exact prefixLift 4301631
  have htrace : WordTrace (prefixWord ++ tailWord_4301631) baseStart_4301631 baseEnd_4301631 := by
    simpa [prefixWord, tailWord_4301631, baseEnd_4301631] using wordTrace_append hprefix tailTrace_4301631
  have hstable : (prefixWord ++ tailWord_4301631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301631).length < 2 ^ (prefixWord ++ tailWord_4301631).sum := by decide
  have hdescent : baseEnd_4301631 < baseStart_4301631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301651 : List Nat := [1, 1, 1, 2, 1, 1, 3, 8, 5]
def baseStart_4301651 : Nat := 118140960795 + 4301651 * 2 ^ 59
def prefixEnd_4301651 : Nat := 4983230072969 + 3 ^ 40 * 4301651 * 2
def baseEnd_4301651 : Nat := 245423841210428278264397

theorem tailTrace_4301651 : CollatzResearch.WordTrace tailWord_4301651 prefixEnd_4301651 245423841210428278264397 := by
  unfold tailWord_4301651
  simp only [CollatzResearch.WordTrace]
  refine ⟨156894101338860565346360807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104596067559240376897573871 156894101338860565346360807)
  ·
    refine ⟨235341152008290848019541211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156894101338860565346360807 235341152008290848019541211)
    ·
      refine ⟨353011728012436272029311817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235341152008290848019541211 353011728012436272029311817)
      ·
        refine ⟨264758796009327204021983863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353011728012436272029311817 264758796009327204021983863)
        ·
          refine ⟨397138194013990806032975795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264758796009327204021983863 397138194013990806032975795)
          ·
            refine ⟨595707291020986209049463693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397138194013990806032975795 595707291020986209049463693)
            ·
              refine ⟨223390234132869828393548885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 595707291020986209049463693 223390234132869828393548885)
              ·
                refine ⟨2617854306244568301486901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 223390234132869828393548885 2617854306244568301486901)
                ·
                  refine ⟨245423841210428278264397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2617854306244568301486901 245423841210428278264397)
                  ·
                    rfl

theorem cell23_4301651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 5].length) (baseStart_4301651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301651 prefixEnd_4301651 := by exact prefixLift 4301651
  have htrace : WordTrace (prefixWord ++ tailWord_4301651) baseStart_4301651 baseEnd_4301651 := by
    simpa [prefixWord, tailWord_4301651, baseEnd_4301651] using wordTrace_append hprefix tailTrace_4301651
  have hstable : (prefixWord ++ tailWord_4301651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301651).length < 2 ^ (prefixWord ++ tailWord_4301651).sum := by decide
  have hdescent : baseEnd_4301651 < baseStart_4301651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301681 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_4301681 : Nat := 118140960795 + 4301681 * 2 ^ 59
def prefixEnd_4301681 : Nat := 4983230072969 + 3 ^ 40 * 4301681 * 2
def baseEnd_4301681 : Nat := 736276658437829795668145

theorem tailTrace_4301681 : CollatzResearch.WordTrace tailWord_4301681 prefixEnd_4301681 736276658437829795668145 := by
  unfold tailWord_4301681
  simp only [CollatzResearch.WordTrace]
  refine ⟨156895195528751880469952897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104596797019167920313301931 156895195528751880469952897)
  ·
    refine ⟨117671396646563910352464673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156895195528751880469952897 117671396646563910352464673)
    ·
      refine ⟨88253547484922932764348505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117671396646563910352464673 88253547484922932764348505)
      ·
        refine ⟨66190160613692199573261379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88253547484922932764348505 66190160613692199573261379)
        ·
          refine ⟨99285240920538299359892069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66190160613692199573261379 99285240920538299359892069)
          ·
            refine ⟨18615982672600931129979763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99285240920538299359892069 18615982672600931129979763)
            ·
              refine ⟨27923974008901396694969645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18615982672600931129979763 27923974008901396694969645)
              ·
                refine ⟨10471490253338023760613617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27923974008901396694969645 10471490253338023760613617)
                ·
                  refine ⟨7853617690003517820460213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10471490253338023760613617 7853617690003517820460213)
                  ·
                    refine ⟨736276658437829795668145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7853617690003517820460213 736276658437829795668145)
                    ·
                      rfl

theorem cell23_4301681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_4301681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301681 prefixEnd_4301681 := by exact prefixLift 4301681
  have htrace : WordTrace (prefixWord ++ tailWord_4301681) baseStart_4301681 baseEnd_4301681 := by
    simpa [prefixWord, tailWord_4301681, baseEnd_4301681] using wordTrace_append hprefix tailTrace_4301681
  have hstable : (prefixWord ++ tailWord_4301681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301681).length < 2 ^ (prefixWord ++ tailWord_4301681).sum := by decide
  have hdescent : baseEnd_4301681 < baseStart_4301681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301721 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_4301721 : Nat := 118140960795 + 4301721 * 2 ^ 59
def prefixEnd_4301721 : Nat := 4983230072969 + 3 ^ 40 * 4301721 * 2
def baseEnd_4301721 : Nat := 2208850514539669230504251

theorem tailTrace_4301721 : CollatzResearch.WordTrace tailWord_4301721 prefixEnd_4301721 2208850514539669230504251 := by
  unfold tailWord_4301721
  simp only [CollatzResearch.WordTrace]
  refine ⟨156896654448606967301409017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104597769632404644867606011 156896654448606967301409017)
  ·
    refine ⟨117672490836455225476056763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156896654448606967301409017 117672490836455225476056763)
    ·
      refine ⟨176508736254682838214085145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117672490836455225476056763 176508736254682838214085145)
      ·
        refine ⟨132381552191012128660563859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176508736254682838214085145 132381552191012128660563859)
        ·
          refine ⟨198572328286518192990845789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132381552191012128660563859 198572328286518192990845789)
          ·
            refine ⟨74464623107444322371567171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198572328286518192990845789 74464623107444322371567171)
            ·
              refine ⟨111696934661166483557350757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74464623107444322371567171 111696934661166483557350757)
              ·
                refine ⟨20943175248968715667003267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111696934661166483557350757 20943175248968715667003267)
                ·
                  refine ⟨31414762873453073500504901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20943175248968715667003267 31414762873453073500504901)
                  ·
                    refine ⟨5890268038772451281344669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31414762873453073500504901 5890268038772451281344669)
                    ·
                      refine ⟨2208850514539669230504251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890268038772451281344669 2208850514539669230504251)
                      ·
                        rfl

theorem cell23_4301721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_4301721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301721 prefixEnd_4301721 := by exact prefixLift 4301721
  have htrace : WordTrace (prefixWord ++ tailWord_4301721) baseStart_4301721 baseEnd_4301721 := by
    simpa [prefixWord, tailWord_4301721, baseEnd_4301721] using wordTrace_append hprefix tailTrace_4301721
  have hstable : (prefixWord ++ tailWord_4301721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301721).length < 2 ^ (prefixWord ++ tailWord_4301721).sum := by decide
  have hdescent : baseEnd_4301721 < baseStart_4301721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301785 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 3]
def baseStart_4301785 : Nat := 118140960795 + 4301785 * 2 ^ 59
def prefixEnd_4301785 : Nat := 4983230072969 + 3 ^ 40 * 4301785 * 2
def baseEnd_4301785 : Nat := 2208883377301556980103957

theorem tailTrace_4301785 : CollatzResearch.WordTrace tailWord_4301785 prefixEnd_4301785 2208883377301556980103957 := by
  unfold tailWord_4301785
  simp only [CollatzResearch.WordTrace]
  refine ⟨156898988720375106231738809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104599325813583404154492539 156898988720375106231738809)
  ·
    refine ⟨117674241540281329673804107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156898988720375106231738809 117674241540281329673804107)
    ·
      refine ⟨176511362310421994510706161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117674241540281329673804107 176511362310421994510706161)
      ·
        refine ⟨132383521732816495883029621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176511362310421994510706161 132383521732816495883029621)
        ·
          refine ⟨12410955162451546489034027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132383521732816495883029621 12410955162451546489034027)
          ·
            refine ⟨18616432743677319733551041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12410955162451546489034027 18616432743677319733551041)
            ·
              refine ⟨13962324557757989800163281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18616432743677319733551041 13962324557757989800163281)
              ·
                refine ⟨10471743418318492350122461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13962324557757989800163281 10471743418318492350122461)
                ·
                  refine ⟨3926903781869434631295923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10471743418318492350122461 3926903781869434631295923)
                  ·
                    refine ⟨5890355672804151946943885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3926903781869434631295923 5890355672804151946943885)
                    ·
                      refine ⟨2208883377301556980103957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890355672804151946943885 2208883377301556980103957)
                      ·
                        rfl

theorem cell23_4301785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_4301785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301785 prefixEnd_4301785 := by exact prefixLift 4301785
  have htrace : WordTrace (prefixWord ++ tailWord_4301785) baseStart_4301785 baseEnd_4301785 := by
    simpa [prefixWord, tailWord_4301785, baseEnd_4301785] using wordTrace_append hprefix tailTrace_4301785
  have hstable : (prefixWord ++ tailWord_4301785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301785).length < 2 ^ (prefixWord ++ tailWord_4301785).sum := by decide
  have hdescent : baseEnd_4301785 < baseStart_4301785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301795 : List Nat := [1, 1, 1, 6, 1, 1, 2, 3, 2, 3, 2]
def baseStart_4301795 : Nat := 118140960795 + 4301795 * 2 ^ 59
def prefixEnd_4301795 : Nat := 4983230072969 + 3 ^ 40 * 4301795 * 2
def baseEnd_4301795 : Nat := 2208888512108101940978911

theorem tailTrace_4301795 : CollatzResearch.WordTrace tailWord_4301795 prefixEnd_4301795 2208888512108101940978911 := by
  unfold tailWord_4301795
  simp only [CollatzResearch.WordTrace]
  refine ⟨156899353450338877939602839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104599568966892585293068559 156899353450338877939602839)
  ·
    refine ⟨235349030175508316909404259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156899353450338877939602839 235349030175508316909404259)
    ·
      refine ⟨353023545263262475364106389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235349030175508316909404259 353023545263262475364106389)
      ·
        refine ⟨16547978684215428532692487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 353023545263262475364106389 16547978684215428532692487)
        ·
          refine ⟨24821968026323142799038731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16547978684215428532692487 24821968026323142799038731)
          ·
            refine ⟨37232952039484714198558097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24821968026323142799038731 37232952039484714198558097)
            ·
              refine ⟨27924714029613535648918573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37232952039484714198558097 27924714029613535648918573)
              ·
                refine ⟨10471767761105075868344465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27924714029613535648918573 10471767761105075868344465)
                ·
                  refine ⟨7853825820828806901258349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10471767761105075868344465 7853825820828806901258349)
                  ·
                    refine ⟨2945184682810802587971881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7853825820828806901258349 2945184682810802587971881)
                    ·
                      refine ⟨2208888512108101940978911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945184682810802587971881 2208888512108101940978911)
                      ·
                        rfl

theorem cell23_4301795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_4301795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301795 prefixEnd_4301795 := by exact prefixLift 4301795
  have htrace : WordTrace (prefixWord ++ tailWord_4301795) baseStart_4301795 baseEnd_4301795 := by
    simpa [prefixWord, tailWord_4301795, baseEnd_4301795] using wordTrace_append hprefix tailTrace_4301795
  have hstable : (prefixWord ++ tailWord_4301795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301795).length < 2 ^ (prefixWord ++ tailWord_4301795).sum := by decide
  have hdescent : baseEnd_4301795 < baseStart_4301795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301826 : List Nat := [3, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_4301826 : Nat := 118140960795 + 4301826 * 2 ^ 59
def prefixEnd_4301826 : Nat := 4983230072969 + 3 ^ 40 * 4301826 * 2
def baseEnd_4301826 : Nat := 245433825556487924410141

theorem tailTrace_4301826 : CollatzResearch.WordTrace tailWord_4301826 prefixEnd_4301826 245433825556487924410141 := by
  unfold tailWord_4301826
  simp only [CollatzResearch.WordTrace]
  refine ⟨39225121028306642558495333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104600322742151046822654221 39225121028306642558495333)
  ·
    refine ⟨7354710192807495479717875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39225121028306642558495333 7354710192807495479717875)
    ·
      refine ⟨11032065289211243219576813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7354710192807495479717875 11032065289211243219576813)
      ·
        refine ⟨4137024483454216207341305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11032065289211243219576813 4137024483454216207341305)
        ·
          refine ⟨3102768362590662155505979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4137024483454216207341305 3102768362590662155505979)
          ·
            refine ⟨4654152543885993233258969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102768362590662155505979 4654152543885993233258969)
            ·
              refine ⟨3490614407914494924944227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4654152543885993233258969 3490614407914494924944227)
              ·
                refine ⟨5235921611871742387416341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3490614407914494924944227 5235921611871742387416341)
                ·
                  refine ⟨245433825556487924410141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5235921611871742387416341 245433825556487924410141)
                  ·
                    rfl

theorem cell23_4301826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_4301826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301826 prefixEnd_4301826 := by exact prefixLift 4301826
  have htrace : WordTrace (prefixWord ++ tailWord_4301826) baseStart_4301826 baseEnd_4301826 := by
    simpa [prefixWord, tailWord_4301826, baseEnd_4301826] using wordTrace_append hprefix tailTrace_4301826
  have hstable : (prefixWord ++ tailWord_4301826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301826).length < 2 ^ (prefixWord ++ tailWord_4301826).sum := by decide
  have hdescent : baseEnd_4301826 < baseStart_4301826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301835 : List Nat := [1, 1, 1, 1, 6, 3, 1, 3, 2, 4]
def baseStart_4301835 : Nat := 118140960795 + 4301835 * 2 ^ 59
def prefixEnd_4301835 : Nat := 4983230072969 + 3 ^ 40 * 4301835 * 2
def baseEnd_4301835 : Nat := 736303017111427261492909

theorem tailTrace_4301835 : CollatzResearch.WordTrace tailWord_4301835 prefixEnd_4301835 736303017111427261492909 := by
  unfold tailWord_4301835
  simp only [CollatzResearch.WordTrace]
  refine ⟨156900812370193964771058959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104600541580129309847372639 156900812370193964771058959)
  ·
    refine ⟨235351218555290947156588439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156900812370193964771058959 235351218555290947156588439)
    ·
      refine ⟨353026827832936420734882659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235351218555290947156588439 353026827832936420734882659)
      ·
        refine ⟨529540241749404631102323989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353026827832936420734882659 529540241749404631102323989)
        ·
          refine ⟨24822198832003342082921437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 529540241749404631102323989 24822198832003342082921437)
          ·
            refine ⟨9308324562001253281095539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24822198832003342082921437 9308324562001253281095539)
            ·
              refine ⟨13962486843001879921643309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308324562001253281095539 13962486843001879921643309)
              ·
                refine ⟨5235932566125704970616241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13962486843001879921643309 5235932566125704970616241)
                ·
                  refine ⟨3926949424594278727962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5235932566125704970616241 3926949424594278727962181)
                  ·
                    refine ⟨736303017111427261492909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3926949424594278727962181 736303017111427261492909)
                    ·
                      rfl

theorem cell23_4301835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2, 4].length) (baseStart_4301835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301835 prefixEnd_4301835 := by exact prefixLift 4301835
  have htrace : WordTrace (prefixWord ++ tailWord_4301835) baseStart_4301835 baseEnd_4301835 := by
    simpa [prefixWord, tailWord_4301835, baseEnd_4301835] using wordTrace_append hprefix tailTrace_4301835
  have hstable : (prefixWord ++ tailWord_4301835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301835).length < 2 ^ (prefixWord ++ tailWord_4301835).sum := by decide
  have hdescent : baseEnd_4301835 < baseStart_4301835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301838 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4301838 : Nat := 118140960795 + 4301838 * 2 ^ 59
def prefixEnd_4301838 : Nat := 4983230072969 + 3 ^ 40 * 4301838 * 2
def baseEnd_4301838 : Nat := 2208910591776245272741213

theorem tailTrace_4301838 : CollatzResearch.WordTrace tailWord_4301838 prefixEnd_4301838 2208910591776245272741213 := by
  unfold tailWord_4301838
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612615223647887035427271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104600614526122064188945445 19612615223647887035427271)
  ·
    refine ⟨29418922835471830553140907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19612615223647887035427271 29418922835471830553140907)
    ·
      refine ⟨44128384253207745829711361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29418922835471830553140907 44128384253207745829711361)
      ·
        refine ⟨33096288189905809372283521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44128384253207745829711361 33096288189905809372283521)
        ·
          refine ⟨24822216142429357029212641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33096288189905809372283521 24822216142429357029212641)
          ·
            refine ⟨18616662106822017771909481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24822216142429357029212641 18616662106822017771909481)
            ·
              refine ⟨13962496580116513328932111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18616662106822017771909481 13962496580116513328932111)
              ·
                refine ⟨20943744870174769993398167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13962496580116513328932111 20943744870174769993398167)
                ·
                  refine ⟨31415617305262154990097251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20943744870174769993398167 31415617305262154990097251)
                  ·
                    refine ⟨47123425957893232485145877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31415617305262154990097251 47123425957893232485145877)
                    ·
                      refine ⟨2208910591776245272741213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47123425957893232485145877 2208910591776245272741213)
                      ·
                        rfl

theorem cell23_4301838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4301838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301838 prefixEnd_4301838 := by exact prefixLift 4301838
  have htrace : WordTrace (prefixWord ++ tailWord_4301838) baseStart_4301838 baseEnd_4301838 := by
    simpa [prefixWord, tailWord_4301838, baseEnd_4301838] using wordTrace_append hprefix tailTrace_4301838
  have hstable : (prefixWord ++ tailWord_4301838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301838).length < 2 ^ (prefixWord ++ tailWord_4301838).sum := by decide
  have hdescent : baseEnd_4301838 < baseStart_4301838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301845 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_4301845 : Nat := 118140960795 + 4301845 * 2 ^ 59
def prefixEnd_4301845 : Nat := 4983230072969 + 3 ^ 40 * 4301845 * 2
def baseEnd_4301845 : Nat := 2208914186140826745353681

theorem tailTrace_4301845 : CollatzResearch.WordTrace tailWord_4301845 prefixEnd_4301845 2208914186140826745353681 := by
  unfold tailWord_4301845
  simp only [CollatzResearch.WordTrace]
  refine ⟨156901177100157736478922989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104600784733438490985948659 156901177100157736478922989)
  ·
    refine ⟨58837941412559151179596121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156901177100157736478922989 58837941412559151179596121)
    ·
      refine ⟨44128456059419363384697091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58837941412559151179596121 44128456059419363384697091)
      ·
        refine ⟨66192684089129045077045637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44128456059419363384697091 66192684089129045077045637)
        ·
          refine ⟨12411128266711695951946057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66192684089129045077045637 12411128266711695951946057)
          ·
            refine ⟨9308346200033771963959543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12411128266711695951946057 9308346200033771963959543)
            ·
              refine ⟨13962519300050657945939315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308346200033771963959543 13962519300050657945939315)
              ·
                refine ⟨20943778950075986918908973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13962519300050657945939315 20943778950075986918908973)
                ·
                  refine ⟨7853917106278495094590865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20943778950075986918908973 7853917106278495094590865)
                  ·
                    refine ⟨5890437829708871320943149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7853917106278495094590865 5890437829708871320943149)
                    ·
                      refine ⟨2208914186140826745353681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890437829708871320943149 2208914186140826745353681)
                      ·
                        rfl

theorem cell23_4301845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_4301845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301845 prefixEnd_4301845 := by exact prefixLift 4301845
  have htrace : WordTrace (prefixWord ++ tailWord_4301845) baseStart_4301845 baseEnd_4301845 := by
    simpa [prefixWord, tailWord_4301845, baseEnd_4301845] using wordTrace_append hprefix tailTrace_4301845
  have hstable : (prefixWord ++ tailWord_4301845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301845).length < 2 ^ (prefixWord ++ tailWord_4301845).sum := by decide
  have hdescent : baseEnd_4301845 < baseStart_4301845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301871 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5]
def baseStart_4301871 : Nat := 118140960795 + 4301871 * 2 ^ 59
def prefixEnd_4301871 : Nat := 4983230072969 + 3 ^ 40 * 4301871 * 2
def baseEnd_4301871 : Nat := 2208927536637843643628561

theorem tailTrace_4301871 : CollatzResearch.WordTrace tailWord_4301871 prefixEnd_4301871 2208927536637843643628561 := by
  unfold tailWord_4301871
  simp only [CollatzResearch.WordTrace]
  refine ⟨156902125398063542919369467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104601416932042361946246311 156902125398063542919369467)
  ·
    refine ⟨235353188097095314379054201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156902125398063542919369467 235353188097095314379054201)
    ·
      refine ⟨176514891072821485784290651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235353188097095314379054201 176514891072821485784290651)
      ·
        refine ⟨264772336609232228676435977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176514891072821485784290651 264772336609232228676435977)
        ·
          refine ⟨198579252456924171507326983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264772336609232228676435977 198579252456924171507326983)
          ·
            refine ⟨297868878685386257260990475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198579252456924171507326983 297868878685386257260990475)
            ·
              refine ⟨446803318028079385891485713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297868878685386257260990475 446803318028079385891485713)
              ·
                refine ⟨335102488521059539418614285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446803318028079385891485713 335102488521059539418614285)
                ·
                  refine ⟨125663433195397327281980357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335102488521059539418614285 125663433195397327281980357)
                  ·
                    refine ⟨23561893724136998865371317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125663433195397327281980357 23561893724136998865371317)
                    ·
                      refine ⟨2208927536637843643628561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23561893724136998865371317 2208927536637843643628561)
                      ·
                        rfl

theorem cell23_4301871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 5].length) (baseStart_4301871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301871 prefixEnd_4301871 := by exact prefixLift 4301871
  have htrace : WordTrace (prefixWord ++ tailWord_4301871) baseStart_4301871 baseEnd_4301871 := by
    simpa [prefixWord, tailWord_4301871, baseEnd_4301871] using wordTrace_append hprefix tailTrace_4301871
  have hstable : (prefixWord ++ tailWord_4301871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301871).length < 2 ^ (prefixWord ++ tailWord_4301871).sum := by decide
  have hdescent : baseEnd_4301871 < baseStart_4301871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301902 : List Nat := [4, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_4301902 : Nat := 118140960795 + 4301902 * 2 ^ 59
def prefixEnd_4301902 : Nat := 4983230072969 + 3 ^ 40 * 4301902 * 2
def baseEnd_4301902 : Nat := 2208943454538133022340919

theorem tailTrace_4301902 : CollatzResearch.WordTrace tailWord_4301902 prefixEnd_4301902 2208943454538133022340919 := by
  unfold tailWord_4301902
  simp only [CollatzResearch.WordTrace]
  refine ⟨19612907007618904401718495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104602170707300823475831973 19612907007618904401718495)
  ·
    refine ⟨29419360511428356602577743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19612907007618904401718495 29419360511428356602577743)
    ·
      refine ⟨44129040767142534903866615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29419360511428356602577743 44129040767142534903866615)
      ·
        refine ⟨66193561150713802355799923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44129040767142534903866615 66193561150713802355799923)
        ·
          refine ⟨99290341726070703533699885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66193561150713802355799923 99290341726070703533699885)
          ·
            refine ⟨37233878147276513825137457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99290341726070703533699885 37233878147276513825137457)
            ·
              refine ⟨27925408610457385368853093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37233878147276513825137457 27925408610457385368853093)
              ·
                refine ⟨5236014114460759756659955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27925408610457385368853093 5236014114460759756659955)
                ·
                  refine ⟨7854021171691139634989933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5236014114460759756659955 7854021171691139634989933)
                  ·
                    refine ⟨2945257939384177363121225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7854021171691139634989933 2945257939384177363121225)
                    ·
                      refine ⟨2208943454538133022340919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945257939384177363121225 2208943454538133022340919)
                      ·
                        rfl

theorem cell23_4301902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_4301902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301902 prefixEnd_4301902 := by exact prefixLift 4301902
  have htrace : WordTrace (prefixWord ++ tailWord_4301902) baseStart_4301902 baseEnd_4301902 := by
    simpa [prefixWord, tailWord_4301902, baseEnd_4301902] using wordTrace_append hprefix tailTrace_4301902
  have hstable : (prefixWord ++ tailWord_4301902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301902).length < 2 ^ (prefixWord ++ tailWord_4301902).sum := by decide
  have hdescent : baseEnd_4301902 < baseStart_4301902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301910 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4301910 : Nat := 118140960795 + 4301910 * 2 ^ 59
def prefixEnd_4301910 : Nat := 4983230072969 + 3 ^ 40 * 4301910 * 2
def baseEnd_4301910 : Nat := 2208947562383368991040883

theorem tailTrace_4301910 : CollatzResearch.WordTrace tailWord_4301910 prefixEnd_4301910 2208947562383368991040883 := by
  unfold tailWord_4301910
  simp only [CollatzResearch.WordTrace]
  refine ⟨9806471740307640786252449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104602365229948168386692789 9806471740307640786252449)
  ·
    refine ⟨7354853805230730589689337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9806471740307640786252449 7354853805230730589689337)
    ·
      refine ⟨5516140353923047942267003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7354853805230730589689337 5516140353923047942267003)
      ·
        refine ⟨8274210530884571913400505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5516140353923047942267003 8274210530884571913400505)
        ·
          refine ⟨6205657898163428935050379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8274210530884571913400505 6205657898163428935050379)
          ·
            refine ⟨9308486847245143402575569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6205657898163428935050379 9308486847245143402575569)
            ·
              refine ⟨6981365135433857551931677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9308486847245143402575569 6981365135433857551931677)
              ·
                refine ⟨2618011925787696581974379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6981365135433857551931677 2618011925787696581974379)
                ·
                  refine ⟨3927017888681544872961569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618011925787696581974379 3927017888681544872961569)
                  ·
                    refine ⟨2945263416511158654721177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927017888681544872961569 2945263416511158654721177)
                    ·
                      refine ⟨2208947562383368991040883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945263416511158654721177 2208947562383368991040883)
                      ·
                        rfl

theorem cell23_4301910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4301910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301910 prefixEnd_4301910 := by exact prefixLift 4301910
  have htrace : WordTrace (prefixWord ++ tailWord_4301910) baseStart_4301910 baseEnd_4301910 := by
    simpa [prefixWord, tailWord_4301910, baseEnd_4301910] using wordTrace_append hprefix tailTrace_4301910
  have hstable : (prefixWord ++ tailWord_4301910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301910).length < 2 ^ (prefixWord ++ tailWord_4301910).sum := by decide
  have hdescent : baseEnd_4301910 < baseStart_4301910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301932 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_4301932 : Nat := 118140960795 + 4301932 * 2 ^ 59
def prefixEnd_4301932 : Nat := 4983230072969 + 3 ^ 40 * 4301932 * 2
def baseEnd_4301932 : Nat := 2208958858957767904965781

theorem tailTrace_4301932 : CollatzResearch.WordTrace tailWord_4301932 prefixEnd_4301932 2208958858957767904965781 := by
  unfold tailWord_4301932
  simp only [CollatzResearch.WordTrace]
  refine ⟨78452175125421275168670025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104602900167228366891560033 78452175125421275168670025)
  ·
    refine ⟨58839131344065956376502519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78452175125421275168670025 58839131344065956376502519)
    ·
      refine ⟨88258697016098934564753779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58839131344065956376502519 88258697016098934564753779)
      ·
        refine ⟨132388045524148401847130669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88258697016098934564753779 132388045524148401847130669)
        ·
          refine ⟨49645517071555650692674001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132388045524148401847130669 49645517071555650692674001)
          ·
            refine ⟨37234137803666738019505501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49645517071555650692674001 37234137803666738019505501)
            ·
              refine ⟨13962801676375026757314563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37234137803666738019505501 13962801676375026757314563)
              ·
                refine ⟨20944202514562540135971845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13962801676375026757314563 20944202514562540135971845)
                ·
                  refine ⟨3927037971480476275494721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20944202514562540135971845 3927037971480476275494721)
                  ·
                    refine ⟨2945278478610357206621041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927037971480476275494721 2945278478610357206621041)
                    ·
                      refine ⟨2208958858957767904965781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945278478610357206621041 2208958858957767904965781)
                      ·
                        rfl

theorem cell23_4301932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_4301932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301932 prefixEnd_4301932 := by exact prefixLift 4301932
  have htrace : WordTrace (prefixWord ++ tailWord_4301932) baseStart_4301932 baseEnd_4301932 := by
    simpa [prefixWord, tailWord_4301932, baseEnd_4301932] using wordTrace_append hprefix tailTrace_4301932
  have hstable : (prefixWord ++ tailWord_4301932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301932).length < 2 ^ (prefixWord ++ tailWord_4301932).sum := by decide
  have hdescent : baseEnd_4301932 < baseStart_4301932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4301985 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_4301985 : Nat := 118140960795 + 4301985 * 2 ^ 59
def prefixEnd_4301985 : Nat := 4983230072969 + 3 ^ 40 * 4301985 * 2
def baseEnd_4301985 : Nat := 736328691144152065867679

theorem tailTrace_4301985 : CollatzResearch.WordTrace tailWord_4301985 prefixEnd_4301985 736328691144152065867679 := by
  unfold tailWord_4301985
  simp only [CollatzResearch.WordTrace]
  refine ⟨156906283319650540389019409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104604188879767026926012939 156906283319650540389019409)
  ·
    refine ⟨117679712489737905291764557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156906283319650540389019409 117679712489737905291764557)
    ·
      refine ⟨44129892183651714484411709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117679712489737905291764557 44129892183651714484411709)
      ·
        refine ⟨16548709568869392931654391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44129892183651714484411709 16548709568869392931654391)
        ·
          refine ⟨24823064353304089397481587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16548709568869392931654391 24823064353304089397481587)
          ·
            refine ⟨37234596529956134096222381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24823064353304089397481587 37234596529956134096222381)
            ·
              refine ⟨13962973698733550286083393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37234596529956134096222381 13962973698733550286083393)
              ·
                refine ⟨10472230274050162714562545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13962973698733550286083393 10472230274050162714562545)
                ·
                  refine ⟨7854172705537622035921909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10472230274050162714562545 7854172705537622035921909)
                  ·
                    refine ⟨736328691144152065867679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7854172705537622035921909 736328691144152065867679)
                    ·
                      rfl

theorem cell23_4301985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_4301985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4301985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4301985 prefixEnd_4301985 := by exact prefixLift 4301985
  have htrace : WordTrace (prefixWord ++ tailWord_4301985) baseStart_4301985 baseEnd_4301985 := by
    simpa [prefixWord, tailWord_4301985, baseEnd_4301985] using wordTrace_append hprefix tailTrace_4301985
  have hstable : (prefixWord ++ tailWord_4301985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4301985).length < 2 ^ (prefixWord ++ tailWord_4301985).sum := by decide
  have hdescent : baseEnd_4301985 < baseStart_4301985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4301985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302015 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 3, 4]
def baseStart_4302015 : Nat := 118140960795 + 4302015 * 2 ^ 59
def prefixEnd_4302015 : Nat := 4983230072969 + 3 ^ 40 * 4302015 * 2
def baseEnd_4302015 : Nat := 736333825950697026742633

theorem tailTrace_4302015 : CollatzResearch.WordTrace tailWord_4302015 prefixEnd_4302015 736333825950697026742633 := by
  unfold tailWord_4302015
  simp only [CollatzResearch.WordTrace]
  refine ⟨156907377509541855512611499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104604918339694570341740999 156907377509541855512611499)
  ·
    refine ⟨235361066264312783268917249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156907377509541855512611499 235361066264312783268917249)
    ·
      refine ⟨176520799698234587451687937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235361066264312783268917249 176520799698234587451687937)
      ·
        refine ⟨132390599773675940588765953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176520799698234587451687937 132390599773675940588765953)
        ·
          refine ⟨99292949830256955441574465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132390599773675940588765953 99292949830256955441574465)
          ·
            refine ⟨74469712372692716581180849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99292949830256955441574465 74469712372692716581180849)
            ·
              refine ⟨55852284279519537435885637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74469712372692716581180849 55852284279519537435885637)
              ·
                refine ⟨10472303302409913269228557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55852284279519537435885637 10472303302409913269228557)
                ·
                  refine ⟨3927113738403717475960709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10472303302409913269228557 3927113738403717475960709)
                  ·
                    refine ⟨736333825950697026742633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3927113738403717475960709 736333825950697026742633)
                    ·
                      rfl

theorem cell23_4302015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3, 4].length) (baseStart_4302015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302015 prefixEnd_4302015 := by exact prefixLift 4302015
  have htrace : WordTrace (prefixWord ++ tailWord_4302015) baseStart_4302015 baseEnd_4302015 := by
    simpa [prefixWord, tailWord_4302015, baseEnd_4302015] using wordTrace_append hprefix tailTrace_4302015
  have hstable : (prefixWord ++ tailWord_4302015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302015).length < 2 ^ (prefixWord ++ tailWord_4302015).sum := by decide
  have hdescent : baseEnd_4302015 < baseStart_4302015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302049 : List Nat := [1, 2, 3, 1, 3, 3, 1, 4, 1, 4]
def baseStart_4302049 : Nat := 118140960795 + 4302049 * 2 ^ 59
def prefixEnd_4302049 : Nat := 4983230072969 + 3 ^ 40 * 4302049 * 2
def baseEnd_4302049 : Nat := 736339645398114649067581

theorem tailTrace_4302049 : CollatzResearch.WordTrace tailWord_4302049 prefixEnd_4302049 736339645398114649067581 := by
  unfold tailWord_4302049
  simp only [CollatzResearch.WordTrace]
  refine ⟨156908617591418679319349201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104605745060945786212899467 156908617591418679319349201)
  ·
    refine ⟨117681463193564009489511901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156908617591418679319349201 117681463193564009489511901)
    ·
      refine ⟨44130548697586503558566963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117681463193564009489511901 44130548697586503558566963)
      ·
        refine ⟨66195823046379755337850445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44130548697586503558566963 66195823046379755337850445)
        ·
          refine ⟨24823433642392408251693917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66195823046379755337850445 24823433642392408251693917)
          ·
            refine ⟨9308787615897153094385219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24823433642392408251693917 9308787615897153094385219)
            ·
              refine ⟨13963181423845729641577829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308787615897153094385219 13963181423845729641577829)
              ·
                refine ⟨2618096516971074307795843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13963181423845729641577829 2618096516971074307795843)
                ·
                  refine ⟨3927144775456611461693765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618096516971074307795843 3927144775456611461693765)
                  ·
                    refine ⟨736339645398114649067581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3927144775456611461693765 736339645398114649067581)
                    ·
                      rfl

theorem cell23_4302049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_4302049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302049 prefixEnd_4302049 := by exact prefixLift 4302049
  have htrace : WordTrace (prefixWord ++ tailWord_4302049) baseStart_4302049 baseEnd_4302049 := by
    simpa [prefixWord, tailWord_4302049, baseEnd_4302049] using wordTrace_append hprefix tailTrace_4302049
  have hstable : (prefixWord ++ tailWord_4302049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302049).length < 2 ^ (prefixWord ++ tailWord_4302049).sum := by decide
  have hdescent : baseEnd_4302049 < baseStart_4302049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302076 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_4302076 : Nat := 118140960795 + 4302076 * 2 ^ 59
def prefixEnd_4302076 : Nat := 4983230072969 + 3 ^ 40 * 4302076 * 2
def baseEnd_4302076 : Nat := 2209032800172015341565119

theorem tailTrace_4302076 : CollatzResearch.WordTrace tailWord_4302076 prefixEnd_4302076 2209032800172015341565119 := by
  unfold tailWord_4302076
  simp only [CollatzResearch.WordTrace]
  refine ⟨78454801181160431465291041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104606401574880575287054721 78454801181160431465291041)
  ·
    refine ⟨58841100885870323598968281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78454801181160431465291041 58841100885870323598968281)
    ·
      refine ⟨44130825664402742699226211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58841100885870323598968281 44130825664402742699226211)
      ·
        refine ⟨66196238496604114048839317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44130825664402742699226211 66196238496604114048839317)
        ·
          refine ⟨3102948679528317846039343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66196238496604114048839317 3102948679528317846039343)
          ·
            refine ⟨4654423019292476769059015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3102948679528317846039343 4654423019292476769059015)
            ·
              refine ⟨6981634528938715153588523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4654423019292476769059015 6981634528938715153588523)
              ·
                refine ⟨10472451793408072730382785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6981634528938715153588523 10472451793408072730382785)
                ·
                  refine ⟨7854338845056054547787089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10472451793408072730382785 7854338845056054547787089)
                  ·
                    refine ⟨5890754133792040910840317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7854338845056054547787089 5890754133792040910840317)
                    ·
                      refine ⟨2209032800172015341565119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890754133792040910840317 2209032800172015341565119)
                      ·
                        rfl

theorem cell23_4302076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_4302076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302076 prefixEnd_4302076 := by exact prefixLift 4302076
  have htrace : WordTrace (prefixWord ++ tailWord_4302076) baseStart_4302076 baseEnd_4302076 := by
    simpa [prefixWord, tailWord_4302076, baseEnd_4302076] using wordTrace_append hprefix tailTrace_4302076
  have hstable : (prefixWord ++ tailWord_4302076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302076).length < 2 ^ (prefixWord ++ tailWord_4302076).sum := by decide
  have hdescent : baseEnd_4302076 < baseStart_4302076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302092 : List Nat := [2, 2, 1, 2, 2, 4, 1, 3, 1, 5]
def baseStart_4302092 : Nat := 118140960795 + 4302092 * 2 ^ 59
def prefixEnd_4302092 : Nat := 4983230072969 + 3 ^ 40 * 4302092 * 2
def baseEnd_4302092 : Nat := 736347005287495759655015

theorem tailTrace_4302092 : CollatzResearch.WordTrace tailWord_4302092 prefixEnd_4302092 736347005287495759655015 := by
  unfold tailWord_4302092
  simp only [CollatzResearch.WordTrace]
  refine ⟨78455092965131448831582265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104606790620175265108776353 78455092965131448831582265)
  ·
    refine ⟨58841319723848586623686699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78455092965131448831582265 58841319723848586623686699)
    ·
      refine ⟨88261979585772879935530049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58841319723848586623686699 88261979585772879935530049)
      ·
        refine ⟨66196484689329659951647537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88261979585772879935530049 66196484689329659951647537)
        ·
          refine ⟨49647363516997244963735653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66196484689329659951647537 49647363516997244963735653)
          ·
            refine ⟨9308880659436983430700435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49647363516997244963735653 9308880659436983430700435)
            ·
              refine ⟨13963320989155475146050653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9308880659436983430700435 13963320989155475146050653)
              ·
                refine ⟨5236245370933303179768995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13963320989155475146050653 5236245370933303179768995)
                ·
                  refine ⟨7854368056399954769653493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5236245370933303179768995 7854368056399954769653493)
                  ·
                    refine ⟨736347005287495759655015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7854368056399954769653493 736347005287495759655015)
                    ·
                      rfl

theorem cell23_4302092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_4302092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302092 prefixEnd_4302092 := by exact prefixLift 4302092
  have htrace : WordTrace (prefixWord ++ tailWord_4302092) baseStart_4302092 baseEnd_4302092 := by
    simpa [prefixWord, tailWord_4302092, baseEnd_4302092] using wordTrace_append hprefix tailTrace_4302092
  have hstable : (prefixWord ++ tailWord_4302092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302092).length < 2 ^ (prefixWord ++ tailWord_4302092).sum := by decide
  have hdescent : baseEnd_4302092 < baseStart_4302092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302106 : List Nat := [3, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3]
def baseStart_4302106 : Nat := 118140960795 + 4302106 * 2 ^ 59
def prefixEnd_4302106 : Nat := 4983230072969 + 3 ^ 40 * 4302106 * 2
def baseEnd_4302106 : Nat := 2209048204591650224189981

theorem tailTrace_4302106 : CollatzResearch.WordTrace tailWord_4302106 prefixEnd_4302106 2209048204591650224189981 := by
  unfold tailWord_4302106
  simp only [CollatzResearch.WordTrace]
  refine ⟨39227674138053044513543543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104607131034808118702782781 39227674138053044513543543)
  ·
    refine ⟨58841511207079566770315315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39227674138053044513543543 58841511207079566770315315)
    ·
      refine ⟨88262266810619350155472973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58841511207079566770315315 88262266810619350155472973)
      ·
        refine ⟨33098350053982256308302365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88262266810619350155472973 33098350053982256308302365)
        ·
          refine ⟨12411881270243346115613387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33098350053982256308302365 12411881270243346115613387)
          ·
            refine ⟨18617821905365019173420081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12411881270243346115613387 18617821905365019173420081)
            ·
              refine ⟨13963366429023764380065061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18617821905365019173420081 13963366429023764380065061)
              ·
                refine ⟨2618131205441955821262199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13963366429023764380065061 2618131205441955821262199)
                ·
                  refine ⟨3927196808162933731893299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618131205441955821262199 3927196808162933731893299)
                  ·
                    refine ⟨5890795212244400597839949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927196808162933731893299 5890795212244400597839949)
                    ·
                      refine ⟨2209048204591650224189981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890795212244400597839949 2209048204591650224189981)
                      ·
                        rfl

theorem cell23_4302106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_4302106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302106 prefixEnd_4302106 := by exact prefixLift 4302106
  have htrace : WordTrace (prefixWord ++ tailWord_4302106) baseStart_4302106 baseEnd_4302106 := by
    simpa [prefixWord, tailWord_4302106, baseEnd_4302106] using wordTrace_append hprefix tailTrace_4302106
  have hstable : (prefixWord ++ tailWord_4302106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302106).length < 2 ^ (prefixWord ++ tailWord_4302106).sum := by decide
  have hdescent : baseEnd_4302106 < baseStart_4302106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302115 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5]
def baseStart_4302115 : Nat := 118140960795 + 4302115 * 2 ^ 59
def prefixEnd_4302115 : Nat := 4983230072969 + 3 ^ 40 * 4302115 * 2
def baseEnd_4302115 : Nat := 2209052825917540688977439

theorem tailTrace_4302115 : CollatzResearch.WordTrace tailWord_4302115 prefixEnd_4302115 2209052825917540688977439 := by
  unfold tailWord_4302115
  simp only [CollatzResearch.WordTrace]
  refine ⟨156911024809179572591251799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104607349872786381727501199 156911024809179572591251799)
  ·
    refine ⟨235366537213769358886877699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156911024809179572591251799 235366537213769358886877699)
    ·
      refine ⟨353049805820654038330316549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235366537213769358886877699 353049805820654038330316549)
      ·
        refine ⟨66196838591372632186934353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 353049805820654038330316549 66196838591372632186934353)
        ·
          refine ⟨49647628943529474140200765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66196838591372632186934353 49647628943529474140200765)
          ·
            refine ⟨18617860853823552802575287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49647628943529474140200765 18617860853823552802575287)
            ·
              refine ⟨27926791280735329203862931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18617860853823552802575287 27926791280735329203862931)
              ·
                refine ⟨41890186921102993805794397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27926791280735329203862931 41890186921102993805794397)
                ·
                  refine ⟨15708820095413622677172899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41890186921102993805794397 15708820095413622677172899)
                  ·
                    refine ⟨23563230143120434015759349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15708820095413622677172899 23563230143120434015759349)
                    ·
                      refine ⟨2209052825917540688977439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23563230143120434015759349 2209052825917540688977439)
                      ·
                        rfl

theorem cell23_4302115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_4302115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302115 prefixEnd_4302115 := by exact prefixLift 4302115
  have htrace : WordTrace (prefixWord ++ tailWord_4302115) baseStart_4302115 baseEnd_4302115 := by
    simpa [prefixWord, tailWord_4302115, baseEnd_4302115] using wordTrace_append hprefix tailTrace_4302115
  have hstable : (prefixWord ++ tailWord_4302115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302115).length < 2 ^ (prefixWord ++ tailWord_4302115).sum := by decide
  have hdescent : baseEnd_4302115 < baseStart_4302115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302129 : List Nat := [1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_4302129 : Nat := 118140960795 + 4302129 * 2 ^ 59
def prefixEnd_4302129 : Nat := 4983230072969 + 3 ^ 40 * 4302129 * 2
def baseEnd_4302129 : Nat := 2209060014646703634202375

theorem tailTrace_4302129 : CollatzResearch.WordTrace tailWord_4302129 prefixEnd_4302129 2209060014646703634202375 := by
  unfold tailWord_4302129
  simp only [CollatzResearch.WordTrace]
  refine ⟨156911535431128852982261441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104607690287419235321507627 156911535431128852982261441)
  ·
    refine ⟨117683651573346639736696081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156911535431128852982261441 117683651573346639736696081)
    ·
      refine ⟨88262738680009979802522061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117683651573346639736696081 88262738680009979802522061)
      ·
        refine ⟨33098527005003742425945773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88262738680009979802522061 33098527005003742425945773)
        ·
          refine ⟨12411947626876403409729665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33098527005003742425945773 12411947626876403409729665)
          ·
            refine ⟨9308960720157302557297249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12411947626876403409729665 9308960720157302557297249)
            ·
              refine ⟨6981720540117976917972937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9308960720157302557297249 6981720540117976917972937)
              ·
                refine ⟨5236290405088482688479703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6981720540117976917972937 5236290405088482688479703)
                ·
                  refine ⟨7854435607632724032719555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5236290405088482688479703 7854435607632724032719555)
                  ·
                    refine ⟨11781653411449086049079333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7854435607632724032719555 11781653411449086049079333)
                    ·
                      refine ⟨2209060014646703634202375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11781653411449086049079333 2209060014646703634202375)
                      ·
                        rfl

theorem cell23_4302129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_4302129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302129 prefixEnd_4302129 := by exact prefixLift 4302129
  have htrace : WordTrace (prefixWord ++ tailWord_4302129) baseStart_4302129 baseEnd_4302129 := by
    simpa [prefixWord, tailWord_4302129, baseEnd_4302129] using wordTrace_append hprefix tailTrace_4302129
  have hstable : (prefixWord ++ tailWord_4302129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302129).length < 2 ^ (prefixWord ++ tailWord_4302129).sum := by decide
  have hdescent : baseEnd_4302129 < baseStart_4302129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302132 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4302132 : Nat := 118140960795 + 4302132 * 2 ^ 59
def prefixEnd_4302132 : Nat := 4983230072969 + 3 ^ 40 * 4302132 * 2
def baseEnd_4302132 : Nat := 2209061555088667122464861

theorem tailTrace_4302132 : CollatzResearch.WordTrace tailWord_4302132 prefixEnd_4302132 2209061555088667122464861 := by
  unfold tailWord_4302132
  simp only [CollatzResearch.WordTrace]
  refine ⟨78455822425058992247310325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104607763233411989663080433 78455822425058992247310325)
  ·
    refine ⟨7355233352349280523185343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78455822425058992247310325 7355233352349280523185343)
    ·
      refine ⟨11032850028523920784778015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7355233352349280523185343 11032850028523920784778015)
      ·
        refine ⟨16549275042785881177167023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11032850028523920784778015 16549275042785881177167023)
        ·
          refine ⟨24823912564178821765750535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549275042785881177167023 24823912564178821765750535)
          ·
            refine ⟨37235868846268232648625803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24823912564178821765750535 37235868846268232648625803)
            ·
              refine ⟨55853803269402348972938705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37235868846268232648625803 55853803269402348972938705)
              ·
                refine ⟨41890352452051761729704029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55853803269402348972938705 41890352452051761729704029)
                ·
                  refine ⟨15708882169519410648639011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41890352452051761729704029 15708882169519410648639011)
                  ·
                    refine ⟨23563323254279115972958517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15708882169519410648639011 23563323254279115972958517)
                    ·
                      refine ⟨2209061555088667122464861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23563323254279115972958517 2209061555088667122464861)
                      ·
                        rfl

theorem cell23_4302132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4302132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302132 prefixEnd_4302132 := by exact prefixLift 4302132
  have htrace : WordTrace (prefixWord ++ tailWord_4302132) baseStart_4302132 baseEnd_4302132 := by
    simpa [prefixWord, tailWord_4302132, baseEnd_4302132] using wordTrace_append hprefix tailTrace_4302132
  have hstable : (prefixWord ++ tailWord_4302132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302132).length < 2 ^ (prefixWord ++ tailWord_4302132).sum := by decide
  have hdescent : baseEnd_4302132 < baseStart_4302132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302142 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4302142 : Nat := 118140960795 + 4302142 * 2 ^ 59
def prefixEnd_4302142 : Nat := 4983230072969 + 3 ^ 40 * 4302142 * 2
def baseEnd_4302142 : Nat := 2209066689895212083339815

theorem tailTrace_4302142 : CollatzResearch.WordTrace tailWord_4302142 prefixEnd_4302142 2209066689895212083339815 := by
  unfold tailWord_4302142
  simp only [CollatzResearch.WordTrace]
  refine ⟨19614001197510219525310585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104608006386721170801656453 19614001197510219525310585)
  ·
    refine ⟨14710500898132664643982939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19614001197510219525310585 14710500898132664643982939)
    ·
      refine ⟨22065751347198996965974409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14710500898132664643982939 22065751347198996965974409)
      ·
        refine ⟨16549313510399247724480807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22065751347198996965974409 16549313510399247724480807)
        ·
          refine ⟨24823970265598871586721211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549313510399247724480807 24823970265598871586721211)
          ·
            refine ⟨37235955398398307380081817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24823970265598871586721211 37235955398398307380081817)
            ·
              refine ⟨27926966548798730535061363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37235955398398307380081817 27926966548798730535061363)
              ·
                refine ⟨41890449823198095802592045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27926966548798730535061363 41890449823198095802592045)
                ·
                  refine ⟨15708918683699285925972017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41890449823198095802592045 15708918683699285925972017)
                  ·
                    refine ⟨11781689012774464444479013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15708918683699285925972017 11781689012774464444479013)
                    ·
                      refine ⟨2209066689895212083339815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11781689012774464444479013 2209066689895212083339815)
                      ·
                        rfl

theorem cell23_4302142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4302142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302142 prefixEnd_4302142 := by exact prefixLift 4302142
  have htrace : WordTrace (prefixWord ++ tailWord_4302142) baseStart_4302142 baseEnd_4302142 := by
    simpa [prefixWord, tailWord_4302142, baseEnd_4302142] using wordTrace_append hprefix tailTrace_4302142
  have hstable : (prefixWord ++ tailWord_4302142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302142).length < 2 ^ (prefixWord ++ tailWord_4302142).sum := by decide
  have hdescent : baseEnd_4302142 < baseStart_4302142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302150 : List Nat := [6, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4302150 : Nat := 118140960795 + 4302150 * 2 ^ 59
def prefixEnd_4302150 : Nat := 4983230072969 + 3 ^ 40 * 4302150 * 2
def baseEnd_4302150 : Nat := 2209070797740448052039779

theorem tailTrace_4302150 : CollatzResearch.WordTrace tailWord_4302150 prefixEnd_4302150 2209070797740448052039779 := by
  unfold tailWord_4302150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903509417626649174024247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104608200909368515712517269 4903509417626649174024247)
  ·
    refine ⟨7355264126439973761036371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903509417626649174024247 7355264126439973761036371)
    ·
      refine ⟨11032896189659960641554557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7355264126439973761036371 11032896189659960641554557)
      ·
        refine ⟨4137336071122485240582959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11032896189659960641554557 4137336071122485240582959)
        ·
          refine ⟨6206004106683727860874439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137336071122485240582959 6206004106683727860874439)
          ·
            refine ⟨9309006160025591791311659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206004106683727860874439 9309006160025591791311659)
            ·
              refine ⟨13963509240038387686967489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309006160025591791311659 13963509240038387686967489)
              ·
                refine ⟨10472631930028790765225617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13963509240038387686967489 10472631930028790765225617)
                ·
                  refine ⟨7854473947521593073919213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10472631930028790765225617 7854473947521593073919213)
                  ·
                    refine ⟨2945427730320597402719705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7854473947521593073919213 2945427730320597402719705)
                    ·
                      refine ⟨2209070797740448052039779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945427730320597402719705 2209070797740448052039779)
                      ·
                        rfl

theorem cell23_4302150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4302150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302150 prefixEnd_4302150 := by exact prefixLift 4302150
  have htrace : WordTrace (prefixWord ++ tailWord_4302150) baseStart_4302150 baseEnd_4302150 := by
    simpa [prefixWord, tailWord_4302150, baseEnd_4302150] using wordTrace_append hprefix tailTrace_4302150
  have hstable : (prefixWord ++ tailWord_4302150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302150).length < 2 ^ (prefixWord ++ tailWord_4302150).sum := by decide
  have hdescent : baseEnd_4302150 < baseStart_4302150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302157 : List Nat := [1, 6, 1, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4302157 : Nat := 118140960795 + 4302157 * 2 ^ 59
def prefixEnd_4302157 : Nat := 4983230072969 + 3 ^ 40 * 4302157 * 2
def baseEnd_4302157 : Nat := 2209074392105029524652247

theorem tailTrace_4302157 : CollatzResearch.WordTrace tailWord_4302157 prefixEnd_4302157 2209074392105029524652247 := by
  unfold tailWord_4302157
  simp only [CollatzResearch.WordTrace]
  refine ⟨156912556675027413764280725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104608371116684942509520483 156912556675027413764280725)
  ·
    refine ⟨7355276094141910020200659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156912556675027413764280725 7355276094141910020200659)
    ·
      refine ⟨11032914141212865030300989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7355276094141910020200659 11032914141212865030300989)
      ·
        refine ⟨4137342802954824386362871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11032914141212865030300989 4137342802954824386362871)
        ·
          refine ⟨6206014204432236579544307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4137342802954824386362871 6206014204432236579544307)
          ·
            refine ⟨9309021306648354869316461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206014204432236579544307 9309021306648354869316461)
            ·
              refine ⟨3490882989993133075993673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9309021306648354869316461 3490882989993133075993673)
              ·
                refine ⟨2618162242494849806995255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490882989993133075993673 2618162242494849806995255)
                ·
                  refine ⟨3927243363742274710492883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618162242494849806995255 3927243363742274710492883)
                  ·
                    refine ⟨5890865045613412065739325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927243363742274710492883 5890865045613412065739325)
                    ·
                      refine ⟨2209074392105029524652247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890865045613412065739325 2209074392105029524652247)
                      ·
                        rfl

theorem cell23_4302157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4302157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302157 prefixEnd_4302157 := by exact prefixLift 4302157
  have htrace : WordTrace (prefixWord ++ tailWord_4302157) baseStart_4302157 baseEnd_4302157 := by
    simpa [prefixWord, tailWord_4302157, baseEnd_4302157] using wordTrace_append hprefix tailTrace_4302157
  have hstable : (prefixWord ++ tailWord_4302157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302157).length < 2 ^ (prefixWord ++ tailWord_4302157).sum := by decide
  have hdescent : baseEnd_4302157 < baseStart_4302157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302163 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 1, 2, 2]
def baseStart_4302163 : Nat := 118140960795 + 4302163 * 2 ^ 59
def prefixEnd_4302163 : Nat := 4983230072969 + 3 ^ 40 * 4302163 * 2
def baseEnd_4302163 : Nat := 2209077472988956501177219

theorem tailTrace_4302163 : CollatzResearch.WordTrace tailWord_4302163 prefixEnd_4302163 2209077472988956501177219 := by
  unfold tailWord_4302163
  simp only [CollatzResearch.WordTrace]
  refine ⟨156912775513005676788999143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104608517008670451192666095 156912775513005676788999143)
  ·
    refine ⟨235369163269508515183498715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156912775513005676788999143 235369163269508515183498715)
    ·
      refine ⟨353053744904262772775248073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235369163269508515183498715 353053744904262772775248073)
      ·
        refine ⟨264790308678197079581436055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353053744904262772775248073 264790308678197079581436055)
        ·
          refine ⟨397185463017295619372154083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264790308678197079581436055 397185463017295619372154083)
          ·
            refine ⟨595778194525943429058231125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397185463017295619372154083 595778194525943429058231125)
            ·
              refine ⟨3490887858550449779638073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 595778194525943429058231125 3490887858550449779638073)
              ·
                refine ⟨2618165893912837334728555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3490887858550449779638073 2618165893912837334728555)
                ·
                  refine ⟨3927248840869256002092833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618165893912837334728555 3927248840869256002092833)
                  ·
                    refine ⟨2945436630651942001569625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927248840869256002092833 2945436630651942001569625)
                    ·
                      refine ⟨2209077472988956501177219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945436630651942001569625 2209077472988956501177219)
                      ·
                        rfl

theorem cell23_4302163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 1, 2, 2].length) (baseStart_4302163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302163 prefixEnd_4302163 := by exact prefixLift 4302163
  have htrace : WordTrace (prefixWord ++ tailWord_4302163) baseStart_4302163 baseEnd_4302163 := by
    simpa [prefixWord, tailWord_4302163, baseEnd_4302163] using wordTrace_append hprefix tailTrace_4302163
  have hstable : (prefixWord ++ tailWord_4302163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302163).length < 2 ^ (prefixWord ++ tailWord_4302163).sum := by decide
  have hdescent : baseEnd_4302163 < baseStart_4302163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302183 : List Nat := [1, 1, 5, 1, 5, 1, 1, 2, 1, 2, 3]
def baseStart_4302183 : Nat := 118140960795 + 4302183 * 2 ^ 59
def prefixEnd_4302183 : Nat := 4983230072969 + 3 ^ 40 * 4302183 * 2
def baseEnd_4302183 : Nat := 2209087742602046422927127

theorem tailTrace_4302183 : CollatzResearch.WordTrace tailWord_4302183 prefixEnd_4302183 2209087742602046422927127 := by
  unfold tailWord_4302183
  simp only [CollatzResearch.WordTrace]
  refine ⟨156913504972933220204727203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104609003315288813469818135 156913504972933220204727203)
  ·
    refine ⟨235370257459399830307090805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156913504972933220204727203 235370257459399830307090805)
    ·
      refine ⟨22065961636818734091289763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235370257459399830307090805 22065961636818734091289763)
      ·
        refine ⟨33098942455228101136934645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22065961636818734091289763 33098942455228101136934645)
        ·
          refine ⟨3103025855177634481587623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33098942455228101136934645 3103025855177634481587623)
          ·
            refine ⟨4654538782766451722381435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103025855177634481587623 4654538782766451722381435)
            ·
              refine ⟨6981808174149677583572153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4654538782766451722381435 6981808174149677583572153)
              ·
                refine ⟨5236356130612258187679115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6981808174149677583572153 5236356130612258187679115)
                ·
                  refine ⟨7854534195918387281518673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5236356130612258187679115 7854534195918387281518673)
                  ·
                    refine ⟨5890900646938790461139005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7854534195918387281518673 5890900646938790461139005)
                    ·
                      refine ⟨2209087742602046422927127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5890900646938790461139005 2209087742602046422927127)
                      ·
                        rfl

theorem cell23_4302183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_4302183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302183 prefixEnd_4302183 := by exact prefixLift 4302183
  have htrace : WordTrace (prefixWord ++ tailWord_4302183) baseStart_4302183 baseEnd_4302183 := by
    simpa [prefixWord, tailWord_4302183, baseEnd_4302183] using wordTrace_append hprefix tailTrace_4302183
  have hstable : (prefixWord ++ tailWord_4302183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302183).length < 2 ^ (prefixWord ++ tailWord_4302183).sum := by decide
  have hdescent : baseEnd_4302183 < baseStart_4302183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302185 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_4302185 : Nat := 118140960795 + 4302185 * 2 ^ 59
def prefixEnd_4302185 : Nat := 4983230072969 + 3 ^ 40 * 4302185 * 2
def baseEnd_4302185 : Nat := 2209088769563355415102117

theorem tailTrace_4302185 : CollatzResearch.WordTrace tailWord_4302185 prefixEnd_4302185 2209088769563355415102117 := by
  unfold tailWord_4302185
  simp only [CollatzResearch.WordTrace]
  refine ⟨156913577918925974546300009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104609051945950649697533339 156913577918925974546300009)
  ·
    refine ⟨117685183439194480909725007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156913577918925974546300009 117685183439194480909725007)
    ·
      refine ⟨176527775158791721364587511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117685183439194480909725007 176527775158791721364587511)
      ·
        refine ⟨264791662738187582046881267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176527775158791721364587511 264791662738187582046881267)
        ·
          refine ⟨397187494107281373070321901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264791662738187582046881267 397187494107281373070321901)
          ·
            refine ⟨148945310290230514901370713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 397187494107281373070321901 148945310290230514901370713)
            ·
              refine ⟨111708982717672886176028035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148945310290230514901370713 111708982717672886176028035)
              ·
                refine ⟨167563474076509329264042053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111708982717672886176028035 167563474076509329264042053)
                ·
                  refine ⟨31418151389345499237007885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167563474076509329264042053 31418151389345499237007885)
                  ·
                    refine ⟨11781806771004562213877957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31418151389345499237007885 11781806771004562213877957)
                    ·
                      refine ⟨2209088769563355415102117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11781806771004562213877957 2209088769563355415102117)
                      ·
                        rfl

theorem cell23_4302185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_4302185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302185 prefixEnd_4302185 := by exact prefixLift 4302185
  have htrace : WordTrace (prefixWord ++ tailWord_4302185) baseStart_4302185 baseEnd_4302185 := by
    simpa [prefixWord, tailWord_4302185, baseEnd_4302185] using wordTrace_append hprefix tailTrace_4302185
  have hstable : (prefixWord ++ tailWord_4302185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302185).length < 2 ^ (prefixWord ++ tailWord_4302185).sum := by decide
  have hdescent : baseEnd_4302185 < baseStart_4302185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302242 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_4302242 : Nat := 118140960795 + 4302242 * 2 ^ 59
def prefixEnd_4302242 : Nat := 4983230072969 + 3 ^ 40 * 4302242 * 2
def baseEnd_4302242 : Nat := 245457559773406854676595

theorem tailTrace_4302242 : CollatzResearch.WordTrace tailWord_4302242 prefixEnd_4302242 245457559773406854676595 := by
  unfold tailWord_4302242
  simp only [CollatzResearch.WordTrace]
  refine ⟨39228914219929868320281245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104610437919812982187416653 39228914219929868320281245)
  ·
    refine ⟨14710842832473700620105467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39228914219929868320281245 14710842832473700620105467)
    ·
      refine ⟨22066264248710550930158201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14710842832473700620105467 22066264248710550930158201)
      ·
        refine ⟨16549698186532913197618651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22066264248710550930158201 16549698186532913197618651)
        ·
          refine ⟨24824547279799369796427977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16549698186532913197618651 24824547279799369796427977)
          ·
            refine ⟨18618410459849527347320983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24824547279799369796427977 18618410459849527347320983)
            ·
              refine ⟨27927615689774291020981475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18618410459849527347320983 27927615689774291020981475)
              ·
                refine ⟨41891423534661436531472213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27927615689774291020981475 41891423534661436531472213)
                ·
                  refine ⟨245457559773406854676595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41891423534661436531472213 245457559773406854676595)
                  ·
                    rfl

theorem cell23_4302242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_4302242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302242 prefixEnd_4302242 := by exact prefixLift 4302242
  have htrace : WordTrace (prefixWord ++ tailWord_4302242) baseStart_4302242 baseEnd_4302242 := by
    simpa [prefixWord, tailWord_4302242, baseEnd_4302242] using wordTrace_append hprefix tailTrace_4302242
  have hstable : (prefixWord ++ tailWord_4302242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302242).length < 2 ^ (prefixWord ++ tailWord_4302242).sum := by decide
  have hdescent : baseEnd_4302242 < baseStart_4302242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302272 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 2, 5]
def baseStart_4302272 : Nat := 118140960795 + 4302272 * 2 ^ 59
def prefixEnd_4302272 : Nat := 4983230072969 + 3 ^ 40 * 4302272 * 2
def baseEnd_4302272 : Nat := 736377814126765524904739

theorem tailTrace_4302272 : CollatzResearch.WordTrace tailWord_4302272 prefixEnd_4302272 736377814126765524904739 := by
  unfold tailWord_4302272
  simp only [CollatzResearch.WordTrace]
  refine ⟨78458375534805394202358535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104611167379740525603144713 78458375534805394202358535)
  ·
    refine ⟨117687563302208091303537803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78458375534805394202358535 117687563302208091303537803)
    ·
      refine ⟨176531344953312136955306705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117687563302208091303537803 176531344953312136955306705)
      ·
        refine ⟨132398508714984102716480029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176531344953312136955306705 132398508714984102716480029)
        ·
          refine ⟨49649440768119038518680011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132398508714984102716480029 49649440768119038518680011)
          ·
            refine ⟨74474161152178557778020017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49649440768119038518680011 74474161152178557778020017)
            ·
              refine ⟨55855620864133918333515013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74474161152178557778020017 55855620864133918333515013)
              ·
                refine ⟨10472928912025109687534065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55855620864133918333515013 10472928912025109687534065)
                ·
                  refine ⟨7854696684018832265650549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10472928912025109687534065 7854696684018832265650549)
                  ·
                    refine ⟨736377814126765524904739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7854696684018832265650549 736377814126765524904739)
                    ·
                      rfl

theorem cell23_4302272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2, 5].length) (baseStart_4302272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302272 prefixEnd_4302272 := by exact prefixLift 4302272
  have htrace : WordTrace (prefixWord ++ tailWord_4302272) baseStart_4302272 baseEnd_4302272 := by
    simpa [prefixWord, tailWord_4302272, baseEnd_4302272] using wordTrace_append hprefix tailTrace_4302272
  have hstable : (prefixWord ++ tailWord_4302272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302272).length < 2 ^ (prefixWord ++ tailWord_4302272).sum := by decide
  have hdescent : baseEnd_4302272 < baseStart_4302272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302276 : List Nat := [2, 3, 3, 2, 1, 1, 2, 4, 5]
def baseStart_4302276 : Nat := 118140960795 + 4302276 * 2 ^ 59
def prefixEnd_4302276 : Nat := 4983230072969 + 3 ^ 40 * 4302276 * 2
def baseEnd_4302276 : Nat := 245459499589212728784911

theorem tailTrace_4302276 : CollatzResearch.WordTrace tailWord_4302276 prefixEnd_4302276 245459499589212728784911 := by
  unfold tailWord_4302276
  simp only [CollatzResearch.WordTrace]
  refine ⟨78458448480798148543931341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104611264641064198058575121 78458448480798148543931341)
  ·
    refine ⟨29421918180299305703974253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78458448480798148543931341 29421918180299305703974253)
    ·
      refine ⟨11033219317612239638990345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29421918180299305703974253 11033219317612239638990345)
      ·
        refine ⟨8274914488209179729242759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11033219317612239638990345 8274914488209179729242759)
        ·
          refine ⟨12412371732313769593864139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8274914488209179729242759 12412371732313769593864139)
          ·
            refine ⟨18618557598470654390796209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12412371732313769593864139 18618557598470654390796209)
            ·
              refine ⟨13963918198852990793097157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18618557598470654390796209 13963918198852990793097157)
              ·
                refine ⟨2618234662284935773705717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13963918198852990793097157 2618234662284935773705717)
                ·
                  refine ⟨245459499589212728784911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2618234662284935773705717 245459499589212728784911)
                  ·
                    rfl

theorem cell23_4302276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_4302276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302276 prefixEnd_4302276 := by exact prefixLift 4302276
  have htrace : WordTrace (prefixWord ++ tailWord_4302276) baseStart_4302276 baseEnd_4302276 := by
    simpa [prefixWord, tailWord_4302276, baseEnd_4302276] using wordTrace_append hprefix tailTrace_4302276
  have hstable : (prefixWord ++ tailWord_4302276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302276).length < 2 ^ (prefixWord ++ tailWord_4302276).sum := by decide
  have hdescent : baseEnd_4302276 < baseStart_4302276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302309 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4302309 : Nat := 118140960795 + 4302309 * 2 ^ 59
def prefixEnd_4302309 : Nat := 4983230072969 + 3 ^ 40 * 4302309 * 2
def baseEnd_4302309 : Nat := 2209152441164512929951547

theorem tailTrace_4302309 : CollatzResearch.WordTrace tailWord_4302309 prefixEnd_4302309 2209152441164512929951547 := by
  unfold tailWord_4302309
  simp only [CollatzResearch.WordTrace]
  refine ⟨156918100570476743723813981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104612067046984495815875987 156918100570476743723813981)
  ·
    refine ⟨58844287713928778896430243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156918100570476743723813981 58844287713928778896430243)
    ·
      refine ⟨88266431570893168344645365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58844287713928778896430243 88266431570893168344645365)
      ·
        refine ⟨8274977959771234532310503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88266431570893168344645365 8274977959771234532310503)
        ·
          refine ⟨12412466939656851798465755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8274977959771234532310503 12412466939656851798465755)
          ·
            refine ⟨18618700409485277697698633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12412466939656851798465755 18618700409485277697698633)
            ·
              refine ⟨13964025307113958273273975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18618700409485277697698633 13964025307113958273273975)
              ·
                refine ⟨20946037960670937409910963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13964025307113958273273975 20946037960670937409910963)
                ·
                  refine ⟨31419056941006406114866445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20946037960670937409910963 31419056941006406114866445)
                  ·
                    refine ⟨11782146352877402293074917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31419056941006406114866445 11782146352877402293074917)
                    ·
                      refine ⟨2209152441164512929951547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11782146352877402293074917 2209152441164512929951547)
                      ·
                        rfl

theorem cell23_4302309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4302309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302309 prefixEnd_4302309 := by exact prefixLift 4302309
  have htrace : WordTrace (prefixWord ++ tailWord_4302309) baseStart_4302309 baseEnd_4302309 := by
    simpa [prefixWord, tailWord_4302309, baseEnd_4302309] using wordTrace_append hprefix tailTrace_4302309
  have hstable : (prefixWord ++ tailWord_4302309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302309).length < 2 ^ (prefixWord ++ tailWord_4302309).sum := by decide
  have hdescent : baseEnd_4302309 < baseStart_4302309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302326 : List Nat := [5, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4302326 : Nat := 118140960795 + 4302326 * 2 ^ 59
def prefixEnd_4302326 : Nat := 4983230072969 + 3 ^ 40 * 4302326 * 2
def baseEnd_4302326 : Nat := 2209161170335639363438969

theorem tailTrace_4302326 : CollatzResearch.WordTrace tailWord_4302326 prefixEnd_4302326 2209161170335639363438969 := by
  unfold tailWord_4302326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9807420038213447226698927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104612480407610103751455221 9807420038213447226698927)
  ·
    refine ⟨14711130057320170840048391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9807420038213447226698927 14711130057320170840048391)
    ·
      refine ⟨22066695085980256260072587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14711130057320170840048391 22066695085980256260072587)
      ·
        refine ⟨33100042628970384390108881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22066695085980256260072587 33100042628970384390108881)
        ·
          refine ⟨24825031971727788292581661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33100042628970384390108881 24825031971727788292581661)
          ·
            refine ⟨9309386989397920609718123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24825031971727788292581661 9309386989397920609718123)
            ·
              refine ⟨13964080484096880914577185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309386989397920609718123 13964080484096880914577185)
              ·
                refine ⟨10473060363072660685932889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13964080484096880914577185 10473060363072660685932889)
                ·
                  refine ⟨7854795272304495514449667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10473060363072660685932889 7854795272304495514449667)
                  ·
                    refine ⟨11782192908456743271674501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7854795272304495514449667 11782192908456743271674501)
                    ·
                      refine ⟨2209161170335639363438969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11782192908456743271674501 2209161170335639363438969)
                      ·
                        rfl

theorem cell23_4302326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4302326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302326 prefixEnd_4302326 := by exact prefixLift 4302326
  have htrace : WordTrace (prefixWord ++ tailWord_4302326) baseStart_4302326 baseEnd_4302326 := by
    simpa [prefixWord, tailWord_4302326, baseEnd_4302326] using wordTrace_append hprefix tailTrace_4302326
  have hstable : (prefixWord ++ tailWord_4302326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302326).length < 2 ^ (prefixWord ++ tailWord_4302326).sum := by decide
  have hdescent : baseEnd_4302326 < baseStart_4302326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302332 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 8]
def baseStart_4302332 : Nat := 118140960795 + 4302332 * 2 ^ 59
def prefixEnd_4302332 : Nat := 4983230072969 + 3 ^ 40 * 4302332 * 2
def baseEnd_4302332 : Nat := 245462694579951815551549

theorem tailTrace_4302332 : CollatzResearch.WordTrace tailWord_4302332 prefixEnd_4302332 245462694579951815551549 := by
  unfold tailWord_4302332
  simp only [CollatzResearch.WordTrace]
  refine ⟨78459469724696709325950625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104612626299595612434600833 78459469724696709325950625)
  ·
    refine ⟨58844602293522531994462969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78459469724696709325950625 58844602293522531994462969)
    ·
      refine ⟨44133451720141898995847227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58844602293522531994462969 44133451720141898995847227)
      ·
        refine ⟨66200177580212848493770841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44133451720141898995847227 66200177580212848493770841)
        ·
          refine ⟨49650133185159636370328131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66200177580212848493770841 49650133185159636370328131)
          ·
            refine ⟨74475199777739454555492197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49650133185159636370328131 74475199777739454555492197)
            ·
              refine ⟨13964099958326147729154787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74475199777739454555492197 13964099958326147729154787)
              ·
                refine ⟨20946149937489221593732181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13964099958326147729154787 20946149937489221593732181)
                ·
                  refine ⟨245462694579951815551549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20946149937489221593732181 245462694579951815551549)
                  ·
                    rfl

theorem cell23_4302332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_4302332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302332 prefixEnd_4302332 := by exact prefixLift 4302332
  have htrace : WordTrace (prefixWord ++ tailWord_4302332) baseStart_4302332 baseEnd_4302332 := by
    simpa [prefixWord, tailWord_4302332, baseEnd_4302332] using wordTrace_append hprefix tailTrace_4302332
  have hstable : (prefixWord ++ tailWord_4302332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302332).length < 2 ^ (prefixWord ++ tailWord_4302332).sum := by decide
  have hdescent : baseEnd_4302332 < baseStart_4302332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302399 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4]
def baseStart_4302399 : Nat := 118140960795 + 4302399 * 2 ^ 59
def prefixEnd_4302399 : Nat := 4983230072969 + 3 ^ 40 * 4302399 * 2
def baseEnd_4302399 : Nat := 2209198654423417577826133

theorem tailTrace_4302399 : CollatzResearch.WordTrace tailWord_4302399 prefixEnd_4302399 2209198654423417577826133 := by
  unfold tailWord_4302399
  simp only [CollatzResearch.WordTrace]
  refine ⟨156921383140150689094590251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104614255426767126063060167 156921383140150689094590251)
  ·
    refine ⟨235382074710226033641885377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156921383140150689094590251 235382074710226033641885377)
    ·
      refine ⟨176536556032669525231414033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235382074710226033641885377 176536556032669525231414033)
      ·
        refine ⟨132402417024502143923560525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176536556032669525231414033 132402417024502143923560525)
        ·
          refine ⟨49650906384188303971335197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132402417024502143923560525 49650906384188303971335197)
          ·
            refine ⟨18619089894070613989250699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49650906384188303971335197 18619089894070613989250699)
            ·
              refine ⟨27928634841105920983876049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18619089894070613989250699 27928634841105920983876049)
              ·
                refine ⟨20946476130829440737907037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27928634841105920983876049 20946476130829440737907037)
                ·
                  refine ⟨7854928549061040276715139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20946476130829440737907037 7854928549061040276715139)
                  ·
                    refine ⟨11782392823591560415072709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7854928549061040276715139 11782392823591560415072709)
                    ·
                      refine ⟨2209198654423417577826133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11782392823591560415072709 2209198654423417577826133)
                      ·
                        rfl

theorem cell23_4302399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_4302399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302399 prefixEnd_4302399 := by exact prefixLift 4302399
  have htrace : WordTrace (prefixWord ++ tailWord_4302399) baseStart_4302399 baseEnd_4302399 := by
    simpa [prefixWord, tailWord_4302399, baseEnd_4302399] using wordTrace_append hprefix tailTrace_4302399
  have hstable : (prefixWord ++ tailWord_4302399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302399).length < 2 ^ (prefixWord ++ tailWord_4302399).sum := by decide
  have hdescent : baseEnd_4302399 < baseStart_4302399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302449 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_4302449 : Nat := 118140960795 + 4302449 * 2 ^ 59
def prefixEnd_4302449 : Nat := 4983230072969 + 3 ^ 40 * 4302449 * 2
def baseEnd_4302449 : Nat := 2209224328456142382200903

theorem tailTrace_4302449 : CollatzResearch.WordTrace tailWord_4302449 prefixEnd_4302449 2209224328456142382200903 := by
  unfold tailWord_4302449
  simp only [CollatzResearch.WordTrace]
  refine ⟨156923206789969547633910401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104615471193313031755940267 156923206789969547633910401)
  ·
    refine ⟨117692405092477160725432801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156923206789969547633910401 117692405092477160725432801)
    ·
      refine ⟨88269303819357870544074601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117692405092477160725432801 88269303819357870544074601)
      ·
        refine ⟨66201977864518402908055951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88269303819357870544074601 66201977864518402908055951)
        ·
          refine ⟨99302966796777604362083927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66201977864518402908055951 99302966796777604362083927)
          ·
            refine ⟨148954450195166406543125891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99302966796777604362083927 148954450195166406543125891)
            ·
              refine ⟨223431675292749609814688837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148954450195166406543125891 223431675292749609814688837)
              ·
                refine ⟨41893439117390551840254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223431675292749609814688837 41893439117390551840254157)
                ·
                  refine ⟨15710039669021456940095309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41893439117390551840254157 15710039669021456940095309)
                  ·
                    refine ⟨5891264875883046352535741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15710039669021456940095309 5891264875883046352535741)
                    ·
                      refine ⟨2209224328456142382200903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891264875883046352535741 2209224328456142382200903)
                      ·
                        rfl

theorem cell23_4302449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_4302449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302449 prefixEnd_4302449 := by exact prefixLift 4302449
  have htrace : WordTrace (prefixWord ++ tailWord_4302449) baseStart_4302449 baseEnd_4302449 := by
    simpa [prefixWord, tailWord_4302449, baseEnd_4302449] using wordTrace_append hprefix tailTrace_4302449
  have hstable : (prefixWord ++ tailWord_4302449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302449).length < 2 ^ (prefixWord ++ tailWord_4302449).sum := by decide
  have hdescent : baseEnd_4302449 < baseStart_4302449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302450 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_4302450 : Nat := 118140960795 + 4302450 * 2 ^ 59
def prefixEnd_4302450 : Nat := 4983230072969 + 3 ^ 40 * 4302450 * 2
def baseEnd_4302450 : Nat := 2209224841936796878288399

theorem tailTrace_4302450 : CollatzResearch.WordTrace tailWord_4302450 prefixEnd_4302450 2209224841936796878288399 := by
  unfold tailWord_4302450
  simp only [CollatzResearch.WordTrace]
  refine ⟨39230810815741481201174201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104615495508643949869797869 39230810815741481201174201)
  ·
    refine ⟨29423108111806110900880651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39230810815741481201174201 29423108111806110900880651)
    ·
      refine ⟨44134662167709166351320977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29423108111806110900880651 44134662167709166351320977)
      ·
        refine ⟨33100996625781874763490733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44134662167709166351320977 33100996625781874763490733)
        ·
          refine ⟨12412873734668203036309025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33100996625781874763490733 12412873734668203036309025)
          ·
            refine ⟨9309655301001152277231769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12412873734668203036309025 9309655301001152277231769)
            ·
              refine ⟨6982241475750864207923827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9309655301001152277231769 6982241475750864207923827)
              ·
                refine ⟨10473362213626296311885741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982241475750864207923827 10473362213626296311885741)
                ·
                  refine ⟨3927510830109861116957153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10473362213626296311885741 3927510830109861116957153)
                  ·
                    refine ⟨2945633122582395837717865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927510830109861116957153 2945633122582395837717865)
                    ·
                      refine ⟨2209224841936796878288399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945633122582395837717865 2209224841936796878288399)
                      ·
                        rfl

theorem cell23_4302450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_4302450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302450 prefixEnd_4302450 := by exact prefixLift 4302450
  have htrace : WordTrace (prefixWord ++ tailWord_4302450) baseStart_4302450 baseEnd_4302450 := by
    simpa [prefixWord, tailWord_4302450, baseEnd_4302450] using wordTrace_append hprefix tailTrace_4302450
  have hstable : (prefixWord ++ tailWord_4302450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302450).length < 2 ^ (prefixWord ++ tailWord_4302450).sum := by decide
  have hdescent : baseEnd_4302450 < baseStart_4302450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302526 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4302526 : Nat := 118140960795 + 4302526 * 2 ^ 59
def prefixEnd_4302526 : Nat := 4983230072969 + 3 ^ 40 * 4302526 * 2
def baseEnd_4302526 : Nat := 2209263866466538580938049

theorem tailTrace_4302526 : CollatzResearch.WordTrace tailWord_4302526 prefixEnd_4302526 2209263866466538580938049 := by
  unfold tailWord_4302526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19615751901336323723057929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104617343473793726522975621 19615751901336323723057929)
  ·
    refine ⟨14711813926002242792293447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19615751901336323723057929 14711813926002242792293447)
    ·
      refine ⟨22067720889003364188440171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14711813926002242792293447 22067720889003364188440171)
      ·
        refine ⟨33101581333505046282660257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22067720889003364188440171 33101581333505046282660257)
        ·
          refine ⟨24826186000128784711995193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33101581333505046282660257 24826186000128784711995193)
          ·
            refine ⟨18619639500096588533996395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24826186000128784711995193 18619639500096588533996395)
            ·
              refine ⟨27929459250144882800994593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18619639500096588533996395 27929459250144882800994593)
              ·
                refine ⟨20947094437608662100745945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27929459250144882800994593 20947094437608662100745945)
                ·
                  refine ⟨15710320828206496575559459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20947094437608662100745945 15710320828206496575559459)
                  ·
                    refine ⟨23565481242309744863339189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15710320828206496575559459 23565481242309744863339189)
                    ·
                      refine ⟨2209263866466538580938049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23565481242309744863339189 2209263866466538580938049)
                      ·
                        rfl

theorem cell23_4302526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4302526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302526 prefixEnd_4302526 := by exact prefixLift 4302526
  have htrace : WordTrace (prefixWord ++ tailWord_4302526) baseStart_4302526 baseEnd_4302526 := by
    simpa [prefixWord, tailWord_4302526, baseEnd_4302526] using wordTrace_append hprefix tailTrace_4302526
  have hstable : (prefixWord ++ tailWord_4302526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302526).length < 2 ^ (prefixWord ++ tailWord_4302526).sum := by decide
  have hdescent : baseEnd_4302526 < baseStart_4302526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302540 : List Nat := [2, 2, 1, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4302540 : Nat := 118140960795 + 4302540 * 2 ^ 59
def prefixEnd_4302540 : Nat := 4983230072969 + 3 ^ 40 * 4302540 * 2
def baseEnd_4302540 : Nat := 2209271055195701526162985

theorem tailTrace_4302540 : CollatzResearch.WordTrace tailWord_4302540 prefixEnd_4302540 2209271055195701526162985 := by
  unfold tailWord_4302540
  simp only [CollatzResearch.WordTrace]
  refine ⟨78463262916319935087736537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104617683888426580116982049 78463262916319935087736537)
  ·
    refine ⟨58847447187239951315802403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78463262916319935087736537 58847447187239951315802403)
    ·
      refine ⟨88271170780859926973703605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58847447187239951315802403 88271170780859926973703605)
      ·
        refine ⟨8275422260705618153784713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88271170780859926973703605 8275422260705618153784713)
        ·
          refine ⟨6206566695529213615338535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8275422260705618153784713 6206566695529213615338535)
          ·
            refine ⟨9309850043293820423007803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206566695529213615338535 9309850043293820423007803)
            ·
              refine ⟨13964775064940730634511705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309850043293820423007803 13964775064940730634511705)
              ·
                refine ⟨10473581298705547975883779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13964775064940730634511705 10473581298705547975883779)
                ·
                  refine ⟨15710371948058321963825669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10473581298705547975883779 15710371948058321963825669)
                  ·
                    refine ⟨2945694740260935368217313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15710371948058321963825669 2945694740260935368217313)
                    ·
                      refine ⟨2209271055195701526162985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945694740260935368217313 2209271055195701526162985)
                      ·
                        rfl

theorem cell23_4302540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4302540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302540 prefixEnd_4302540 := by exact prefixLift 4302540
  have htrace : WordTrace (prefixWord ++ tailWord_4302540) baseStart_4302540 baseEnd_4302540 := by
    simpa [prefixWord, tailWord_4302540, baseEnd_4302540] using wordTrace_append hprefix tailTrace_4302540
  have hstable : (prefixWord ++ tailWord_4302540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302540).length < 2 ^ (prefixWord ++ tailWord_4302540).sum := by decide
  have hdescent : baseEnd_4302540 < baseStart_4302540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302573 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4302573 : Nat := 118140960795 + 4302573 * 2 ^ 59
def prefixEnd_4302573 : Nat := 4983230072969 + 3 ^ 40 * 4302573 * 2
def baseEnd_4302573 : Nat := 2209288000057299897050333

theorem tailTrace_4302573 : CollatzResearch.WordTrace tailWord_4302573 prefixEnd_4302573 2209288000057299897050333 := by
  unfold tailWord_4302573
  simp only [CollatzResearch.WordTrace]
  refine ⟨156927729441520316811424373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104618486294346877874282915 156927729441520316811424373)
  ·
    refine ⟨14711974635142529701071035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156927729441520316811424373 14711974635142529701071035)
    ·
      refine ⟨22067961952713794551606553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14711974635142529701071035 22067961952713794551606553)
      ·
        refine ⟨16550971464535345913704915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22067961952713794551606553 16550971464535345913704915)
        ·
          refine ⟨24826457196803018870557373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16550971464535345913704915 24826457196803018870557373)
          ·
            refine ⟨9309921448801132076459015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24826457196803018870557373 9309921448801132076459015)
            ·
              refine ⟨13964882173201698114688523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309921448801132076459015 13964882173201698114688523)
              ·
                refine ⟨20947323259802547172032785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13964882173201698114688523 20947323259802547172032785)
                ·
                  refine ⟨15710492444851910379024589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20947323259802547172032785 15710492444851910379024589)
                  ·
                    refine ⟨5891434666819466392134221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15710492444851910379024589 5891434666819466392134221)
                    ·
                      refine ⟨2209288000057299897050333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891434666819466392134221 2209288000057299897050333)
                      ·
                        rfl

theorem cell23_4302573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4302573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302573 prefixEnd_4302573 := by exact prefixLift 4302573
  have htrace : WordTrace (prefixWord ++ tailWord_4302573) baseStart_4302573 baseEnd_4302573 := by
    simpa [prefixWord, tailWord_4302573, baseEnd_4302573] using wordTrace_append hprefix tailTrace_4302573
  have hstable : (prefixWord ++ tailWord_4302573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302573).length < 2 ^ (prefixWord ++ tailWord_4302573).sum := by decide
  have hdescent : baseEnd_4302573 < baseStart_4302573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302580 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4302580 : Nat := 118140960795 + 4302580 * 2 ^ 59
def prefixEnd_4302580 : Nat := 4983230072969 + 3 ^ 40 * 4302580 * 2
def baseEnd_4302580 : Nat := 245476843824653485518089

theorem tailTrace_4302580 : CollatzResearch.WordTrace tailWord_4302580 prefixEnd_4302580 245476843824653485518089 := by
  unfold tailWord_4302580
  simp only [CollatzResearch.WordTrace]
  refine ⟨78463992376247478503464597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104618656501663304671286129 78463992376247478503464597)
  ·
    refine ⟨3677999642636600554849903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78463992376247478503464597 3677999642636600554849903)
    ·
      refine ⟨5516999463954900832274855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3677999642636600554849903 5516999463954900832274855)
      ·
        refine ⟨8275499195932351248412283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5516999463954900832274855 8275499195932351248412283)
        ·
          refine ⟨12413248793898526872618425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8275499195932351248412283 12413248793898526872618425)
          ·
            refine ⟨9309936595423895154463819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12413248793898526872618425 9309936595423895154463819)
            ·
              refine ⟨13964904893135842731695729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9309936595423895154463819 13964904893135842731695729)
              ·
                refine ⟨10473678669851882048771797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13964904893135842731695729 10473678669851882048771797)
                ·
                  refine ⟨245476843824653485518089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10473678669851882048771797 245476843824653485518089)
                  ·
                    rfl

theorem cell23_4302580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4302580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302580 prefixEnd_4302580 := by exact prefixLift 4302580
  have htrace : WordTrace (prefixWord ++ tailWord_4302580) baseStart_4302580 baseEnd_4302580 := by
    simpa [prefixWord, tailWord_4302580, baseEnd_4302580] using wordTrace_append hprefix tailTrace_4302580
  have hstable : (prefixWord ++ tailWord_4302580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302580).length < 2 ^ (prefixWord ++ tailWord_4302580).sum := by decide
  have hdescent : baseEnd_4302580 < baseStart_4302580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302589 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_4302589 : Nat := 118140960795 + 4302589 * 2 ^ 59
def prefixEnd_4302589 : Nat := 4983230072969 + 3 ^ 40 * 4302589 * 2
def baseEnd_4302589 : Nat := 736432071915923944816753

theorem tailTrace_4302589 : CollatzResearch.WordTrace tailWord_4302589 prefixEnd_4302589 736432071915923944816753 := by
  unfold tailWord_4302589
  simp only [CollatzResearch.WordTrace]
  refine ⟨156928313009462351544006821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104618875339641567696004547 156928313009462351544006821)
  ·
    refine ⟨29424058689274190914501279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156928313009462351544006821 29424058689274190914501279)
    ·
      refine ⟨44136088033911286371751919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29424058689274190914501279 44136088033911286371751919)
      ·
        refine ⟨66204132050866929557627879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44136088033911286371751919 66204132050866929557627879)
        ·
          refine ⟨99306198076300394336441819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66204132050866929557627879 99306198076300394336441819)
          ·
            refine ⟨148959297114450591504662729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99306198076300394336441819 148959297114450591504662729)
            ·
              refine ⟨111719472835837943628497047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148959297114450591504662729 111719472835837943628497047)
              ·
                refine ⟨167579209253756915442745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111719472835837943628497047 167579209253756915442745571)
                ·
                  refine ⟨251368813880635373164118357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167579209253756915442745571 251368813880635373164118357)
                  ·
                    refine ⟨736432071915923944816753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 251368813880635373164118357 736432071915923944816753)
                    ·
                      rfl

theorem cell23_4302589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_4302589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302589 prefixEnd_4302589 := by exact prefixLift 4302589
  have htrace : WordTrace (prefixWord ++ tailWord_4302589) baseStart_4302589 baseEnd_4302589 := by
    simpa [prefixWord, tailWord_4302589, baseEnd_4302589] using wordTrace_append hprefix tailTrace_4302589
  have hstable : (prefixWord ++ tailWord_4302589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302589).length < 2 ^ (prefixWord ++ tailWord_4302589).sum := by decide
  have hdescent : baseEnd_4302589 < baseStart_4302589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302613 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_4302613 : Nat := 118140960795 + 4302613 * 2 ^ 59
def prefixEnd_4302613 : Nat := 4983230072969 + 3 ^ 40 * 4302613 * 2
def baseEnd_4302613 : Nat := 2209308539283479740550149

theorem tailTrace_4302613 : CollatzResearch.WordTrace tailWord_4302613 prefixEnd_4302613 2209308539283479740550149 := by
  unfold tailWord_4302613
  simp only [CollatzResearch.WordTrace]
  refine ⟨156929188361375403642880493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104619458907583602428586995 156929188361375403642880493)
  ·
    refine ⟨58848445635515776366080185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156929188361375403642880493 58848445635515776366080185)
    ·
      refine ⟨44136334226636832274560139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58848445635515776366080185 44136334226636832274560139)
      ·
        refine ⟨66204501339955248411840209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44136334226636832274560139 66204501339955248411840209)
        ·
          refine ⟨49653376004966436308880157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66204501339955248411840209 49653376004966436308880157)
          ·
            refine ⟨18620016001862413615830059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49653376004966436308880157 18620016001862413615830059)
            ·
              refine ⟨27930024002793620423745089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18620016001862413615830059 27930024002793620423745089)
              ·
                refine ⟨20947518002095215317808817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27930024002793620423745089 20947518002095215317808817)
                ·
                  refine ⟨15710638501571411488356613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20947518002095215317808817 15710638501571411488356613)
                  ·
                    refine ⟨2945744719044639654066865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15710638501571411488356613 2945744719044639654066865)
                    ·
                      refine ⟨2209308539283479740550149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945744719044639654066865 2209308539283479740550149)
                      ·
                        rfl

theorem cell23_4302613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_4302613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302613 prefixEnd_4302613 := by exact prefixLift 4302613
  have htrace : WordTrace (prefixWord ++ tailWord_4302613) baseStart_4302613 baseEnd_4302613 := by
    simpa [prefixWord, tailWord_4302613, baseEnd_4302613] using wordTrace_append hprefix tailTrace_4302613
  have hstable : (prefixWord ++ tailWord_4302613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302613).length < 2 ^ (prefixWord ++ tailWord_4302613).sum := by decide
  have hdescent : baseEnd_4302613 < baseStart_4302613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302619 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 8]
def baseStart_4302619 : Nat := 118140960795 + 4302619 * 2 ^ 59
def prefixEnd_4302619 : Nat := 4983230072969 + 3 ^ 40 * 4302619 * 2
def baseEnd_4302619 : Nat := 245479068907489635230569

theorem tailTrace_4302619 : CollatzResearch.WordTrace tailWord_4302619 prefixEnd_4302619 245479068907489635230569 := by
  unfold tailWord_4302619
  simp only [CollatzResearch.WordTrace]
  refine ⟨156929407199353666667598911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104619604799569111111732607 156929407199353666667598911)
  ·
    refine ⟨235394110799030500001398367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156929407199353666667598911 235394110799030500001398367)
    ·
      refine ⟨353091166198545750002097551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235394110799030500001398367 353091166198545750002097551)
      ·
        refine ⟨529636749297818625003146327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353091166198545750002097551 529636749297818625003146327)
        ·
          refine ⟨794455123946727937504719491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529636749297818625003146327 794455123946727937504719491)
          ·
            refine ⟨1191682685920091906257079237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794455123946727937504719491 1191682685920091906257079237)
            ·
              refine ⟨223440503610017232423202357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1191682685920091906257079237 223440503610017232423202357)
              ·
                refine ⟨20947547213439115539675221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223440503610017232423202357 20947547213439115539675221)
                ·
                  refine ⟨245479068907489635230569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20947547213439115539675221 245479068907489635230569)
                  ·
                    rfl

theorem cell23_4302619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 8].length) (baseStart_4302619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302619 prefixEnd_4302619 := by exact prefixLift 4302619
  have htrace : WordTrace (prefixWord ++ tailWord_4302619) baseStart_4302619 baseEnd_4302619 := by
    simpa [prefixWord, tailWord_4302619, baseEnd_4302619] using wordTrace_append hprefix tailTrace_4302619
  have hstable : (prefixWord ++ tailWord_4302619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302619).length < 2 ^ (prefixWord ++ tailWord_4302619).sum := by decide
  have hdescent : baseEnd_4302619 < baseStart_4302619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302623 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 3, 4]
def baseStart_4302623 : Nat := 118140960795 + 4302623 * 2 ^ 59
def prefixEnd_4302623 : Nat := 4983230072969 + 3 ^ 40 * 4302623 * 2
def baseEnd_4302623 : Nat := 736437891363341567141701

theorem tailTrace_4302623 : CollatzResearch.WordTrace tailWord_4302623 prefixEnd_4302623 736437891363341567141701 := by
  unfold tailWord_4302623
  simp only [CollatzResearch.WordTrace]
  refine ⟨156929553091339175350744523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104619702060892783567163015 156929553091339175350744523)
  ·
    refine ⟨235394329637008763026116785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156929553091339175350744523 235394329637008763026116785)
    ·
      refine ⟨176545747227756572269587589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235394329637008763026116785 176545747227756572269587589)
      ·
        refine ⟨33102327605204357300547673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176545747227756572269587589 33102327605204357300547673)
        ·
          refine ⟨24826745703903267975410755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33102327605204357300547673 24826745703903267975410755)
          ·
            refine ⟨37240118555854901963116133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24826745703903267975410755 37240118555854901963116133)
            ·
              refine ⟨6982522229222794118084275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37240118555854901963116133 6982522229222794118084275)
              ·
                refine ⟨10473783343834191177126413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982522229222794118084275 10473783343834191177126413)
                ·
                  refine ⟨3927668753937821691422405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10473783343834191177126413 3927668753937821691422405)
                  ·
                    refine ⟨736437891363341567141701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3927668753937821691422405 736437891363341567141701)
                    ·
                      rfl

theorem cell23_4302623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 3, 4].length) (baseStart_4302623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302623 prefixEnd_4302623 := by exact prefixLift 4302623
  have htrace : WordTrace (prefixWord ++ tailWord_4302623) baseStart_4302623 baseEnd_4302623 := by
    simpa [prefixWord, tailWord_4302623, baseEnd_4302623] using wordTrace_append hprefix tailTrace_4302623
  have hstable : (prefixWord ++ tailWord_4302623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302623).length < 2 ^ (prefixWord ++ tailWord_4302623).sum := by decide
  have hdescent : baseEnd_4302623 < baseStart_4302623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302626 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4302626 : Nat := 118140960795 + 4302626 * 2 ^ 59
def prefixEnd_4302626 : Nat := 4983230072969 + 3 ^ 40 * 4302626 * 2
def baseEnd_4302626 : Nat := 2209315214531988189687589

theorem tailTrace_4302626 : CollatzResearch.WordTrace tailWord_4302626 prefixEnd_4302626 2209315214531988189687589 := by
  unfold tailWord_4302626
  simp only [CollatzResearch.WordTrace]
  refine ⟨39232415627582076715775933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104619775006885537908735821 39232415627582076715775933)
  ·
    refine ⟨14712155860343278768415975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39232415627582076715775933 14712155860343278768415975)
    ·
      refine ⟨22068233790514918152623963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14712155860343278768415975 22068233790514918152623963)
      ·
        refine ⟨33102350685772377228935945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22068233790514918152623963 33102350685772377228935945)
        ·
          refine ⟨24826763014329282921701959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33102350685772377228935945 24826763014329282921701959)
          ·
            refine ⟨37240144521493924382552939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24826763014329282921701959 37240144521493924382552939)
            ·
              refine ⟨55860216782240886573829409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37240144521493924382552939 55860216782240886573829409)
              ·
                refine ⟨41895162586680664930372057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55860216782240886573829409 41895162586680664930372057)
                ·
                  refine ⟨31421371940010498697779043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41895162586680664930372057 31421371940010498697779043)
                  ·
                    refine ⟨47132057910015748046668565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31421371940010498697779043 47132057910015748046668565)
                    ·
                      refine ⟨2209315214531988189687589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47132057910015748046668565 2209315214531988189687589)
                      ·
                        rfl

theorem cell23_4302626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4302626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302626 prefixEnd_4302626 := by exact prefixLift 4302626
  have htrace : WordTrace (prefixWord ++ tailWord_4302626) baseStart_4302626 baseEnd_4302626 := by
    simpa [prefixWord, tailWord_4302626, baseEnd_4302626] using wordTrace_append hprefix tailTrace_4302626
  have hstable : (prefixWord ++ tailWord_4302626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302626).length < 2 ^ (prefixWord ++ tailWord_4302626).sum := by decide
  have hdescent : baseEnd_4302626 < baseStart_4302626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302663 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 3]
def baseStart_4302663 : Nat := 118140960795 + 4302663 * 2 ^ 59
def prefixEnd_4302663 : Nat := 4983230072969 + 3 ^ 40 * 4302663 * 2
def baseEnd_4302663 : Nat := 2209334213316204544924919

theorem tailTrace_4302663 : CollatzResearch.WordTrace tailWord_4302663 prefixEnd_4302663 2209334213316204544924919 := by
  unfold tailWord_4302663
  simp only [CollatzResearch.WordTrace]
  refine ⟨156931012011194262182200643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104620674674129508121467095 156931012011194262182200643)
  ·
    refine ⟨235396518016791393273300965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156931012011194262182200643 235396518016791393273300965)
    ·
      refine ⟨44136847128148386238743931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235396518016791393273300965 44136847128148386238743931)
      ·
        refine ⟨66205270692222579358115897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44136847128148386238743931 66205270692222579358115897)
        ·
          refine ⟨49653953019166934518586923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66205270692222579358115897 49653953019166934518586923)
          ·
            refine ⟨74480929528750401777880385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49653953019166934518586923 74480929528750401777880385)
            ·
              refine ⟨55860697146562801333410289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74480929528750401777880385 55860697146562801333410289)
              ·
                refine ⟨41895522859922101000057717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55860697146562801333410289 41895522859922101000057717)
                ·
                  refine ⟨3927705268117696968755411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41895522859922101000057717 3927705268117696968755411)
                  ·
                    refine ⟨5891557902176545453133117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927705268117696968755411 5891557902176545453133117)
                    ·
                      refine ⟨2209334213316204544924919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891557902176545453133117 2209334213316204544924919)
                      ·
                        rfl

theorem cell23_4302663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_4302663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302663 prefixEnd_4302663 := by exact prefixLift 4302663
  have htrace : WordTrace (prefixWord ++ tailWord_4302663) baseStart_4302663 baseEnd_4302663 := by
    simpa [prefixWord, tailWord_4302663, baseEnd_4302663] using wordTrace_append hprefix tailTrace_4302663
  have hstable : (prefixWord ++ tailWord_4302663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302663).length < 2 ^ (prefixWord ++ tailWord_4302663).sum := by decide
  have hdescent : baseEnd_4302663 < baseStart_4302663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302700 : List Nat := [2, 2, 1, 1, 4, 4, 1, 2, 1, 5]
def baseStart_4302700 : Nat := 118140960795 + 4302700 * 2 ^ 59
def prefixEnd_4302700 : Nat := 4983230072969 + 3 ^ 40 * 4302700 * 2
def baseEnd_4302700 : Nat := 736451070700140300054083

theorem tailTrace_4302700 : CollatzResearch.WordTrace tailWord_4302700 prefixEnd_4302700 736451070700140300054083 := by
  unfold tailWord_4302700
  simp only [CollatzResearch.WordTrace]
  refine ⟨78466180756030108750648777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104621574341373478334198369 78466180756030108750648777)
  ·
    refine ⟨58849635567022581562986583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78466180756030108750648777 58849635567022581562986583)
    ·
      refine ⟨88274453350533872344479875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58849635567022581562986583 88274453350533872344479875)
      ·
        refine ⟨132411680025800808516719813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88274453350533872344479875 132411680025800808516719813)
        ·
          refine ⟨24827190004837651596884965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132411680025800808516719813 24827190004837651596884965)
          ·
            refine ⟨4655098125907059674415931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24827190004837651596884965 4655098125907059674415931)
            ·
              refine ⟨6982647188860589511623897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655098125907059674415931 6982647188860589511623897)
              ·
                refine ⟨5236985391645442133717923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6982647188860589511623897 5236985391645442133717923)
                ·
                  refine ⟨7855478087468163200576885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5236985391645442133717923 7855478087468163200576885)
                  ·
                    refine ⟨736451070700140300054083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7855478087468163200576885 736451070700140300054083)
                    ·
                      rfl

theorem cell23_4302700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_4302700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302700 prefixEnd_4302700 := by exact prefixLift 4302700
  have htrace : WordTrace (prefixWord ++ tailWord_4302700) baseStart_4302700 baseEnd_4302700 := by
    simpa [prefixWord, tailWord_4302700, baseEnd_4302700] using wordTrace_append hprefix tailTrace_4302700
  have hstable : (prefixWord ++ tailWord_4302700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302700).length < 2 ^ (prefixWord ++ tailWord_4302700).sum := by decide
  have hdescent : baseEnd_4302700 < baseStart_4302700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302720 : List Nat := [2, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4]
def baseStart_4302720 : Nat := 118140960795 + 4302720 * 2 ^ 59
def prefixEnd_4302720 : Nat := 4983230072969 + 3 ^ 40 * 4302720 * 2
def baseEnd_4302720 : Nat := 2209363481713510821912157

theorem tailTrace_4302720 : CollatzResearch.WordTrace tailWord_4302720 prefixEnd_4302720 2209363481713510821912157 := by
  unfold tailWord_4302720
  simp only [CollatzResearch.WordTrace]
  refine ⟨78466545485993880458512807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104622060647991840611350409 78466545485993880458512807)
  ·
    refine ⟨117699818228990820687769211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78466545485993880458512807 117699818228990820687769211)
    ·
      refine ⟨176549727343486231031653817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117699818228990820687769211 176549727343486231031653817)
      ·
        refine ⟨132412295507614673273740363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176549727343486231031653817 132412295507614673273740363)
        ·
          refine ⟨198618443261422009910610545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132412295507614673273740363 198618443261422009910610545)
          ·
            refine ⟨148963832446066507432957909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198618443261422009910610545 148963832446066507432957909)
            ·
              refine ⟨3491339822954683767959951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148963832446066507432957909 3491339822954683767959951)
              ·
                refine ⟨5237009734432025651939927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491339822954683767959951 5237009734432025651939927)
                ·
                  refine ⟨7855514601648038477909891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5237009734432025651939927 7855514601648038477909891)
                  ·
                    refine ⟨11783271902472057716864837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7855514601648038477909891 11783271902472057716864837)
                    ·
                      refine ⟨2209363481713510821912157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11783271902472057716864837 2209363481713510821912157)
                      ·
                        rfl

theorem cell23_4302720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_4302720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302720 prefixEnd_4302720 := by exact prefixLift 4302720
  have htrace : WordTrace (prefixWord ++ tailWord_4302720) baseStart_4302720 baseEnd_4302720 := by
    simpa [prefixWord, tailWord_4302720, baseEnd_4302720] using wordTrace_append hprefix tailTrace_4302720
  have hstable : (prefixWord ++ tailWord_4302720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302720).length < 2 ^ (prefixWord ++ tailWord_4302720).sum := by decide
  have hdescent : baseEnd_4302720 < baseStart_4302720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302723 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5]
def baseStart_4302723 : Nat := 118140960795 + 4302723 * 2 ^ 59
def prefixEnd_4302723 : Nat := 4983230072969 + 3 ^ 40 * 4302723 * 2
def baseEnd_4302723 : Nat := 2209365022155474310174643

theorem tailTrace_4302723 : CollatzResearch.WordTrace tailWord_4302723 prefixEnd_4302723 2209365022155474310174643 := by
  unfold tailWord_4302723
  simp only [CollatzResearch.WordTrace]
  refine ⟨156933200390976892429384823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104622133593984594952923215 156933200390976892429384823)
  ·
    refine ⟨235399800586465338644077235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156933200390976892429384823 235399800586465338644077235)
    ·
      refine ⟨353099700879698007966115853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235399800586465338644077235 353099700879698007966115853)
      ·
        refine ⟨132412387829886752987293445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353099700879698007966115853 132412387829886752987293445)
        ·
          refine ⟨24827322718103766185117521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132412387829886752987293445 24827322718103766185117521)
          ·
            refine ⟨18620492038577824638838141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24827322718103766185117521 18620492038577824638838141)
            ·
              refine ⟨6982684514466684239564303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18620492038577824638838141 6982684514466684239564303)
              ·
                refine ⟨10474026771700026359346455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6982684514466684239564303 10474026771700026359346455)
                ·
                  refine ⟨15711040157550039539019683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10474026771700026359346455 15711040157550039539019683)
                  ·
                    refine ⟨23566560236325059308529525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15711040157550039539019683 23566560236325059308529525)
                    ·
                      refine ⟨2209365022155474310174643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23566560236325059308529525 2209365022155474310174643)
                      ·
                        rfl

theorem cell23_4302723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_4302723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302723 prefixEnd_4302723 := by exact prefixLift 4302723
  have htrace : WordTrace (prefixWord ++ tailWord_4302723) baseStart_4302723 baseEnd_4302723 := by
    simpa [prefixWord, tailWord_4302723, baseEnd_4302723] using wordTrace_append hprefix tailTrace_4302723
  have hstable : (prefixWord ++ tailWord_4302723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302723).length < 2 ^ (prefixWord ++ tailWord_4302723).sum := by decide
  have hdescent : baseEnd_4302723 < baseStart_4302723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302740 : List Nat := [2, 4, 2, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4302740 : Nat := 118140960795 + 4302740 * 2 ^ 59
def prefixEnd_4302740 : Nat := 4983230072969 + 3 ^ 40 * 4302740 * 2
def baseEnd_4302740 : Nat := 2209373751326600743662065

theorem tailTrace_4302740 : CollatzResearch.WordTrace tailWord_4302740 prefixEnd_4302740 2209373751326600743662065 := by
  unfold tailWord_4302740
  simp only [CollatzResearch.WordTrace]
  refine ⟨78466910215957652166376837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104622546954610202888502449 78466910215957652166376837)
  ·
    refine ⟨14712545665492059781195657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78466910215957652166376837 14712545665492059781195657)
    ·
      refine ⟨11034409249119044835896743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14712545665492059781195657 11034409249119044835896743)
      ·
        refine ⟨16551613873678567253845115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11034409249119044835896743 16551613873678567253845115)
        ·
          refine ⟨24827420810517850880767673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16551613873678567253845115 24827420810517850880767673)
          ·
            refine ⟨18620565607888388160575755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24827420810517850880767673 18620565607888388160575755)
            ·
              refine ⟨27930848411832582240863633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18620565607888388160575755 27930848411832582240863633)
              ·
                refine ⟨20948136308874436680647725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27930848411832582240863633 20948136308874436680647725)
                ·
                  refine ⟨7855551115827913755242897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20948136308874436680647725 7855551115827913755242897)
                  ·
                    refine ⟨5891663336870935316432173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7855551115827913755242897 5891663336870935316432173)
                    ·
                      refine ⟨2209373751326600743662065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891663336870935316432173 2209373751326600743662065)
                      ·
                        rfl

theorem cell23_4302740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4302740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302740 prefixEnd_4302740 := by exact prefixLift 4302740
  have htrace : WordTrace (prefixWord ++ tailWord_4302740) baseStart_4302740 baseEnd_4302740 := by
    simpa [prefixWord, tailWord_4302740, baseEnd_4302740] using wordTrace_append hprefix tailTrace_4302740
  have hstable : (prefixWord ++ tailWord_4302740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302740).length < 2 ^ (prefixWord ++ tailWord_4302740).sum := by decide
  have hdescent : baseEnd_4302740 < baseStart_4302740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302743 : List Nat := [1, 1, 3, 3, 1, 5, 1, 8]
def baseStart_4302743 : Nat := 118140960795 + 4302743 * 2 ^ 59
def prefixEnd_4302743 : Nat := 4983230072969 + 3 ^ 40 * 4302743 * 2
def baseEnd_4302743 : Nat := 81828714509946823404613

theorem tailTrace_4302743 : CollatzResearch.WordTrace tailWord_4302743 prefixEnd_4302743 81828714509946823404613 := by
  unfold tailWord_4302743
  simp only [CollatzResearch.WordTrace]
  refine ⟨156933929850904435845112883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104622619900602957230075255 156933929850904435845112883)
  ·
    refine ⟨235400894776356653767669325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156933929850904435845112883 235400894776356653767669325)
    ·
      refine ⟨88275335541133745162875997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235400894776356653767669325 88275335541133745162875997)
      ·
        refine ⟨33103250827925154436078499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88275335541133745162875997 33103250827925154436078499)
        ·
          refine ⟨49654876241887731654117749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33103250827925154436078499 49654876241887731654117749)
          ·
            refine ⟨4655144647676974842573539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49654876241887731654117749 4655144647676974842573539)
            ·
              refine ⟨6982716971515462263860309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655144647676974842573539 6982716971515462263860309)
              ·
                refine ⟨81828714509946823404613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6982716971515462263860309 81828714509946823404613)
                ·
                  rfl

theorem cell23_4302743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 8].length) (baseStart_4302743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302743 prefixEnd_4302743 := by exact prefixLift 4302743
  have htrace : WordTrace (prefixWord ++ tailWord_4302743) baseStart_4302743 baseEnd_4302743 := by
    simpa [prefixWord, tailWord_4302743, baseEnd_4302743] using wordTrace_append hprefix tailTrace_4302743
  have hstable : (prefixWord ++ tailWord_4302743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302743).length < 2 ^ (prefixWord ++ tailWord_4302743).sum := by decide
  have hdescent : baseEnd_4302743 < baseStart_4302743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302754 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_4302754 : Nat := 118140960795 + 4302754 * 2 ^ 59
def prefixEnd_4302754 : Nat := 4983230072969 + 3 ^ 40 * 4302754 * 2
def baseEnd_4302754 : Nat := 2209380940055763688887001

theorem tailTrace_4302754 : CollatzResearch.WordTrace tailWord_4302754 prefixEnd_4302754 2209380940055763688887001 := by
  unfold tailWord_4302754
  simp only [CollatzResearch.WordTrace]
  refine ⟨39233582763466146180940829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104622887369243056482508877 39233582763466146180940829)
  ·
    refine ⟨14712593536299804817852811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39233582763466146180940829 14712593536299804817852811)
    ·
      refine ⟨22068890304449707226779217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14712593536299804817852811 22068890304449707226779217)
      ·
        refine ⟨16551667728337280420084413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22068890304449707226779217 16551667728337280420084413)
        ·
          refine ⟨6206875398126480157531655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16551667728337280420084413 6206875398126480157531655)
          ·
            refine ⟨9310313097189720236297483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6206875398126480157531655 9310313097189720236297483)
            ·
              refine ⟨13965469645784580354446225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9310313097189720236297483 13965469645784580354446225)
              ·
                refine ⟨10474102234338435265834669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13965469645784580354446225 10474102234338435265834669)
                ·
                  refine ⟨3927788337876913224688001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10474102234338435265834669 3927788337876913224688001)
                  ·
                    refine ⟨2945841253407684918516001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3927788337876913224688001 2945841253407684918516001)
                    ·
                      refine ⟨2209380940055763688887001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2945841253407684918516001 2209380940055763688887001)
                      ·
                        rfl

theorem cell23_4302754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_4302754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302754 prefixEnd_4302754 := by exact prefixLift 4302754
  have htrace : WordTrace (prefixWord ++ tailWord_4302754) baseStart_4302754 baseEnd_4302754 := by
    simpa [prefixWord, tailWord_4302754, baseEnd_4302754] using wordTrace_append hprefix tailTrace_4302754
  have hstable : (prefixWord ++ tailWord_4302754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302754).length < 2 ^ (prefixWord ++ tailWord_4302754).sum := by decide
  have hdescent : baseEnd_4302754 < baseStart_4302754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302804 : List Nat := [2, 4, 1, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4302804 : Nat := 118140960795 + 4302804 * 2 ^ 59
def prefixEnd_4302804 : Nat := 4983230072969 + 3 ^ 40 * 4302804 * 2
def baseEnd_4302804 : Nat := 2209406614088488493261771

theorem tailTrace_4302804 : CollatzResearch.WordTrace tailWord_4302804 prefixEnd_4302804 2209406614088488493261771 := by
  unfold tailWord_4302804
  simp only [CollatzResearch.WordTrace]
  refine ⟨78468077351841721631541733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104624103135788962175388977 78468077351841721631541733)
  ·
    refine ⟨14712764503470322805914075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78468077351841721631541733 14712764503470322805914075)
    ·
      refine ⟨22069146755205484208871113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14712764503470322805914075 22069146755205484208871113)
      ·
        refine ⟨16551860066404113156653335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22069146755205484208871113 16551860066404113156653335)
        ·
          refine ⟨24827790099606169734980003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16551860066404113156653335 24827790099606169734980003)
          ·
            refine ⟨37241685149409254602470005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24827790099606169734980003 37241685149409254602470005)
            ·
              refine ⟨3491407982757117618981563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37241685149409254602470005 3491407982757117618981563)
              ·
                refine ⟨5237111974135676428472345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491407982757117618981563 5237111974135676428472345)
                ·
                  refine ⟨3927833980601757321354259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5237111974135676428472345 3927833980601757321354259)
                  ·
                    refine ⟨5891750970902635982031389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927833980601757321354259 5891750970902635982031389)
                    ·
                      refine ⟨2209406614088488493261771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891750970902635982031389 2209406614088488493261771)
                      ·
                        rfl

theorem cell23_4302804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4302804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302804 prefixEnd_4302804 := by exact prefixLift 4302804
  have htrace : WordTrace (prefixWord ++ tailWord_4302804) baseStart_4302804 baseEnd_4302804 := by
    simpa [prefixWord, tailWord_4302804, baseEnd_4302804] using wordTrace_append hprefix tailTrace_4302804
  have hstable : (prefixWord ++ tailWord_4302804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302804).length < 2 ^ (prefixWord ++ tailWord_4302804).sum := by decide
  have hdescent : baseEnd_4302804 < baseStart_4302804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302830 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4302830 : Nat := 118140960795 + 4302830 * 2 ^ 59
def prefixEnd_4302830 : Nat := 4983230072969 + 3 ^ 40 * 4302830 * 2
def baseEnd_4302830 : Nat := 2209419964585505391536651

theorem tailTrace_4302830 : CollatzResearch.WordTrace tailWord_4302830 prefixEnd_4302830 2209419964585505391536651 := by
  unfold tailWord_4302830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19617137875198656212941243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104624735334392833135686629 19617137875198656212941243)
  ·
    refine ⟨29425706812797984319411865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19617137875198656212941243 29425706812797984319411865)
    ·
      refine ⟨22069280109598488239558899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29425706812797984319411865 22069280109598488239558899)
      ·
        refine ⟨33103920164397732359338349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22069280109598488239558899 33103920164397732359338349)
        ·
          refine ⟨12413970061649149634751881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33103920164397732359338349 12413970061649149634751881)
          ·
            refine ⟨9310477546236862226063911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12413970061649149634751881 9310477546236862226063911)
            ·
              refine ⟨13965716319355293339095867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9310477546236862226063911 13965716319355293339095867)
              ·
                refine ⟨20948574479032940008643801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13965716319355293339095867 20948574479032940008643801)
                ·
                  refine ⟨15711430859274705006482851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20948574479032940008643801 15711430859274705006482851)
                  ·
                    refine ⟨23567146288912057509724277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15711430859274705006482851 23567146288912057509724277)
                    ·
                      refine ⟨2209419964585505391536651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23567146288912057509724277 2209419964585505391536651)
                      ·
                        rfl

theorem cell23_4302830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4302830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302830 prefixEnd_4302830 := by exact prefixLift 4302830
  have htrace : WordTrace (prefixWord ++ tailWord_4302830) baseStart_4302830 baseEnd_4302830 := by
    simpa [prefixWord, tailWord_4302830, baseEnd_4302830] using wordTrace_append hprefix tailTrace_4302830
  have hstable : (prefixWord ++ tailWord_4302830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302830).length < 2 ^ (prefixWord ++ tailWord_4302830).sum := by decide
  have hdescent : baseEnd_4302830 < baseStart_4302830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302843 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3]
def baseStart_4302843 : Nat := 118140960795 + 4302843 * 2 ^ 59
def prefixEnd_4302843 : Nat := 4983230072969 + 3 ^ 40 * 4302843 * 2
def baseEnd_4302843 : Nat := 2209426639834013840674091

theorem tailTrace_4302843 : CollatzResearch.WordTrace tailWord_4302843 prefixEnd_4302843 2209426639834013840674091 := by
  unfold tailWord_4302843
  simp only [CollatzResearch.WordTrace]
  refine ⟨156937577150542152923753183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104625051433694768615835455 156937577150542152923753183)
  ·
    refine ⟨235406365725813229385629775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156937577150542152923753183 235406365725813229385629775)
    ·
      refine ⟨353109548588719844078444663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235406365725813229385629775 353109548588719844078444663)
      ·
        refine ⟨529664322883079766117666995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353109548588719844078444663 529664322883079766117666995)
        ·
          refine ⟨794496484324619649176500493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529664322883079766117666995 794496484324619649176500493)
          ·
            refine ⟨297936181621732368441187685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 794496484324619649176500493 297936181621732368441187685)
            ·
              refine ⟨55863034054074819082722691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 297936181621732368441187685 55863034054074819082722691)
              ·
                refine ⟨83794551081112228624084037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55863034054074819082722691 83794551081112228624084037)
                ·
                  refine ⟨15711478327708542867015757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83794551081112228624084037 15711478327708542867015757)
                  ·
                    refine ⟨5891804372890703575130909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15711478327708542867015757 5891804372890703575130909)
                    ·
                      refine ⟨2209426639834013840674091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891804372890703575130909 2209426639834013840674091)
                      ·
                        rfl

theorem cell23_4302843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 3].length) (baseStart_4302843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302843 prefixEnd_4302843 := by exact prefixLift 4302843
  have htrace : WordTrace (prefixWord ++ tailWord_4302843) baseStart_4302843 baseEnd_4302843 := by
    simpa [prefixWord, tailWord_4302843, baseEnd_4302843] using wordTrace_append hprefix tailTrace_4302843
  have hstable : (prefixWord ++ tailWord_4302843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302843).length < 2 ^ (prefixWord ++ tailWord_4302843).sum := by decide
  have hdescent : baseEnd_4302843 < baseStart_4302843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302890 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4302890 : Nat := 118140960795 + 4302890 * 2 ^ 59
def prefixEnd_4302890 : Nat := 4983230072969 + 3 ^ 40 * 4302890 * 2
def baseEnd_4302890 : Nat := 2209450773424775156786375

theorem tailTrace_4302890 : CollatzResearch.WordTrace tailWord_4302890 prefixEnd_4302890 2209450773424775156786375 := by
  unfold tailWord_4302890
  simp only [CollatzResearch.WordTrace]
  refine ⟨39234822845342969987678531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104626194254247919967142749 39234822845342969987678531)
  ·
    refine ⟨58852234268014454981517797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39234822845342969987678531 58852234268014454981517797)
    ·
      refine ⟨11034793925252710309034587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58852234268014454981517797 11034793925252710309034587)
      ·
        refine ⟨16552190887879065463551881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11034793925252710309034587 16552190887879065463551881)
        ·
          refine ⟨12414143165909299097663911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16552190887879065463551881 12414143165909299097663911)
          ·
            refine ⟨18621214748863948646495867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12414143165909299097663911 18621214748863948646495867)
            ·
              refine ⟨27931822123295922969743801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18621214748863948646495867 27931822123295922969743801)
              ·
                refine ⟨20948866592471942227307851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27931822123295922969743801 20948866592471942227307851)
                ·
                  refine ⟨31423299888707913340961777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20948866592471942227307851 31423299888707913340961777)
                  ·
                    refine ⟨23567474916530935005721333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31423299888707913340961777 23567474916530935005721333)
                    ·
                      refine ⟨2209450773424775156786375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23567474916530935005721333 2209450773424775156786375)
                      ·
                        rfl

theorem cell23_4302890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4302890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302890 prefixEnd_4302890 := by exact prefixLift 4302890
  have htrace : WordTrace (prefixWord ++ tailWord_4302890) baseStart_4302890 baseEnd_4302890 := by
    simpa [prefixWord, tailWord_4302890, baseEnd_4302890] using wordTrace_append hprefix tailTrace_4302890
  have hstable : (prefixWord ++ tailWord_4302890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302890).length < 2 ^ (prefixWord ++ tailWord_4302890).sum := by decide
  have hdescent : baseEnd_4302890 < baseStart_4302890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302934 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4302934 : Nat := 118140960795 + 4302934 * 2 ^ 59
def prefixEnd_4302934 : Nat := 4983230072969 + 3 ^ 40 * 4302934 * 2
def baseEnd_4302934 : Nat := 2209473366573572984636173

theorem tailTrace_4302934 : CollatzResearch.WordTrace tailWord_4302934 prefixEnd_4302934 2209473366573572984636173 := by
  unfold tailWord_4302934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9808806012075779716582241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104627264128808316976877237 9808806012075779716582241)
  ·
    refine ⟨7356604509056834787436681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9808806012075779716582241 7356604509056834787436681)
    ·
      refine ⟨5517453381792626090577511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7356604509056834787436681 5517453381792626090577511)
      ·
        refine ⟨8276180072688939135866267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517453381792626090577511 8276180072688939135866267)
        ·
          refine ⟨12414270109033408703799401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276180072688939135866267 12414270109033408703799401)
          ·
            refine ⟨9310702581775056527849551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12414270109033408703799401 9310702581775056527849551)
            ·
              refine ⟨13966053872662584791774327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9310702581775056527849551 13966053872662584791774327)
              ·
                refine ⟨20949080808993877187661491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13966053872662584791774327 20949080808993877187661491)
                ·
                  refine ⟨31423621213490815781492237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20949080808993877187661491 31423621213490815781492237)
                  ·
                    refine ⟨11783857955059055918059589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31423621213490815781492237 11783857955059055918059589)
                    ·
                      refine ⟨2209473366573572984636173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11783857955059055918059589 2209473366573572984636173)
                      ·
                        rfl

theorem cell23_4302934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4302934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302934 prefixEnd_4302934 := by exact prefixLift 4302934
  have htrace : WordTrace (prefixWord ++ tailWord_4302934) baseStart_4302934 baseEnd_4302934 := by
    simpa [prefixWord, tailWord_4302934, baseEnd_4302934] using wordTrace_append hprefix tailTrace_4302934
  have hstable : (prefixWord ++ tailWord_4302934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302934).length < 2 ^ (prefixWord ++ tailWord_4302934).sum := by decide
  have hdescent : baseEnd_4302934 < baseStart_4302934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302944 : List Nat := [2, 1, 1, 3, 2, 4, 2, 3, 1, 4]
def baseStart_4302944 : Nat := 118140960795 + 4302944 * 2 ^ 59
def prefixEnd_4302944 : Nat := 4983230072969 + 3 ^ 40 * 4302944 * 2
def baseEnd_4302944 : Nat := 736492833793372648503709

theorem tailTrace_4302944 : CollatzResearch.WordTrace tailWord_4302944 prefixEnd_4302944 736492833793372648503709 := by
  unfold tailWord_4302944
  simp only [CollatzResearch.WordTrace]
  refine ⟨78470630461588123586589943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104627507282117498115453257 78470630461588123586589943)
  ·
    refine ⟨117705945692382185379884915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78470630461588123586589943 117705945692382185379884915)
    ·
      refine ⟨176558918538573278069827373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117705945692382185379884915 176558918538573278069827373)
      ·
        refine ⟨66209594451964979276185265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176558918538573278069827373 66209594451964979276185265)
        ·
          refine ⟨49657195838973734457138949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66209594451964979276185265 49657195838973734457138949)
          ·
            refine ⟨9310724219807575210713553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49657195838973734457138949 9310724219807575210713553)
            ·
              refine ⟨6983043164855681408035165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310724219807575210713553 6983043164855681408035165)
              ·
                refine ⟨2618641186820880528013187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6983043164855681408035165 2618641186820880528013187)
                ·
                  refine ⟨3927961780231320792019781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618641186820880528013187 3927961780231320792019781)
                  ·
                    refine ⟨736492833793372648503709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3927961780231320792019781 736492833793372648503709)
                    ·
                      rfl

theorem cell23_4302944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 3, 1, 4].length) (baseStart_4302944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302944 prefixEnd_4302944 := by exact prefixLift 4302944
  have htrace : WordTrace (prefixWord ++ tailWord_4302944) baseStart_4302944 baseEnd_4302944 := by
    simpa [prefixWord, tailWord_4302944, baseEnd_4302944] using wordTrace_append hprefix tailTrace_4302944
  have hstable : (prefixWord ++ tailWord_4302944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302944).length < 2 ^ (prefixWord ++ tailWord_4302944).sum := by decide
  have hdescent : baseEnd_4302944 < baseStart_4302944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302967 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 3]
def baseStart_4302967 : Nat := 118140960795 + 4302967 * 2 ^ 59
def prefixEnd_4302967 : Nat := 4983230072969 + 3 ^ 40 * 4302967 * 2
def baseEnd_4302967 : Nat := 2209490311435171355523521

theorem tailTrace_4302967 : CollatzResearch.WordTrace tailWord_4302967 prefixEnd_4302967 2209490311435171355523521 := by
  unfold tailWord_4302967
  simp only [CollatzResearch.WordTrace]
  refine ⟨156942099802092922101267155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104628066534728614734178103 156942099802092922101267155)
  ·
    refine ⟨235413149703139383151900733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156942099802092922101267155 235413149703139383151900733)
    ·
      refine ⟨88279931138677268681962775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235413149703139383151900733 88279931138677268681962775)
      ·
        refine ⟨132419896708015903022944163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88279931138677268681962775 132419896708015903022944163)
        ·
          refine ⟨198629845062023854534416245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132419896708015903022944163 198629845062023854534416245)
          ·
            refine ⟨18621547974564736362601523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 198629845062023854534416245 18621547974564736362601523)
            ·
              refine ⟨27932321961847104543902285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18621547974564736362601523 27932321961847104543902285)
              ·
                refine ⟨10474620735692664203963357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27932321961847104543902285 10474620735692664203963357)
                ·
                  refine ⟨3927982775884749076486259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10474620735692664203963357 3927982775884749076486259)
                  ·
                    refine ⟨5891974163827123614729389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927982775884749076486259 5891974163827123614729389)
                    ·
                      refine ⟨2209490311435171355523521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891974163827123614729389 2209490311435171355523521)
                      ·
                        rfl

theorem cell23_4302967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_4302967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302967 prefixEnd_4302967 := by exact prefixLift 4302967
  have htrace : WordTrace (prefixWord ++ tailWord_4302967) baseStart_4302967 baseEnd_4302967 := by
    simpa [prefixWord, tailWord_4302967, baseEnd_4302967] using wordTrace_append hprefix tailTrace_4302967
  have hstable : (prefixWord ++ tailWord_4302967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302967).length < 2 ^ (prefixWord ++ tailWord_4302967).sum := by decide
  have hdescent : baseEnd_4302967 < baseStart_4302967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302984 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_4302984 : Nat := 118140960795 + 4302984 * 2 ^ 59
def prefixEnd_4302984 : Nat := 4983230072969 + 3 ^ 40 * 4302984 * 2
def baseEnd_4302984 : Nat := 2209499040606297789010943

theorem tailTrace_4302984 : CollatzResearch.WordTrace tailWord_4302984 prefixEnd_4302984 2209499040606297789010943 := by
  unfold tailWord_4302984
  simp only [CollatzResearch.WordTrace]
  refine ⟨78471359921515667002318003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104628479895354222669757337 78471359921515667002318003)
  ·
    refine ⟨117707039882273500503477005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78471359921515667002318003 117707039882273500503477005)
    ·
      refine ⟨44140139955852562688803877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117707039882273500503477005 44140139955852562688803877)
      ·
        refine ⟨8276276241722355504150727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44140139955852562688803877 8276276241722355504150727)
        ·
          refine ⟨12414414362583533256226091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8276276241722355504150727 12414414362583533256226091)
          ·
            refine ⟨18621621543875299884339137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12414414362583533256226091 18621621543875299884339137)
            ·
              refine ⟨13966216157906474913254353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18621621543875299884339137 13966216157906474913254353)
              ·
                refine ⟨10474662118429856184940765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13966216157906474913254353 10474662118429856184940765)
                ·
                  refine ⟨3927998294411196069352787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10474662118429856184940765 3927998294411196069352787)
                  ·
                    refine ⟨5891997441616794104029181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3927998294411196069352787 5891997441616794104029181)
                    ·
                      refine ⟨2209499040606297789010943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5891997441616794104029181 2209499040606297789010943)
                      ·
                        rfl

theorem cell23_4302984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_4302984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302984 prefixEnd_4302984 := by exact prefixLift 4302984
  have htrace : WordTrace (prefixWord ++ tailWord_4302984) baseStart_4302984 baseEnd_4302984 := by
    simpa [prefixWord, tailWord_4302984, baseEnd_4302984] using wordTrace_append hprefix tailTrace_4302984
  have hstable : (prefixWord ++ tailWord_4302984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302984).length < 2 ^ (prefixWord ++ tailWord_4302984).sum := by decide
  have hdescent : baseEnd_4302984 < baseStart_4302984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4302994 : List Nat := [3, 2, 3, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_4302994 : Nat := 118140960795 + 4302994 * 2 ^ 59
def prefixEnd_4302994 : Nat := 4983230072969 + 3 ^ 40 * 4302994 * 2
def baseEnd_4302994 : Nat := 2209504175412842749885897

theorem tailTrace_4302994 : CollatzResearch.WordTrace tailWord_4302994 prefixEnd_4302994 2209504175412842749885897 := by
  unfold tailWord_4302994
  simp only [CollatzResearch.WordTrace]
  refine ⟨39235771143248776428125009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104628723048663403808333357 39235771143248776428125009)
  ·
    refine ⟨29426828357436582321093757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39235771143248776428125009 29426828357436582321093757)
    ·
      refine ⟨11035060634038718370410159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29426828357436582321093757 11035060634038718370410159)
      ·
        refine ⟨16552590951058077555615239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035060634038718370410159 16552590951058077555615239)
        ·
          refine ⟨24828886426587116333422859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16552590951058077555615239 24828886426587116333422859)
          ·
            refine ⟨37243329639880674500134289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24828886426587116333422859 37243329639880674500134289)
            ·
              refine ⟨27932497229910505875100717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37243329639880674500134289 27932497229910505875100717)
              ·
                refine ⟨10474686461216439703162769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27932497229910505875100717 10474686461216439703162769)
                ·
                  refine ⟨7856014845912329777372077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10474686461216439703162769 7856014845912329777372077)
                  ·
                    refine ⟨2946005567217123666514529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7856014845912329777372077 2946005567217123666514529)
                    ·
                      refine ⟨2209504175412842749885897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946005567217123666514529 2209504175412842749885897)
                      ·
                        rfl

theorem cell23_4302994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_4302994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4302994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4302994 prefixEnd_4302994 := by exact prefixLift 4302994
  have htrace : WordTrace (prefixWord ++ tailWord_4302994) baseStart_4302994 baseEnd_4302994 := by
    simpa [prefixWord, tailWord_4302994, baseEnd_4302994] using wordTrace_append hprefix tailTrace_4302994
  have hstable : (prefixWord ++ tailWord_4302994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4302994).length < 2 ^ (prefixWord ++ tailWord_4302994).sum := by decide
  have hdescent : baseEnd_4302994 < baseStart_4302994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4302994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303018 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4303018 : Nat := 118140960795 + 4303018 * 2 ^ 59
def prefixEnd_4303018 : Nat := 4983230072969 + 3 ^ 40 * 4303018 * 2
def baseEnd_4303018 : Nat := 2209516498948550655985787

theorem tailTrace_4303018 : CollatzResearch.WordTrace tailWord_4303018 prefixEnd_4303018 2209516498948550655985787 := by
  unfold tailWord_4303018
  simp only [CollatzResearch.WordTrace]
  refine ⟨39235989981227039452843427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104629306616605438540915805 39235989981227039452843427)
  ·
    refine ⟨58853984971840559179265141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39235989981227039452843427 58853984971840559179265141)
    ·
      refine ⟨5517561091110052423056107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58853984971840559179265141 5517561091110052423056107)
      ·
        refine ⟨8276341636665078634584161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5517561091110052423056107 8276341636665078634584161)
        ·
          refine ⟨6207256227498808975938121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8276341636665078634584161 6207256227498808975938121)
          ·
            refine ⟨4655442170624106731953591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6207256227498808975938121 4655442170624106731953591)
            ·
              refine ⟨6983163255936160097930387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655442170624106731953591 6983163255936160097930387)
              ·
                refine ⟨10474744883904240146895581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6983163255936160097930387 10474744883904240146895581)
                ·
                  refine ⟨3928029331464090055085843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10474744883904240146895581 3928029331464090055085843)
                  ·
                    refine ⟨5892043997196135082628765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3928029331464090055085843 5892043997196135082628765)
                    ·
                      refine ⟨2209516498948550655985787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892043997196135082628765 2209516498948550655985787)
                      ·
                        rfl

theorem cell23_4303018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4303018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303018 prefixEnd_4303018 := by exact prefixLift 4303018
  have htrace : WordTrace (prefixWord ++ tailWord_4303018) baseStart_4303018 baseEnd_4303018 := by
    simpa [prefixWord, tailWord_4303018, baseEnd_4303018] using wordTrace_append hprefix tailTrace_4303018
  have hstable : (prefixWord ++ tailWord_4303018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303018).length < 2 ^ (prefixWord ++ tailWord_4303018).sum := by decide
  have hdescent : baseEnd_4303018 < baseStart_4303018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303034 : List Nat := [3, 1, 1, 1, 2, 2, 6, 1, 2, 4]
def baseStart_4303034 : Nat := 118140960795 + 4303034 * 2 ^ 59
def prefixEnd_4303034 : Nat := 4983230072969 + 3 ^ 40 * 4303034 * 2
def baseEnd_4303034 : Nat := 736508238213007531128571

theorem tailTrace_4303034 : CollatzResearch.WordTrace tailWord_4303034 prefixEnd_4303034 736508238213007531128571 := by
  unfold tailWord_4303034
  simp only [CollatzResearch.WordTrace]
  refine ⟨39236135873212548135989039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104629695661900128362637437 39236135873212548135989039)
  ·
    refine ⟨58854203809818822203983559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39236135873212548135989039 58854203809818822203983559)
    ·
      refine ⟨88281305714728233305975339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58854203809818822203983559 88281305714728233305975339)
      ·
        refine ⟨132421958572092349958963009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88281305714728233305975339 132421958572092349958963009)
        ·
          refine ⟨99316468929069262469222257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132421958572092349958963009 99316468929069262469222257)
          ·
            refine ⟨74487351696801946851916693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99316468929069262469222257 74487351696801946851916693)
            ·
              refine ⟨3491594610787591258683595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 74487351696801946851916693 3491594610787591258683595)
              ·
                refine ⟨5237391916181386888025393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3491594610787591258683595 5237391916181386888025393)
                ·
                  refine ⟨3928043937136040166019045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5237391916181386888025393 3928043937136040166019045)
                  ·
                    refine ⟨736508238213007531128571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928043937136040166019045 736508238213007531128571)
                    ·
                      rfl

theorem cell23_4303034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 1, 2, 4].length) (baseStart_4303034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303034 prefixEnd_4303034 := by exact prefixLift 4303034
  have htrace : WordTrace (prefixWord ++ tailWord_4303034) baseStart_4303034 baseEnd_4303034 := by
    simpa [prefixWord, tailWord_4303034, baseEnd_4303034] using wordTrace_append hprefix tailTrace_4303034
  have hstable : (prefixWord ++ tailWord_4303034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303034).length < 2 ^ (prefixWord ++ tailWord_4303034).sum := by decide
  have hdescent : baseEnd_4303034 < baseStart_4303034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303044 : List Nat := [2, 3, 3, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_4303044 : Nat := 118140960795 + 4303044 * 2 ^ 59
def prefixEnd_4303044 : Nat := 4983230072969 + 3 ^ 40 * 4303044 * 2
def baseEnd_4303044 : Nat := 2209529849445567554260667

theorem tailTrace_4303044 : CollatzResearch.WordTrace tailWord_4303044 prefixEnd_4303044 2209529849445567554260667 := by
  unfold tailWord_4303044
  simp only [CollatzResearch.WordTrace]
  refine ⟨78472454111406982125910093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104629938815209309501213457 78472454111406982125910093)
  ·
    refine ⟨29427170291777618297216285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78472454111406982125910093 29427170291777618297216285)
    ·
      refine ⟨11035188859416606861456107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29427170291777618297216285 11035188859416606861456107)
      ·
        refine ⟨16552783289124910292184161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035188859416606861456107 16552783289124910292184161)
        ·
          refine ⟨12414587466843682719138121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16552783289124910292184161 12414587466843682719138121)
          ·
            refine ⟨9310940600132762039353591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12414587466843682719138121 9310940600132762039353591)
            ·
              refine ⟨13966410900199143059030387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9310940600132762039353591 13966410900199143059030387)
              ·
                refine ⟨20949616350298714588545581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13966410900199143059030387 20949616350298714588545581)
                ·
                  refine ⟨7856106131362017970704593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20949616350298714588545581 7856106131362017970704593)
                  ·
                    refine ⟨5892079598521513478028445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7856106131362017970704593 5892079598521513478028445)
                    ·
                      refine ⟨2209529849445567554260667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892079598521513478028445 2209529849445567554260667)
                      ·
                        rfl

theorem cell23_4303044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_4303044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303044 prefixEnd_4303044 := by exact prefixLift 4303044
  have htrace : WordTrace (prefixWord ++ tailWord_4303044) baseStart_4303044 baseEnd_4303044 := by
    simpa [prefixWord, tailWord_4303044, baseEnd_4303044] using wordTrace_append hprefix tailTrace_4303044
  have hstable : (prefixWord ++ tailWord_4303044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303044).length < 2 ^ (prefixWord ++ tailWord_4303044).sum := by decide
  have hdescent : baseEnd_4303044 < baseStart_4303044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303057 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_4303057 : Nat := 118140960795 + 4303057 * 2 ^ 59
def prefixEnd_4303057 : Nat := 4983230072969 + 3 ^ 40 * 4303057 * 2
def baseEnd_4303057 : Nat := 2209536524694076003398107

theorem tailTrace_4303057 : CollatzResearch.WordTrace tailWord_4303057 prefixEnd_4303057 2209536524694076003398107 := by
  unfold tailWord_4303057
  simp only [CollatzResearch.WordTrace]
  refine ⟨156945382371766867472043425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104630254914511244981362283 156945382371766867472043425)
  ·
    refine ⟨117709036778825150604032569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156945382371766867472043425 117709036778825150604032569)
    ·
      refine ⟨88281777584118862953024427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117709036778825150604032569 88281777584118862953024427)
      ·
        refine ⟨132422666376178294429536641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88281777584118862953024427 132422666376178294429536641)
        ·
          refine ⟨99316999782133720822152481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132422666376178294429536641 99316999782133720822152481)
          ·
            refine ⟨74487749836600290616614361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99316999782133720822152481 74487749836600290616614361)
            ·
              refine ⟨55865812377450217962460771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74487749836600290616614361 55865812377450217962460771)
              ·
                refine ⟨83798718566175326943691157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55865812377450217962460771 83798718566175326943691157)
                ·
                  refine ⟨3928064932789468450485523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83798718566175326943691157 3928064932789468450485523)
                  ·
                    refine ⟨5892097399184202675728285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3928064932789468450485523 5892097399184202675728285)
                    ·
                      refine ⟨2209536524694076003398107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892097399184202675728285 2209536524694076003398107)
                      ·
                        rfl

theorem cell23_4303057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_4303057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303057 prefixEnd_4303057 := by exact prefixLift 4303057
  have htrace : WordTrace (prefixWord ++ tailWord_4303057) baseStart_4303057 baseEnd_4303057 := by
    simpa [prefixWord, tailWord_4303057, baseEnd_4303057] using wordTrace_append hprefix tailTrace_4303057
  have hstable : (prefixWord ++ tailWord_4303057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303057).length < 2 ^ (prefixWord ++ tailWord_4303057).sum := by decide
  have hdescent : baseEnd_4303057 < baseStart_4303057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303061 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4303061 : Nat := 118140960795 + 4303061 * 2 ^ 59
def prefixEnd_4303061 : Nat := 4983230072969 + 3 ^ 40 * 4303061 * 2
def baseEnd_4303061 : Nat := 2209538578616693987748089

theorem tailTrace_4303061 : CollatzResearch.WordTrace tailWord_4303061 prefixEnd_4303061 2209538578616693987748089 := by
  unfold tailWord_4303061
  simp only [CollatzResearch.WordTrace]
  refine ⟨156945528263752376155189037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104630352175834917436792691 156945528263752376155189037)
  ·
    refine ⟨58854573098907141058195889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156945528263752376155189037 58854573098907141058195889)
    ·
      refine ⟨44140929824180355793646917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58854573098907141058195889 44140929824180355793646917)
      ·
        refine ⟨8276424342033816711308797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44140929824180355793646917 8276424342033816711308797)
        ·
          refine ⟨3103659128262681266740799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8276424342033816711308797 3103659128262681266740799)
          ·
            refine ⟨4655488692394021900111199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3103659128262681266740799 4655488692394021900111199)
            ·
              refine ⟨6983233038591032850166799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4655488692394021900111199 6983233038591032850166799)
              ·
                refine ⟨10474849557886549275250199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6983233038591032850166799 10474849557886549275250199)
                ·
                  refine ⟨15712274336829823912875299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10474849557886549275250199 15712274336829823912875299)
                  ·
                    refine ⟨23568411505244735869312949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15712274336829823912875299 23568411505244735869312949)
                    ·
                      refine ⟨2209538578616693987748089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23568411505244735869312949 2209538578616693987748089)
                      ·
                        rfl

theorem cell23_4303061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4303061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303061 prefixEnd_4303061 := by exact prefixLift 4303061
  have htrace : WordTrace (prefixWord ++ tailWord_4303061) baseStart_4303061 baseEnd_4303061 := by
    simpa [prefixWord, tailWord_4303061, baseEnd_4303061] using wordTrace_append hprefix tailTrace_4303061
  have hstable : (prefixWord ++ tailWord_4303061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303061).length < 2 ^ (prefixWord ++ tailWord_4303061).sum := by decide
  have hdescent : baseEnd_4303061 < baseStart_4303061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303067 : List Nat := [1, 1, 1, 1, 1, 1, 1, 6, 5, 3, 2]
def baseStart_4303067 : Nat := 118140960795 + 4303067 * 2 ^ 59
def prefixEnd_4303067 : Nat := 4983230072969 + 3 ^ 40 * 4303067 * 2
def baseEnd_4303067 : Nat := 2209541659500620964273061

theorem tailTrace_4303067 : CollatzResearch.WordTrace tailWord_4303067 prefixEnd_4303067 2209541659500620964273061 := by
  unfold tailWord_4303067
  simp only [CollatzResearch.WordTrace]
  refine ⟨156945747101730639179907455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104630498067820426119938303 156945747101730639179907455)
  ·
    refine ⟨235418620652595958769861183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156945747101730639179907455 235418620652595958769861183)
    ·
      refine ⟨353127930978893938154791775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235418620652595958769861183 353127930978893938154791775)
      ·
        refine ⟨529691896468340907232187663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353127930978893938154791775 529691896468340907232187663)
        ·
          refine ⟨794537844702511360848281495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529691896468340907232187663 794537844702511360848281495)
          ·
            refine ⟨1191806767053767041272422243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794537844702511360848281495 1191806767053767041272422243)
            ·
              refine ⟨1787710150580650561908633365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191806767053767041272422243 1787710150580650561908633365)
              ·
                refine ⟨83798913308467995089467189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1787710150580650561908633365 83798913308467995089467189)
                ·
                  refine ⟨7856148122668874539637549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83798913308467995089467189 7856148122668874539637549)
                  ·
                    refine ⟨2946055546000827952364081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7856148122668874539637549 2946055546000827952364081)
                    ·
                      refine ⟨2209541659500620964273061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946055546000827952364081 2209541659500620964273061)
                      ·
                        rfl

theorem cell23_4303067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 3, 2].length) (baseStart_4303067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303067 prefixEnd_4303067 := by exact prefixLift 4303067
  have htrace : WordTrace (prefixWord ++ tailWord_4303067) baseStart_4303067 baseEnd_4303067 := by
    simpa [prefixWord, tailWord_4303067, baseEnd_4303067] using wordTrace_append hprefix tailTrace_4303067
  have hstable : (prefixWord ++ tailWord_4303067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303067).length < 2 ^ (prefixWord ++ tailWord_4303067).sum := by decide
  have hdescent : baseEnd_4303067 < baseStart_4303067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303068 : List Nat := [2, 2, 5, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4303068 : Nat := 118140960795 + 4303068 * 2 ^ 59
def prefixEnd_4303068 : Nat := 4983230072969 + 3 ^ 40 * 4303068 * 2
def baseEnd_4303068 : Nat := 736514057660425153453519

theorem tailTrace_4303068 : CollatzResearch.WordTrace tailWord_4303068 prefixEnd_4303068 736514057660425153453519 := by
  unfold tailWord_4303068
  simp only [CollatzResearch.WordTrace]
  refine ⟨78472891787363508175346929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104630522383151344233795905 78472891787363508175346929)
  ·
    refine ⟨58854668840522631131510197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78472891787363508175346929 58854668840522631131510197)
    ·
      refine ⟨5517625203798996668579081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58854668840522631131510197 5517625203798996668579081)
      ·
        refine ⟨4138218902849247501434311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5517625203798996668579081 4138218902849247501434311)
        ·
          refine ⟨6207328354273871252151467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138218902849247501434311 6207328354273871252151467)
          ·
            refine ⟨9310992531410806878227201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207328354273871252151467 9310992531410806878227201)
            ·
              refine ⟨6983244398558105158670401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9310992531410806878227201 6983244398558105158670401)
              ·
                refine ⟨5237433298918578869002801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983244398558105158670401 5237433298918578869002801)
                ·
                  refine ⟨3928074974188934151752101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5237433298918578869002801 3928074974188934151752101)
                  ·
                    refine ⟨736514057660425153453519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928074974188934151752101 736514057660425153453519)
                    ·
                      rfl

theorem cell23_4303068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4303068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303068 prefixEnd_4303068 := by exact prefixLift 4303068
  have htrace : WordTrace (prefixWord ++ tailWord_4303068) baseStart_4303068 baseEnd_4303068 := by
    simpa [prefixWord, tailWord_4303068, baseEnd_4303068] using wordTrace_append hprefix tailTrace_4303068
  have hstable : (prefixWord ++ tailWord_4303068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303068).length < 2 ^ (prefixWord ++ tailWord_4303068).sum := by decide
  have hdescent : baseEnd_4303068 < baseStart_4303068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303075 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4303075 : Nat := 118140960795 + 4303075 * 2 ^ 59
def prefixEnd_4303075 : Nat := 4983230072969 + 3 ^ 40 * 4303075 * 2
def baseEnd_4303075 : Nat := 2209545767345856932973025

theorem tailTrace_4303075 : CollatzResearch.WordTrace tailWord_4303075 prefixEnd_4303075 2209545767345856932973025 := by
  unfold tailWord_4303075
  simp only [CollatzResearch.WordTrace]
  refine ⟨156946038885701656546198679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104630692590467771030799119 156946038885701656546198679)
  ·
    refine ⟨235419058328552484819298019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156946038885701656546198679 235419058328552484819298019)
    ·
      refine ⟨353128587492828727228947029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235419058328552484819298019 353128587492828727228947029)
      ·
        refine ⟨4138225634681586647214223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 353128587492828727228947029 4138225634681586647214223)
        ·
          refine ⟨6207338452022379970821335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4138225634681586647214223 6207338452022379970821335)
          ·
            refine ⟨9311007678033569956232003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6207338452022379970821335 9311007678033569956232003)
            ·
              refine ⟨13966511517050354934348005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311007678033569956232003 13966511517050354934348005)
              ·
                refine ⟨2618720909446941550190251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13966511517050354934348005 2618720909446941550190251)
                ·
                  refine ⟨3928081364170412325285377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2618720909446941550190251 3928081364170412325285377)
                  ·
                    refine ⟨2946061023127809243964033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928081364170412325285377 2946061023127809243964033)
                    ·
                      refine ⟨2209545767345856932973025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946061023127809243964033 2209545767345856932973025)
                      ·
                        rfl

theorem cell23_4303075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4303075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303075 prefixEnd_4303075 := by exact prefixLift 4303075
  have htrace : WordTrace (prefixWord ++ tailWord_4303075) baseStart_4303075 baseEnd_4303075 := by
    simpa [prefixWord, tailWord_4303075, baseEnd_4303075] using wordTrace_append hprefix tailTrace_4303075
  have hstable : (prefixWord ++ tailWord_4303075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303075).length < 2 ^ (prefixWord ++ tailWord_4303075).sum := by decide
  have hdescent : baseEnd_4303075 < baseStart_4303075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303114 : List Nat := [3, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2]
def baseStart_4303114 : Nat := 118140960795 + 4303114 * 2 ^ 59
def prefixEnd_4303114 : Nat := 4983230072969 + 3 ^ 40 * 4303114 * 2
def baseEnd_4303114 : Nat := 2209565793091382280385345

theorem tailTrace_4303114 : CollatzResearch.WordTrace tailWord_4303114 prefixEnd_4303114 2209565793091382280385345 := by
  unfold tailWord_4303114
  simp only [CollatzResearch.WordTrace]
  refine ⟨39236865333140091551717099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104631640888373577471245597 39236865333140091551717099)
  ·
    refine ⟨58855297999710137327575649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39236865333140091551717099 58855297999710137327575649)
    ·
      refine ⟨44141473499782602995681737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58855297999710137327575649 44141473499782602995681737)
      ·
        refine ⟨33106105124836952246761303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44141473499782602995681737 33106105124836952246761303)
        ·
          refine ⟨49659157687255428370141955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33106105124836952246761303 49659157687255428370141955)
          ·
            refine ⟨74488736530883142555212933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49659157687255428370141955 74488736530883142555212933)
            ·
              refine ⟨13966638099540589229102425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74488736530883142555212933 13966638099540589229102425)
              ·
                refine ⟨10474978574655441921826819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13966638099540589229102425 10474978574655441921826819)
                ·
                  refine ⟨15712467861983162882740229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10474978574655441921826819 15712467861983162882740229)
                  ·
                    refine ⟨2946087724121843040513793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15712467861983162882740229 2946087724121843040513793)
                    ·
                      refine ⟨2209565793091382280385345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946087724121843040513793 2209565793091382280385345)
                      ·
                        rfl

theorem cell23_4303114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_4303114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303114 prefixEnd_4303114 := by exact prefixLift 4303114
  have htrace : WordTrace (prefixWord ++ tailWord_4303114) baseStart_4303114 baseEnd_4303114 := by
    simpa [prefixWord, tailWord_4303114, baseEnd_4303114] using wordTrace_append hprefix tailTrace_4303114
  have hstable : (prefixWord ++ tailWord_4303114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303114).length < 2 ^ (prefixWord ++ tailWord_4303114).sum := by decide
  have hdescent : baseEnd_4303114 < baseStart_4303114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303127 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4303127 : Nat := 118140960795 + 4303127 * 2 ^ 59
def prefixEnd_4303127 : Nat := 4983230072969 + 3 ^ 40 * 4303127 * 2
def baseEnd_4303127 : Nat := 2209572468339890729522785

theorem tailTrace_4303127 : CollatzResearch.WordTrace tailWord_4303127 prefixEnd_4303127 2209572468339890729522785 := by
  unfold tailWord_4303127
  simp only [CollatzResearch.WordTrace]
  refine ⟨156947935481513269427091635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104631956987675512951394423 156947935481513269427091635)
  ·
    refine ⟨235421903222269904140637453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156947935481513269427091635 235421903222269904140637453)
    ·
      refine ⟨88283213708351214052739045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235421903222269904140637453 88283213708351214052739045)
      ·
        refine ⟨16553102570315852634888571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88283213708351214052739045 16553102570315852634888571)
        ·
          refine ⟨24829653855473778952332857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553102570315852634888571 24829653855473778952332857)
          ·
            refine ⟨18622240391605334214249643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24829653855473778952332857 18622240391605334214249643)
            ·
              refine ⟨27933360587408001321374465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18622240391605334214249643 27933360587408001321374465)
              ·
                refine ⟨20950020440556000991030849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27933360587408001321374465 20950020440556000991030849)
                ·
                  refine ⟨15712515330417000743273137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20950020440556000991030849 15712515330417000743273137)
                  ·
                    refine ⟨11784386497812750557454853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15712515330417000743273137 11784386497812750557454853)
                    ·
                      refine ⟨2209572468339890729522785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11784386497812750557454853 2209572468339890729522785)
                      ·
                        rfl

theorem cell23_4303127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4303127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303127 prefixEnd_4303127 := by exact prefixLift 4303127
  have htrace : WordTrace (prefixWord ++ tailWord_4303127) baseStart_4303127 baseEnd_4303127 := by
    simpa [prefixWord, tailWord_4303127, baseEnd_4303127] using wordTrace_append hprefix tailTrace_4303127
  have hstable : (prefixWord ++ tailWord_4303127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303127).length < 2 ^ (prefixWord ++ tailWord_4303127).sum := by decide
  have hdescent : baseEnd_4303127 < baseStart_4303127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303131 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 2, 2, 2]
def baseStart_4303131 : Nat := 118140960795 + 4303131 * 2 ^ 59
def prefixEnd_4303131 : Nat := 4983230072969 + 3 ^ 40 * 4303131 * 2
def baseEnd_4303131 : Nat := 2209574522262508713872767

theorem tailTrace_4303131 : CollatzResearch.WordTrace tailWord_4303131 prefixEnd_4303131 2209574522262508713872767 := by
  unfold tailWord_4303131
  simp only [CollatzResearch.WordTrace]
  refine ⟨156948081373498778110237247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104632054248999185406824831 156948081373498778110237247)
  ·
    refine ⟨235422122060248167165355871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156948081373498778110237247 235422122060248167165355871)
    ·
      refine ⟨353133183090372250748033807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235422122060248167165355871 353133183090372250748033807)
      ·
        refine ⟨529699774635558376122050711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353133183090372250748033807 529699774635558376122050711)
        ·
          refine ⟨794549661953337564183076067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529699774635558376122050711 794549661953337564183076067)
          ·
            refine ⟨1191824492930006346274614101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794549661953337564183076067 1191824492930006346274614101)
            ·
              refine ⟨6983346638261755935202817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1191824492930006346274614101 6983346638261755935202817)
              ·
                refine ⟨5237509978696316951402113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983346638261755935202817 5237509978696316951402113)
                ·
                  refine ⟨3928132484022237713551585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5237509978696316951402113 3928132484022237713551585)
                  ·
                    refine ⟨2946099363016678285163689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928132484022237713551585 2946099363016678285163689)
                    ·
                      refine ⟨2209574522262508713872767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946099363016678285163689 2209574522262508713872767)
                      ·
                        rfl

theorem cell23_4303131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2, 2].length) (baseStart_4303131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303131 prefixEnd_4303131 := by exact prefixLift 4303131
  have htrace : WordTrace (prefixWord ++ tailWord_4303131) baseStart_4303131 baseEnd_4303131 := by
    simpa [prefixWord, tailWord_4303131, baseEnd_4303131] using wordTrace_append hprefix tailTrace_4303131
  have hstable : (prefixWord ++ tailWord_4303131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303131).length < 2 ^ (prefixWord ++ tailWord_4303131).sum := by decide
  have hdescent : baseEnd_4303131 < baseStart_4303131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303167 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 2, 5]
def baseStart_4303167 : Nat := 118140960795 + 4303167 * 2 ^ 59
def prefixEnd_4303167 : Nat := 4983230072969 + 3 ^ 40 * 4303167 * 2
def baseEnd_4303167 : Nat := 736531002522023524340867

theorem tailTrace_4303167 : CollatzResearch.WordTrace tailWord_4303167 prefixEnd_4303167 736531002522023524340867 := by
  unfold tailWord_4303167
  simp only [CollatzResearch.WordTrace]
  refine ⟨156949394401368356258547755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104632929600912237505698503 156949394401368356258547755)
  ·
    refine ⟨235424091602052534387821633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156949394401368356258547755 235424091602052534387821633)
    ·
      refine ⟨176568068701539400790866225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235424091602052534387821633 176568068701539400790866225)
      ·
        refine ⟨132426051526154550593149669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176568068701539400790866225 132426051526154550593149669)
        ·
          refine ⟨24829884661153978236215563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132426051526154550593149669 24829884661153978236215563)
          ·
            refine ⟨37244826991730967354323345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24829884661153978236215563 37244826991730967354323345)
            ·
              refine ⟨27933620243798225515742509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37244826991730967354323345 27933620243798225515742509)
              ·
                refine ⟨10475107591424334568403441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27933620243798225515742509 10475107591424334568403441)
                ·
                  refine ⟨7856330693568250926302581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10475107591424334568403441 7856330693568250926302581)
                  ·
                    refine ⟨736531002522023524340867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7856330693568250926302581 736531002522023524340867)
                    ·
                      rfl

theorem cell23_4303167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 2, 5].length) (baseStart_4303167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303167 prefixEnd_4303167 := by exact prefixLift 4303167
  have htrace : WordTrace (prefixWord ++ tailWord_4303167) baseStart_4303167 baseEnd_4303167 := by
    simpa [prefixWord, tailWord_4303167, baseEnd_4303167] using wordTrace_append hprefix tailTrace_4303167
  have hstable : (prefixWord ++ tailWord_4303167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303167).length < 2 ^ (prefixWord ++ tailWord_4303167).sum := by decide
  have hdescent : baseEnd_4303167 < baseStart_4303167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303204 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_4303204 : Nat := 118140960795 + 4303204 * 2 ^ 59
def prefixEnd_4303204 : Nat := 4983230072969 + 3 ^ 40 * 4303204 * 2
def baseEnd_4303204 : Nat := 2209612006350286928259931

theorem tailTrace_4303204 : CollatzResearch.WordTrace tailWord_4303204 prefixEnd_4303204 2209612006350286928259931 := by
  unfold tailWord_4303204
  simp only [CollatzResearch.WordTrace]
  refine ⟨78475371951117155788822333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104633829268156207718429777 78475371951117155788822333)
  ·
    refine ⟨29428264481668933420808375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78475371951117155788822333 29428264481668933420808375)
    ·
      refine ⟨44142396722503400131212563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29428264481668933420808375 44142396722503400131212563)
      ·
        refine ⟨66213595083755100196818845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44142396722503400131212563 66213595083755100196818845)
        ·
          refine ⟨24830098156408162573807067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66213595083755100196818845 24830098156408162573807067)
          ·
            refine ⟨37245147234612243860710601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24830098156408162573807067 37245147234612243860710601)
            ·
              refine ⟨27933860425959182895532951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37245147234612243860710601 27933860425959182895532951)
              ·
                refine ⟨41900790638938774343299427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27933860425959182895532951 41900790638938774343299427)
                ·
                  refine ⟨62851185958408161514949141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41900790638938774343299427 62851185958408161514949141)
                  ·
                    refine ⟨2946149341800382571013241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 62851185958408161514949141 2946149341800382571013241)
                    ·
                      refine ⟨2209612006350286928259931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946149341800382571013241 2209612006350286928259931)
                      ·
                        rfl

theorem cell23_4303204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_4303204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303204 prefixEnd_4303204 := by exact prefixLift 4303204
  have htrace : WordTrace (prefixWord ++ tailWord_4303204) baseStart_4303204 baseEnd_4303204 := by
    simpa [prefixWord, tailWord_4303204, baseEnd_4303204] using wordTrace_append hprefix tailTrace_4303204
  have hstable : (prefixWord ++ tailWord_4303204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303204).length < 2 ^ (prefixWord ++ tailWord_4303204).sum := by decide
  have hdescent : baseEnd_4303204 < baseStart_4303204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303221 : List Nat := [1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4303221 : Nat := 118140960795 + 4303221 * 2 ^ 59
def prefixEnd_4303221 : Nat := 4983230072969 + 3 ^ 40 * 4303221 * 2
def baseEnd_4303221 : Nat := 2209620735521413361747353

theorem tailTrace_4303221 : CollatzResearch.WordTrace tailWord_4303221 prefixEnd_4303221 2209620735521413361747353 := by
  unfold tailWord_4303221
  simp only [CollatzResearch.WordTrace]
  refine ⟨156951363943172723481013517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104634242628781815654009011 156951363943172723481013517)
  ·
    refine ⟨58856761478689771305380069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156951363943172723481013517 58856761478689771305380069)
    ·
      refine ⟨11035642777254332119758763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58856761478689771305380069 11035642777254332119758763)
      ·
        refine ⟨16553464165881498179638145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035642777254332119758763 16553464165881498179638145)
        ·
          refine ⟨12415098124411123634728609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16553464165881498179638145 12415098124411123634728609)
          ·
            refine ⟨9311323593308342726046457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12415098124411123634728609 9311323593308342726046457)
            ·
              refine ⟨6983492694981257044534843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9311323593308342726046457 6983492694981257044534843)
              ·
                refine ⟨10475239042471885566802265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6983492694981257044534843 10475239042471885566802265)
                ·
                  refine ⟨7856429281853914175101699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10475239042471885566802265 7856429281853914175101699)
                  ·
                    refine ⟨11784643922780871262652549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7856429281853914175101699 11784643922780871262652549)
                    ·
                      refine ⟨2209620735521413361747353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11784643922780871262652549 2209620735521413361747353)
                      ·
                        rfl

theorem cell23_4303221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4303221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303221 prefixEnd_4303221 := by exact prefixLift 4303221
  have htrace : WordTrace (prefixWord ++ tailWord_4303221) baseStart_4303221 baseEnd_4303221 := by
    simpa [prefixWord, tailWord_4303221, baseEnd_4303221] using wordTrace_append hprefix tailTrace_4303221
  have hstable : (prefixWord ++ tailWord_4303221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303221).length < 2 ^ (prefixWord ++ tailWord_4303221).sum := by decide
  have hdescent : baseEnd_4303221 < baseStart_4303221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303244 : List Nat := [2, 2, 1, 2, 1, 5, 2, 2, 6]
def baseStart_4303244 : Nat := 118140960795 + 4303244 * 2 ^ 59
def prefixEnd_4303244 : Nat := 4983230072969 + 3 ^ 40 * 4303244 * 2
def baseEnd_4303244 : Nat := 245514727286274085751083

theorem tailTrace_4303244 : CollatzResearch.WordTrace tailWord_4303244 prefixEnd_4303244 245514727286274085751083 := by
  unfold tailWord_4303244
  simp only [CollatzResearch.WordTrace]
  refine ⟨78476101411044699204550393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104634801881392932272733857 78476101411044699204550393)
  ·
    refine ⟨58857076058283524403412795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78476101411044699204550393 58857076058283524403412795)
    ·
      refine ⟨88285614087425286605119193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58857076058283524403412795 88285614087425286605119193)
      ·
        refine ⟨66214210565568964953839395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88285614087425286605119193 66214210565568964953839395)
        ·
          refine ⟨99321315848353447430759093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66214210565568964953839395 99321315848353447430759093)
          ·
            refine ⟨9311373360783135696633665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99321315848353447430759093 9311373360783135696633665)
            ·
              refine ⟨6983530020587351772475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9311373360783135696633665 6983530020587351772475249)
              ·
                refine ⟨5237647515440513829356437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6983530020587351772475249 5237647515440513829356437)
                ·
                  refine ⟨245514727286274085751083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5237647515440513829356437 245514727286274085751083)
                  ·
                    rfl

theorem cell23_4303244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_4303244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303244 prefixEnd_4303244 := by exact prefixLift 4303244
  have htrace : WordTrace (prefixWord ++ tailWord_4303244) baseStart_4303244 baseEnd_4303244 := by
    simpa [prefixWord, tailWord_4303244, baseEnd_4303244] using wordTrace_append hprefix tailTrace_4303244
  have hstable : (prefixWord ++ tailWord_4303244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303244).length < 2 ^ (prefixWord ++ tailWord_4303244).sum := by decide
  have hdescent : baseEnd_4303244 < baseStart_4303244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303257 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_4303257 : Nat := 118140960795 + 4303257 * 2 ^ 59
def prefixEnd_4303257 : Nat := 4983230072969 + 3 ^ 40 * 4303257 * 2
def baseEnd_4303257 : Nat := 736546406941658406965729

theorem tailTrace_4303257 : CollatzResearch.WordTrace tailWord_4303257 prefixEnd_4303257 736546406941658406965729 := by
  unfold tailWord_4303257
  simp only [CollatzResearch.WordTrace]
  refine ⟨156952676971042301629324025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104635117980694867752882683 156952676971042301629324025)
  ·
    refine ⟨117714507728281726221993019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156952676971042301629324025 117714507728281726221993019)
    ·
      refine ⟨176571761592422589332989529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117714507728281726221993019 176571761592422589332989529)
      ·
        refine ⟨132428821194316941999742147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176571761592422589332989529 132428821194316941999742147)
        ·
          refine ⟨198643231791475412999613221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132428821194316941999742147 198643231791475412999613221)
          ·
            refine ⟨37245605960901639937427479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198643231791475412999613221 37245605960901639937427479)
            ·
              refine ⟨55868408941352459906141219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37245605960901639937427479 55868408941352459906141219)
              ·
                refine ⟨83802613412028689859211829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55868408941352459906141219 83802613412028689859211829)
                ·
                  refine ⟨7856495007377689674301109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83802613412028689859211829 7856495007377689674301109)
                  ·
                    refine ⟨736546406941658406965729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7856495007377689674301109 736546406941658406965729)
                    ·
                      rfl

theorem cell23_4303257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_4303257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303257 prefixEnd_4303257 := by exact prefixLift 4303257
  have htrace : WordTrace (prefixWord ++ tailWord_4303257) baseStart_4303257 baseEnd_4303257 := by
    simpa [prefixWord, tailWord_4303257, baseEnd_4303257] using wordTrace_append hprefix tailTrace_4303257
  have hstable : (prefixWord ++ tailWord_4303257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303257).length < 2 ^ (prefixWord ++ tailWord_4303257).sum := by decide
  have hdescent : baseEnd_4303257 < baseStart_4303257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303271 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 3]
def baseStart_4303271 : Nat := 118140960795 + 4303271 * 2 ^ 59
def prefixEnd_4303271 : Nat := 4983230072969 + 3 ^ 40 * 4303271 * 2
def baseEnd_4303271 : Nat := 2209646409554138166122123

theorem tailTrace_4303271 : CollatzResearch.WordTrace tailWord_4303271 prefixEnd_4303271 2209646409554138166122123 := by
  unfold tailWord_4303271
  simp only [CollatzResearch.WordTrace]
  refine ⟨156953187592991582020333667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104635458395327721346889111 156953187592991582020333667)
  ·
    refine ⟨235429781389487373030500501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156953187592991582020333667 235429781389487373030500501)
    ·
      refine ⟨11035771002632220610804711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 235429781389487373030500501 11035771002632220610804711)
      ·
        refine ⟨16553656503948330916207067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035771002632220610804711 16553656503948330916207067)
        ·
          refine ⟨24830484755922496374310601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553656503948330916207067 24830484755922496374310601)
          ·
            refine ⟨18622863566941872280732951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24830484755922496374310601 18622863566941872280732951)
            ·
              refine ⟨27934295350412808421099427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18622863566941872280732951 27934295350412808421099427)
              ·
                refine ⟨41901443025619212631649141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27934295350412808421099427 41901443025619212631649141)
                ·
                  refine ⟨3928260283651801184217107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41901443025619212631649141 3928260283651801184217107)
                  ·
                    refine ⟨5892390425477701776325661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3928260283651801184217107 5892390425477701776325661)
                    ·
                      refine ⟨2209646409554138166122123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892390425477701776325661 2209646409554138166122123)
                      ·
                        rfl

theorem cell23_4303271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_4303271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303271 prefixEnd_4303271 := by exact prefixLift 4303271
  have htrace : WordTrace (prefixWord ++ tailWord_4303271) baseStart_4303271 baseEnd_4303271 := by
    simpa [prefixWord, tailWord_4303271, baseEnd_4303271] using wordTrace_append hprefix tailTrace_4303271
  have hstable : (prefixWord ++ tailWord_4303271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303271).length < 2 ^ (prefixWord ++ tailWord_4303271).sum := by decide
  have hdescent : baseEnd_4303271 < baseStart_4303271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303281 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4303281 : Nat := 118140960795 + 4303281 * 2 ^ 59
def prefixEnd_4303281 : Nat := 4983230072969 + 3 ^ 40 * 4303281 * 2
def baseEnd_4303281 : Nat := 2209651544360683126997077

theorem tailTrace_4303281 : CollatzResearch.WordTrace tailWord_4303281 prefixEnd_4303281 2209651544360683126997077 := by
  unfold tailWord_4303281
  simp only [CollatzResearch.WordTrace]
  refine ⟨156953552322955353728197697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104635701548636902485465131 156953552322955353728197697)
  ·
    refine ⟨117715164242216515296148273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156953552322955353728197697 117715164242216515296148273)
    ·
      refine ⟨88286373181662386472111205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117715164242216515296148273 88286373181662386472111205)
      ·
        refine ⟨16553694971561697463520851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88286373181662386472111205 16553694971561697463520851)
        ·
          refine ⟨24830542457342546195281277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16553694971561697463520851 24830542457342546195281277)
          ·
            refine ⟨9311453421503454823230479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24830542457342546195281277 9311453421503454823230479)
            ·
              refine ⟨13967180132255182234845719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311453421503454823230479 13967180132255182234845719)
              ·
                refine ⟨20950770198382773352268579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13967180132255182234845719 20950770198382773352268579)
                ·
                  refine ⟨31426155297574160028402869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20950770198382773352268579 31426155297574160028402869)
                  ·
                    refine ⟨2946202059147577502662769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31426155297574160028402869 2946202059147577502662769)
                    ·
                      refine ⟨2209651544360683126997077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946202059147577502662769 2209651544360683126997077)
                      ·
                        rfl

theorem cell23_4303281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4303281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303281 prefixEnd_4303281 := by exact prefixLift 4303281
  have htrace : WordTrace (prefixWord ++ tailWord_4303281) baseStart_4303281 baseEnd_4303281 := by
    simpa [prefixWord, tailWord_4303281, baseEnd_4303281] using wordTrace_append hprefix tailTrace_4303281
  have hstable : (prefixWord ++ tailWord_4303281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303281).length < 2 ^ (prefixWord ++ tailWord_4303281).sum := by decide
  have hdescent : baseEnd_4303281 < baseStart_4303281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303307 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6]
def baseStart_4303307 : Nat := 118140960795 + 4303307 * 2 ^ 59
def prefixEnd_4303307 : Nat := 4983230072969 + 3 ^ 40 * 4303307 * 2
def baseEnd_4303307 : Nat := 2209664894857700025271957

theorem tailTrace_4303307 : CollatzResearch.WordTrace tailWord_4303307 prefixEnd_4303307 2209664894857700025271957 := by
  unfold tailWord_4303307
  simp only [CollatzResearch.WordTrace]
  refine ⟨156954500620861160168644175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104636333747240773445762783 156954500620861160168644175)
  ·
    refine ⟨235431750931291740252966263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156954500620861160168644175 235431750931291740252966263)
    ·
      refine ⟨353147626396937610379449395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235431750931291740252966263 353147626396937610379449395)
      ·
        refine ⟨529721439595406415569174093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353147626396937610379449395 529721439595406415569174093)
        ·
          refine ⟨198645539848277405838440285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 529721439595406415569174093 198645539848277405838440285)
          ·
            refine ⟨74492077443104027189415107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198645539848277405838440285 74492077443104027189415107)
            ·
              refine ⟨111738116164656040784122661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74492077443104027189415107 111738116164656040784122661)
              ·
                refine ⟨20950896780873007647022999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111738116164656040784122661 20950896780873007647022999)
                ·
                  refine ⟨31426345171309511470534499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20950896780873007647022999 31426345171309511470534499)
                  ·
                    refine ⟨47139517756964267205801749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31426345171309511470534499 47139517756964267205801749)
                    ·
                      refine ⟨2209664894857700025271957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47139517756964267205801749 2209664894857700025271957)
                      ·
                        rfl

theorem cell23_4303307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 6].length) (baseStart_4303307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303307 prefixEnd_4303307 := by exact prefixLift 4303307
  have htrace : WordTrace (prefixWord ++ tailWord_4303307) baseStart_4303307 baseEnd_4303307 := by
    simpa [prefixWord, tailWord_4303307, baseEnd_4303307] using wordTrace_append hprefix tailTrace_4303307
  have hstable : (prefixWord ++ tailWord_4303307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303307).length < 2 ^ (prefixWord ++ tailWord_4303307).sum := by decide
  have hdescent : baseEnd_4303307 < baseStart_4303307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303344 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3]
def baseStart_4303344 : Nat := 118140960795 + 4303344 * 2 ^ 59
def prefixEnd_4303344 : Nat := 4983230072969 + 3 ^ 40 * 4303344 * 2
def baseEnd_4303344 : Nat := 2209683893641916380509287

theorem tailTrace_4303344 : CollatzResearch.WordTrace tailWord_4303344 prefixEnd_4303344 2209683893641916380509287 := by
  unfold tailWord_4303344
  simp only [CollatzResearch.WordTrace]
  refine ⟨78477925060863557743870543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104637233414484743658494057 78477925060863557743870543)
  ·
    refine ⟨117716887591295336615805815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78477925060863557743870543 117716887591295336615805815)
    ·
      refine ⟨176575331386943004923708723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117716887591295336615805815 176575331386943004923708723)
      ·
        refine ⟨264862997080414507385563085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176575331386943004923708723 264862997080414507385563085)
        ·
          refine ⟨99323623905155440269586157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264862997080414507385563085 99323623905155440269586157)
          ·
            refine ⟨37246358964433290101094809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99323623905155440269586157 37246358964433290101094809)
            ·
              refine ⟨27934769223324967575821107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37246358964433290101094809 27934769223324967575821107)
              ·
                refine ⟨41902153834987451363731661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27934769223324967575821107 41902153834987451363731661)
                ·
                  refine ⟨15713307688120294261399373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41902153834987451363731661 15713307688120294261399373)
                  ·
                    refine ⟨5892490383045110348024765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15713307688120294261399373 5892490383045110348024765)
                    ·
                      refine ⟨2209683893641916380509287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892490383045110348024765 2209683893641916380509287)
                      ·
                        rfl

theorem cell23_4303344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 3].length) (baseStart_4303344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303344 prefixEnd_4303344 := by exact prefixLift 4303344
  have htrace : WordTrace (prefixWord ++ tailWord_4303344) baseStart_4303344 baseEnd_4303344 := by
    simpa [prefixWord, tailWord_4303344, baseEnd_4303344] using wordTrace_append hprefix tailTrace_4303344
  have hstable : (prefixWord ++ tailWord_4303344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303344).length < 2 ^ (prefixWord ++ tailWord_4303344).sum := by decide
  have hdescent : baseEnd_4303344 < baseStart_4303344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303387 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9]
def baseStart_4303387 : Nat := 118140960795 + 4303387 * 2 ^ 59
def prefixEnd_4303387 : Nat := 4983230072969 + 3 ^ 40 * 4303387 * 2
def baseEnd_4303387 : Nat := 2209705973310059712271589

theorem tailTrace_4303387 : CollatzResearch.WordTrace tailWord_4303387 prefixEnd_4303387 2209705973310059712271589 := by
  unfold tailWord_4303387
  simp only [CollatzResearch.WordTrace]
  refine ⟨156957418460571333831556415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104638278973714222554370943 156957418460571333831556415)
  ·
    refine ⟨235436127690857000747334623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156957418460571333831556415 235436127690857000747334623)
    ·
      refine ⟨353154191536285501121001935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235436127690857000747334623 353154191536285501121001935)
      ·
        refine ⟨529731287304428251681502903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353154191536285501121001935 529731287304428251681502903)
        ·
          refine ⟨794596930956642377522254355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529731287304428251681502903 794596930956642377522254355)
          ·
            refine ⟨1191895396434963566283381533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794596930956642377522254355 1191895396434963566283381533)
            ·
              refine ⟨446960773663111337356268075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1191895396434963566283381533 446960773663111337356268075)
              ·
                refine ⟨670441160494667006034402113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446960773663111337356268075 670441160494667006034402113)
                ·
                  refine ⟨502830870371000254525801585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 670441160494667006034402113 502830870371000254525801585)
                  ·
                    refine ⟨377123152778250190894351189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 502830870371000254525801585 377123152778250190894351189)
                    ·
                      refine ⟨2209705973310059712271589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 377123152778250190894351189 2209705973310059712271589)
                      ·
                        rfl

theorem cell23_4303387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_4303387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303387 prefixEnd_4303387 := by exact prefixLift 4303387
  have htrace : WordTrace (prefixWord ++ tailWord_4303387) baseStart_4303387 baseEnd_4303387 := by
    simpa [prefixWord, tailWord_4303387, baseEnd_4303387] using wordTrace_append hprefix tailTrace_4303387
  have hstable : (prefixWord ++ tailWord_4303387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303387).length < 2 ^ (prefixWord ++ tailWord_4303387).sum := by decide
  have hdescent : baseEnd_4303387 < baseStart_4303387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303388 : List Nat := [2, 2, 3, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4303388 : Nat := 118140960795 + 4303388 * 2 ^ 59
def prefixEnd_4303388 : Nat := 4983230072969 + 3 ^ 40 * 4303388 * 2
def baseEnd_4303388 : Nat := 2209706486790714208359085

theorem tailTrace_4303388 : CollatzResearch.WordTrace tailWord_4303388 prefixEnd_4303388 2209706486790714208359085 := by
  unfold tailWord_4303388
  simp only [CollatzResearch.WordTrace]
  refine ⟨78478727466783855501171409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104638303289045140668228545 78478727466783855501171409)
  ·
    refine ⟨58859045600087891625878557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78478727466783855501171409 58859045600087891625878557)
    ·
      refine ⟨22072142100032959359704459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58859045600087891625878557 22072142100032959359704459)
      ·
        refine ⟨33108213150049439039556689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22072142100032959359704459 33108213150049439039556689)
        ·
          refine ⟨24831159862537079279667517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33108213150049439039556689 24831159862537079279667517)
          ·
            refine ⟨9311684948451404729875319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24831159862537079279667517 9311684948451404729875319)
            ·
              refine ⟨13967527422677107094812979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311684948451404729875319 13967527422677107094812979)
              ·
                refine ⟨20951291134015660642219469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13967527422677107094812979 20951291134015660642219469)
                ·
                  refine ⟨7856734175255872740832301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20951291134015660642219469 7856734175255872740832301)
                  ·
                    refine ⟨2946275315720952277812113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7856734175255872740832301 2946275315720952277812113)
                    ·
                      refine ⟨2209706486790714208359085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946275315720952277812113 2209706486790714208359085)
                      ·
                        rfl

theorem cell23_4303388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4303388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303388 prefixEnd_4303388 := by exact prefixLift 4303388
  have htrace : WordTrace (prefixWord ++ tailWord_4303388) baseStart_4303388 baseEnd_4303388 := by
    simpa [prefixWord, tailWord_4303388, baseEnd_4303388] using wordTrace_append hprefix tailTrace_4303388
  have hstable : (prefixWord ++ tailWord_4303388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303388).length < 2 ^ (prefixWord ++ tailWord_4303388).sum := by decide
  have hdescent : baseEnd_4303388 < baseStart_4303388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303394 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_4303394 : Nat := 118140960795 + 4303394 * 2 ^ 59
def prefixEnd_4303394 : Nat := 4983230072969 + 3 ^ 40 * 4303394 * 2
def baseEnd_4303394 : Nat := 736569855891547061628019

theorem tailTrace_4303394 : CollatzResearch.WordTrace tailWord_4303394 prefixEnd_4303394 736569855891547061628019 := by
  unfold tailWord_4303394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39239418442886493506765309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104638449181030649351374157 39239418442886493506765309)
  ·
    refine ⟨14714781916082435065036991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39239418442886493506765309 14714781916082435065036991)
    ·
      refine ⟨22072172874123652597555487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14714781916082435065036991 22072172874123652597555487)
      ·
        refine ⟨33108259311185478896333231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22072172874123652597555487 33108259311185478896333231)
        ·
          refine ⟨49662388966778218344499847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33108259311185478896333231 49662388966778218344499847)
          ·
            refine ⟨74493583450167327516749771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49662388966778218344499847 74493583450167327516749771)
            ·
              refine ⟨111740375175250991275124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74493583450167327516749771 111740375175250991275124657)
              ·
                refine ⟨83805281381438243456343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111740375175250991275124657 83805281381438243456343493)
                ·
                  refine ⟨15713490259019670648064405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83805281381438243456343493 15713490259019670648064405)
                  ·
                    refine ⟨736569855891547061628019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15713490259019670648064405 736569855891547061628019)
                    ·
                      rfl

theorem cell23_4303394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_4303394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303394 prefixEnd_4303394 := by exact prefixLift 4303394
  have htrace : WordTrace (prefixWord ++ tailWord_4303394) baseStart_4303394 baseEnd_4303394 := by
    simpa [prefixWord, tailWord_4303394, baseEnd_4303394] using wordTrace_append hprefix tailTrace_4303394
  have hstable : (prefixWord ++ tailWord_4303394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303394).length < 2 ^ (prefixWord ++ tailWord_4303394).sum := by decide
  have hdescent : baseEnd_4303394 < baseStart_4303394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303404 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_4303404 : Nat := 118140960795 + 4303404 * 2 ^ 59
def prefixEnd_4303404 : Nat := 4983230072969 + 3 ^ 40 * 4303404 * 2
def baseEnd_4303404 : Nat := 2209714702481186145759011

theorem tailTrace_4303404 : CollatzResearch.WordTrace tailWord_4303404 prefixEnd_4303404 2209714702481186145759011 := by
  unfold tailWord_4303404
  simp only [CollatzResearch.WordTrace]
  refine ⟨78479019250754872867462633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104638692334339830489950177 78479019250754872867462633)
  ·
    refine ⟨58859264438066154650596975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78479019250754872867462633 58859264438066154650596975)
    ·
      refine ⟨88288896657099231975895463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58859264438066154650596975 88288896657099231975895463)
      ·
        refine ⟨132433344985648847963843195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88288896657099231975895463 132433344985648847963843195)
        ·
          refine ⟨198650017478473271945764793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132433344985648847963843195 198650017478473271945764793)
          ·
            refine ⟨148987513108854953959323595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198650017478473271945764793 148987513108854953959323595)
            ·
              refine ⟨223481269663282430938985393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148987513108854953959323595 223481269663282430938985393)
              ·
                refine ⟨167610952247461823204239045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223481269663282430938985393 167610952247461823204239045)
                ·
                  refine ⟨31427053546399091850794821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167610952247461823204239045 31427053546399091850794821)
                  ·
                    refine ⟨5892572539949829722024029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31427053546399091850794821 5892572539949829722024029)
                    ·
                      refine ⟨2209714702481186145759011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892572539949829722024029 2209714702481186145759011)
                      ·
                        rfl

theorem cell23_4303404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_4303404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303404 prefixEnd_4303404 := by exact prefixLift 4303404
  have htrace : WordTrace (prefixWord ++ tailWord_4303404) baseStart_4303404 baseEnd_4303404 := by
    simpa [prefixWord, tailWord_4303404, baseEnd_4303404] using wordTrace_append hprefix tailTrace_4303404
  have hstable : (prefixWord ++ tailWord_4303404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303404).length < 2 ^ (prefixWord ++ tailWord_4303404).sum := by decide
  have hdescent : baseEnd_4303404 < baseStart_4303404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303421 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_4303421 : Nat := 118140960795 + 4303421 * 2 ^ 59
def prefixEnd_4303421 : Nat := 4983230072969 + 3 ^ 40 * 4303421 * 2
def baseEnd_4303421 : Nat := 2209723431652312579246433

theorem tailTrace_4303421 : CollatzResearch.WordTrace tailWord_4303421 prefixEnd_4303421 2209723431652312579246433 := by
  unfold tailWord_4303421
  simp only [CollatzResearch.WordTrace]
  refine ⟨156958658542448157638294117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104639105694965438425529411 156958658542448157638294117)
  ·
    refine ⟨29429748476709029557180147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 156958658542448157638294117 29429748476709029557180147)
    ·
      refine ⟨44144622715063544335770221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29429748476709029557180147 44144622715063544335770221)
      ·
        refine ⟨16554233518148829125913833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44144622715063544335770221 16554233518148829125913833)
        ·
          refine ⟨12415675138611621844435375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16554233518148829125913833 12415675138611621844435375)
          ·
            refine ⟨18623512707917432766653063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12415675138611621844435375 18623512707917432766653063)
            ·
              refine ⟨27935269061876149149979595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18623512707917432766653063 27935269061876149149979595)
              ·
                refine ⟨41902903592814223724969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27935269061876149149979595 41902903592814223724969393)
                ·
                  refine ⟨31427177694610667793727045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41902903592814223724969393 31427177694610667793727045)
                  ·
                    refine ⟨5892595817739500211323821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31427177694610667793727045 5892595817739500211323821)
                    ·
                      refine ⟨2209723431652312579246433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892595817739500211323821 2209723431652312579246433)
                      ·
                        rfl

theorem cell23_4303421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_4303421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303421 prefixEnd_4303421 := by exact prefixLift 4303421
  have htrace : WordTrace (prefixWord ++ tailWord_4303421) baseStart_4303421 baseEnd_4303421 := by
    simpa [prefixWord, tailWord_4303421, baseEnd_4303421] using wordTrace_append hprefix tailTrace_4303421
  have hstable : (prefixWord ++ tailWord_4303421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303421).length < 2 ^ (prefixWord ++ tailWord_4303421).sum := by decide
  have hdescent : baseEnd_4303421 < baseStart_4303421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303431 : List Nat := [1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4]
def baseStart_4303431 : Nat := 118140960795 + 4303431 * 2 ^ 59
def prefixEnd_4303431 : Nat := 4983230072969 + 3 ^ 40 * 4303431 * 2
def baseEnd_4303431 : Nat := 2209728566458857540121387

theorem tailTrace_4303431 : CollatzResearch.WordTrace tailWord_4303431 prefixEnd_4303431 2209728566458857540121387 := by
  unfold tailWord_4303431
  simp only [CollatzResearch.WordTrace]
  refine ⟨156959023272411929346158147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104639348848274619564105431 156959023272411929346158147)
  ·
    refine ⟨235438534908617894019237221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156959023272411929346158147 235438534908617894019237221)
    ·
      refine ⟨44144725295365855128606979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235438534908617894019237221 44144725295365855128606979)
      ·
        refine ⟨66217087943048782692910469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44144725295365855128606979 66217087943048782692910469)
        ·
          refine ⟨12415703989321646754920713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66217087943048782692910469 12415703989321646754920713)
          ·
            refine ⟨9311777991991235066190535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12415703989321646754920713 9311777991991235066190535)
            ·
              refine ⟨13967666987986852599285803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9311777991991235066190535 13967666987986852599285803)
              ·
                refine ⟨20951500481980278898928705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13967666987986852599285803 20951500481980278898928705)
                ·
                  refine ⟨15713625361485209174196529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20951500481980278898928705 15713625361485209174196529)
                  ·
                    refine ⟨11785219021113906880647397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15713625361485209174196529 11785219021113906880647397)
                    ·
                      refine ⟨2209728566458857540121387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11785219021113906880647397 2209728566458857540121387)
                      ·
                        rfl

theorem cell23_4303431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_4303431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303431 prefixEnd_4303431 := by exact prefixLift 4303431
  have htrace : WordTrace (prefixWord ++ tailWord_4303431) baseStart_4303431 baseEnd_4303431 := by
    simpa [prefixWord, tailWord_4303431, baseEnd_4303431] using wordTrace_append hprefix tailTrace_4303431
  have hstable : (prefixWord ++ tailWord_4303431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303431).length < 2 ^ (prefixWord ++ tailWord_4303431).sum := by decide
  have hdescent : baseEnd_4303431 < baseStart_4303431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303508 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4303508 : Nat := 118140960795 + 4303508 * 2 ^ 59
def prefixEnd_4303508 : Nat := 4983230072969 + 3 ^ 40 * 4303508 * 2
def baseEnd_4303508 : Nat := 2209768104469253738858533

theorem tailTrace_4303508 : CollatzResearch.WordTrace tailWord_4303508 prefixEnd_4303508 2209768104469253738858533 := by
  unfold tailWord_4303508
  simp only [CollatzResearch.WordTrace]
  refine ⟨78480915846566485748355589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104641221128755314331140785 78480915846566485748355589)
  ·
    refine ⟨14715171721231216077816673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78480915846566485748355589 14715171721231216077816673)
    ·
      refine ⟨11036378790923412058362505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14715171721231216077816673 11036378790923412058362505)
      ·
        refine ⟨8277284093192559043771879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11036378790923412058362505 8277284093192559043771879)
        ·
          refine ⟨12415926139788838565657819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8277284093192559043771879 12415926139788838565657819)
          ·
            refine ⟨18623889209683257848486729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12415926139788838565657819 18623889209683257848486729)
            ·
              refine ⟨13967916907262443386365047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18623889209683257848486729 13967916907262443386365047)
              ·
                refine ⟨20951875360893665079547571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13967916907262443386365047 20951875360893665079547571)
                ·
                  refine ⟨31427813041340497619321357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20951875360893665079547571 31427813041340497619321357)
                  ·
                    refine ⟨11785429890502686607245509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31427813041340497619321357 11785429890502686607245509)
                    ·
                      refine ⟨2209768104469253738858533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11785429890502686607245509 2209768104469253738858533)
                      ·
                        rfl

theorem cell23_4303508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4303508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303508 prefixEnd_4303508 := by exact prefixLift 4303508
  have htrace : WordTrace (prefixWord ++ tailWord_4303508) baseStart_4303508 baseEnd_4303508 := by
    simpa [prefixWord, tailWord_4303508, baseEnd_4303508] using wordTrace_append hprefix tailTrace_4303508
  have hstable : (prefixWord ++ tailWord_4303508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303508).length < 2 ^ (prefixWord ++ tailWord_4303508).sum := by decide
  have hdescent : baseEnd_4303508 < baseStart_4303508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303511 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3]
def baseStart_4303511 : Nat := 118140960795 + 4303511 * 2 ^ 59
def prefixEnd_4303511 : Nat := 4983230072969 + 3 ^ 40 * 4303511 * 2
def baseEnd_4303511 : Nat := 2209769644911217227121019

theorem tailTrace_4303511 : CollatzResearch.WordTrace tailWord_4303511 prefixEnd_4303511 2209769644911217227121019 := by
  unfold tailWord_4303511
  simp only [CollatzResearch.WordTrace]
  refine ⟨156961941112122103009070387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104641294074748068672713591 156961941112122103009070387)
  ·
    refine ⟨235442911668183154513605581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156961941112122103009070387 235442911668183154513605581)
    ·
      refine ⟨88291091875568682942602093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235442911668183154513605581 88291091875568682942602093)
      ·
        refine ⟨33109159453338256103475785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88291091875568682942602093 33109159453338256103475785)
        ·
          refine ⟨24831869590003692077606839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33109159453338256103475785 24831869590003692077606839)
          ·
            refine ⟨37247804385005538116410259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24831869590003692077606839 37247804385005538116410259)
            ·
              refine ⟨55871706577508307174615389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37247804385005538116410259 55871706577508307174615389)
              ·
                refine ⟨20951889966565615190480771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55871706577508307174615389 20951889966565615190480771)
                ·
                  refine ⟨31427834949848422785721157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20951889966565615190480771 31427834949848422785721157)
                  ·
                    refine ⟨5892719053096579272322717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31427834949848422785721157 5892719053096579272322717)
                    ·
                      refine ⟨2209769644911217227121019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5892719053096579272322717 2209769644911217227121019)
                      ·
                        rfl

theorem cell23_4303511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_4303511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303511 prefixEnd_4303511 := by exact prefixLift 4303511
  have htrace : WordTrace (prefixWord ++ tailWord_4303511) baseStart_4303511 baseEnd_4303511 := by
    simpa [prefixWord, tailWord_4303511, baseEnd_4303511] using wordTrace_append hprefix tailTrace_4303511
  have hstable : (prefixWord ++ tailWord_4303511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303511).length < 2 ^ (prefixWord ++ tailWord_4303511).sum := by decide
  have hdescent : baseEnd_4303511 < baseStart_4303511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303544 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 11]
def baseStart_4303544 : Nat := 118140960795 + 4303544 * 2 ^ 59
def prefixEnd_4303544 : Nat := 4983230072969 + 3 ^ 40 * 4303544 * 2
def baseEnd_4303544 : Nat := 736595529924271866002789

theorem tailTrace_4303544 : CollatzResearch.WordTrace tailWord_4303544 prefixEnd_4303544 736595529924271866002789 := by
  unfold tailWord_4303544
  simp only [CollatzResearch.WordTrace]
  refine ⟨78481572360501274822510843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104642096480668366430014457 78481572360501274822510843)
  ·
    refine ⟨117722358540751912233766265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78481572360501274822510843 117722358540751912233766265)
    ·
      refine ⟨88291768905563934175324699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117722358540751912233766265 88291768905563934175324699)
      ·
        refine ⟨132437653358345901262987049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88291768905563934175324699 132437653358345901262987049)
        ·
          refine ⟨99328240018759425947240287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132437653358345901262987049 99328240018759425947240287)
          ·
            refine ⟨148992360028139138920860431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99328240018759425947240287 148992360028139138920860431)
            ·
              refine ⟨223488540042208708381290647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148992360028139138920860431 223488540042208708381290647)
              ·
                refine ⟨335232810063313062571935971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223488540042208708381290647 335232810063313062571935971)
                ·
                  refine ⟨502849215094969593857903957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 335232810063313062571935971 502849215094969593857903957)
                  ·
                    refine ⟨736595529924271866002789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 502849215094969593857903957 736595529924271866002789)
                    ·
                      rfl

theorem cell23_4303544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_4303544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303544 prefixEnd_4303544 := by exact prefixLift 4303544
  have htrace : WordTrace (prefixWord ++ tailWord_4303544) baseStart_4303544 baseEnd_4303544 := by
    simpa [prefixWord, tailWord_4303544, baseEnd_4303544] using wordTrace_append hprefix tailTrace_4303544
  have hstable : (prefixWord ++ tailWord_4303544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303544).length < 2 ^ (prefixWord ++ tailWord_4303544).sum := by decide
  have hdescent : baseEnd_4303544 < baseStart_4303544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303585 : List Nat := [1, 2, 3, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_4303585 : Nat := 118140960795 + 4303585 * 2 ^ 59
def prefixEnd_4303585 : Nat := 4983230072969 + 3 ^ 40 * 4303585 * 2
def baseEnd_4303585 : Nat := 2209807642479649937595679

theorem tailTrace_4303585 : CollatzResearch.WordTrace tailWord_4303585 prefixEnd_4303585 2209807642479649937595679 := by
  unfold tailWord_4303585
  simp only [CollatzResearch.WordTrace]
  refine ⟨156964640113854013647264209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104643093409236009098176139 156964640113854013647264209)
  ·
    refine ⟨117723480085390510235448157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156964640113854013647264209 117723480085390510235448157)
    ·
      refine ⟨44146305032021441338293059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117723480085390510235448157 44146305032021441338293059)
      ·
        refine ⟨66219457548032162007439589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44146305032021441338293059 66219457548032162007439589)
        ·
          refine ⟨12416148290256030376394923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66219457548032162007439589 12416148290256030376394923)
          ·
            refine ⟨18624222435384045564592385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12416148290256030376394923 18624222435384045564592385)
            ·
              refine ⟨13968166826538034173444289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18624222435384045564592385 13968166826538034173444289)
              ·
                refine ⟨10476125119903525630083217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13968166826538034173444289 10476125119903525630083217)
                ·
                  refine ⟨7857093839927644222562413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10476125119903525630083217 7857093839927644222562413)
                  ·
                    refine ⟨2946410189972866583460905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7857093839927644222562413 2946410189972866583460905)
                    ·
                      refine ⟨2209807642479649937595679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946410189972866583460905 2209807642479649937595679)
                      ·
                        rfl

theorem cell23_4303585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_4303585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303585 prefixEnd_4303585 := by exact prefixLift 4303585
  have htrace : WordTrace (prefixWord ++ tailWord_4303585) baseStart_4303585 baseEnd_4303585 := by
    simpa [prefixWord, tailWord_4303585, baseEnd_4303585] using wordTrace_append hprefix tailTrace_4303585
  have hstable : (prefixWord ++ tailWord_4303585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303585).length < 2 ^ (prefixWord ++ tailWord_4303585).sum := by decide
  have hdescent : baseEnd_4303585 < baseStart_4303585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303598 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4303598 : Nat := 118140960795 + 4303598 * 2 ^ 59
def prefixEnd_4303598 : Nat := 4983230072969 + 3 ^ 40 * 4303598 * 2
def baseEnd_4303598 : Nat := 2209814317728158386733119

theorem tailTrace_4303598 : CollatzResearch.WordTrace tailWord_4303598 prefixEnd_4303598 2209814317728158386733119 := by
  unfold tailWord_4303598
  simp only [CollatzResearch.WordTrace]
  refine ⟨19620639282850864608435931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104643409508537944578324965 19620639282850864608435931)
  ·
    refine ⟨29430958924276296912653897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19620639282850864608435931 29430958924276296912653897)
    ·
      refine ⟨22073219193207222684490423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29430958924276296912653897 22073219193207222684490423)
      ·
        refine ⟨33109828789810834026735635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22073219193207222684490423 33109828789810834026735635)
        ·
          refine ⟨49664743184716251040103453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33109828789810834026735635 49664743184716251040103453)
          ·
            refine ⟨18624278694268594140038795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49664743184716251040103453 18624278694268594140038795)
            ·
              refine ⟨27936418041402891210058193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18624278694268594140038795 27936418041402891210058193)
              ·
                refine ⟨20952313531052168407543645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27936418041402891210058193 20952313531052168407543645)
                ·
                  refine ⟨7857117574144563152828867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20952313531052168407543645 7857117574144563152828867)
                  ·
                    refine ⟨11785676361216844729243301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7857117574144563152828867 11785676361216844729243301)
                    ·
                      refine ⟨2209814317728158386733119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11785676361216844729243301 2209814317728158386733119)
                      ·
                        rfl

theorem cell23_4303598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4303598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303598 prefixEnd_4303598 := by exact prefixLift 4303598
  have htrace : WordTrace (prefixWord ++ tailWord_4303598) baseStart_4303598 baseEnd_4303598 := by
    simpa [prefixWord, tailWord_4303598, baseEnd_4303598] using wordTrace_append hprefix tailTrace_4303598
  have hstable : (prefixWord ++ tailWord_4303598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303598).length < 2 ^ (prefixWord ++ tailWord_4303598).sum := by decide
  have hdescent : baseEnd_4303598 < baseStart_4303598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303601 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_4303601 : Nat := 118140960795 + 4303601 * 2 ^ 59
def prefixEnd_4303601 : Nat := 4983230072969 + 3 ^ 40 * 4303601 * 2
def baseEnd_4303601 : Nat := 2209815858170121874995605

theorem tailTrace_4303601 : CollatzResearch.WordTrace tailWord_4303601 prefixEnd_4303601 2209815858170121874995605 := by
  unfold tailWord_4303601
  simp only [CollatzResearch.WordTrace]
  refine ⟨156965223681796048379846657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104643482454530698919897771 156965223681796048379846657)
  ·
    refine ⟨117723917761347036284884993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156965223681796048379846657 117723917761347036284884993)
    ·
      refine ⟨88292938321010277213663745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117723917761347036284884993 88292938321010277213663745)
      ·
        refine ⟨66219703740757707910247809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88292938321010277213663745 66219703740757707910247809)
        ·
          refine ⟨49664777805568280932685857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66219703740757707910247809 49664777805568280932685857)
          ·
            refine ⟨37248583354176210699514393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49664777805568280932685857 37248583354176210699514393)
            ·
              refine ⟨27936437515632158024635795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37248583354176210699514393 27936437515632158024635795)
              ·
                refine ⟨41904656273448237036953693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27936437515632158024635795 41904656273448237036953693)
                ·
                  refine ⟨15714246102543088888857635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41904656273448237036953693 15714246102543088888857635)
                  ·
                    refine ⟨23571369153814633333286453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15714246102543088888857635 23571369153814633333286453)
                    ·
                      refine ⟨2209815858170121874995605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23571369153814633333286453 2209815858170121874995605)
                      ·
                        rfl

theorem cell23_4303601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_4303601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303601 prefixEnd_4303601 := by exact prefixLift 4303601
  have htrace : WordTrace (prefixWord ++ tailWord_4303601) baseStart_4303601 baseEnd_4303601 := by
    simpa [prefixWord, tailWord_4303601, baseEnd_4303601] using wordTrace_append hprefix tailTrace_4303601
  have hstable : (prefixWord ++ tailWord_4303601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303601).length < 2 ^ (prefixWord ++ tailWord_4303601).sum := by decide
  have hdescent : baseEnd_4303601 < baseStart_4303601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303608 : List Nat := [2, 1, 2, 1, 1, 2, 3, 5, 2, 4]
def baseStart_4303608 : Nat := 118140960795 + 4303608 * 2 ^ 59
def prefixEnd_4303608 : Nat := 4983230072969 + 3 ^ 40 * 4303608 * 2
def baseEnd_4303608 : Nat := 736606484178234449202691

theorem tailTrace_4303608 : CollatzResearch.WordTrace tailWord_4303608 prefixEnd_4303608 736606484178234449202691 := by
  unfold tailWord_4303608
  simp only [CollatzResearch.WordTrace]
  refine ⟨78482739496385344287675739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104643652661847125716900985 78482739496385344287675739)
  ·
    refine ⟨117724109244578016431513609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78482739496385344287675739 117724109244578016431513609)
    ·
      refine ⟨88293081933433512323635207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117724109244578016431513609 88293081933433512323635207)
      ·
        refine ⟨132439622900150268485452811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88293081933433512323635207 132439622900150268485452811)
        ·
          refine ⟨198659434350225402728179217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132439622900150268485452811 198659434350225402728179217)
          ·
            refine ⟨148994575762669052046134413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198659434350225402728179217 148994575762669052046134413)
            ·
              refine ⟨55872965911000894517300405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 148994575762669052046134413 55872965911000894517300405)
              ·
                refine ⟨5238090554156333860996913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55872965911000894517300405 5238090554156333860996913)
                ·
                  refine ⟨3928567915617250395747685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5238090554156333860996913 3928567915617250395747685)
                  ·
                    refine ⟨736606484178234449202691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928567915617250395747685 736606484178234449202691)
                    ·
                      rfl

theorem cell23_4303608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_4303608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303608 prefixEnd_4303608 := by exact prefixLift 4303608
  have htrace : WordTrace (prefixWord ++ tailWord_4303608) baseStart_4303608 baseEnd_4303608 := by
    simpa [prefixWord, tailWord_4303608, baseEnd_4303608] using wordTrace_append hprefix tailTrace_4303608
  have hstable : (prefixWord ++ tailWord_4303608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303608).length < 2 ^ (prefixWord ++ tailWord_4303608).sum := by decide
  have hdescent : baseEnd_4303608 < baseStart_4303608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303662 : List Nat := [4, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_4303662 : Nat := 118140960795 + 4303662 * 2 ^ 59
def prefixEnd_4303662 : Nat := 4983230072969 + 3 ^ 40 * 4303662 * 2
def baseEnd_4303662 : Nat := 2209847180490046136332825

theorem tailTrace_4303662 : CollatzResearch.WordTrace tailWord_4303662 prefixEnd_4303662 2209847180490046136332825 := by
  unfold tailWord_4303662
  simp only [CollatzResearch.WordTrace]
  refine ⟨19620931066821881974727155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104644965689716703865211493 19620931066821881974727155)
  ·
    refine ⟨29431396600232822962090733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19620931066821881974727155 29431396600232822962090733)
    ·
      refine ⟨11036773725087308610784025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29431396600232822962090733 11036773725087308610784025)
      ·
        refine ⟨8277580293815481458088019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11036773725087308610784025 8277580293815481458088019)
        ·
          refine ⟨12416370440723222187132029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8277580293815481458088019 12416370440723222187132029)
          ·
            refine ⟨4656138915271208320174511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12416370440723222187132029 4656138915271208320174511)
            ·
              refine ⟨6984208372906812480261767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656138915271208320174511 6984208372906812480261767)
              ·
                refine ⟨10476312559360218720392651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984208372906812480261767 10476312559360218720392651)
                ·
                  refine ⟨15714468839040328080588977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10476312559360218720392651 15714468839040328080588977)
                  ·
                    refine ⟨11785851629280246060441733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15714468839040328080588977 11785851629280246060441733)
                    ·
                      refine ⟨2209847180490046136332825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11785851629280246060441733 2209847180490046136332825)
                      ·
                        rfl

theorem cell23_4303662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_4303662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303662 prefixEnd_4303662 := by exact prefixLift 4303662
  have htrace : WordTrace (prefixWord ++ tailWord_4303662) baseStart_4303662 baseEnd_4303662 := by
    simpa [prefixWord, tailWord_4303662, baseEnd_4303662] using wordTrace_append hprefix tailTrace_4303662
  have hstable : (prefixWord ++ tailWord_4303662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303662).length < 2 ^ (prefixWord ++ tailWord_4303662).sum := by decide
  have hdescent : baseEnd_4303662 < baseStart_4303662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303692 : List Nat := [2, 2, 1, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4303692 : Nat := 118140960795 + 4303692 * 2 ^ 59
def prefixEnd_4303692 : Nat := 4983230072969 + 3 ^ 40 * 4303692 * 2
def baseEnd_4303692 : Nat := 2209862584909681018957687

theorem tailTrace_4303692 : CollatzResearch.WordTrace tailWord_4303692 prefixEnd_4303692 2209862584909681018957687 := by
  unfold tailWord_4303692
  simp only [CollatzResearch.WordTrace]
  refine ⟨78484271362233185460704665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104645695149644247280939553 78484271362233185460704665)
  ·
    refine ⟨58863203521674889095528499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78484271362233185460704665 58863203521674889095528499)
    ·
      refine ⟨88294805282512333643292749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58863203521674889095528499 88294805282512333643292749)
      ·
        refine ⟨33110551980942125116234781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88294805282512333643292749 33110551980942125116234781)
        ·
          refine ⟨12416456992853296918588043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33110551980942125116234781 12416456992853296918588043)
          ·
            refine ⟨18624685489279945377882065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12416456992853296918588043 18624685489279945377882065)
            ·
              refine ⟨13968514116959959033411549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18624685489279945377882065 13968514116959959033411549)
              ·
                refine ⟨5238192793859984637529331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13968514116959959033411549 5238192793859984637529331)
                ·
                  refine ⟨7857289190789976956293997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5238192793859984637529331 7857289190789976956293997)
                  ·
                    refine ⟨2946483446546241358610249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7857289190789976956293997 2946483446546241358610249)
                    ·
                      refine ⟨2209862584909681018957687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946483446546241358610249 2209862584909681018957687)
                      ·
                        rfl

theorem cell23_4303692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4303692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303692 prefixEnd_4303692 := by exact prefixLift 4303692
  have htrace : WordTrace (prefixWord ++ tailWord_4303692) baseStart_4303692 baseEnd_4303692 := by
    simpa [prefixWord, tailWord_4303692, baseEnd_4303692] using wordTrace_append hprefix tailTrace_4303692
  have hstable : (prefixWord ++ tailWord_4303692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303692).length < 2 ^ (prefixWord ++ tailWord_4303692).sum := by decide
  have hdescent : baseEnd_4303692 < baseStart_4303692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303726 : List Nat := [4, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_4303726 : Nat := 118140960795 + 4303726 * 2 ^ 59
def prefixEnd_4303726 : Nat := 4983230072969 + 3 ^ 40 * 4303726 * 2
def baseEnd_4303726 : Nat := 2209880043251933885932531

theorem tailTrace_4303726 : CollatzResearch.WordTrace tailWord_4303726 prefixEnd_4303726 2209880043251933885932531 := by
  unfold tailWord_4303726
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621222850792899341018379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104646521870895463152098021 19621222850792899341018379)
  ·
    refine ⟨29431834276189349011527569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19621222850792899341018379 29431834276189349011527569)
    ·
      refine ⟨22073875707142011758645677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29431834276189349011527569 22073875707142011758645677)
      ·
        refine ⟨8277703390178254409492129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22073875707142011758645677 8277703390178254409492129)
        ·
          refine ⟨6208277542633690807119097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8277703390178254409492129 6208277542633690807119097)
          ·
            refine ⟨4656208156975268105339323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6208277542633690807119097 4656208156975268105339323)
            ·
              refine ⟨6984312235462902158008985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656208156975268105339323 6984312235462902158008985)
              ·
                refine ⟨5238234176597176618506739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6984312235462902158008985 5238234176597176618506739)
                ·
                  refine ⟨7857351264895764927760109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5238234176597176618506739 7857351264895764927760109)
                  ·
                    refine ⟨2946506724335911847910041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7857351264895764927760109 2946506724335911847910041)
                    ·
                      refine ⟨2209880043251933885932531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946506724335911847910041 2209880043251933885932531)
                      ·
                        rfl

theorem cell23_4303726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_4303726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303726 prefixEnd_4303726 := by exact prefixLift 4303726
  have htrace : WordTrace (prefixWord ++ tailWord_4303726) baseStart_4303726 baseEnd_4303726 := by
    simpa [prefixWord, tailWord_4303726, baseEnd_4303726] using wordTrace_append hprefix tailTrace_4303726
  have hstable : (prefixWord ++ tailWord_4303726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303726).length < 2 ^ (prefixWord ++ tailWord_4303726).sum := by decide
  have hdescent : baseEnd_4303726 < baseStart_4303726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303738 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3]
def baseStart_4303738 : Nat := 118140960795 + 4303738 * 2 ^ 59
def prefixEnd_4303738 : Nat := 4983230072969 + 3 ^ 40 * 4303738 * 2
def baseEnd_4303738 : Nat := 2209886205019787838982475

theorem tailTrace_4303738 : CollatzResearch.WordTrace tailWord_4303738 prefixEnd_4303738 2209886205019787838982475 := by
  unfold tailWord_4303738
  simp only [CollatzResearch.WordTrace]
  refine ⟨39242555120574930194395967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104646813654866480518389245 39242555120574930194395967)
  ·
    refine ⟨58863832680862395291593951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39242555120574930194395967 58863832680862395291593951)
    ·
      refine ⟨88295749021293592937390927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58863832680862395291593951 88295749021293592937390927)
      ·
        refine ⟨132443623531940389406086391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88295749021293592937390927 132443623531940389406086391)
        ·
          refine ⟨198665435297910584109129587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132443623531940389406086391 198665435297910584109129587)
          ·
            refine ⟨297998152946865876163694381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198665435297910584109129587 297998152946865876163694381)
            ·
              refine ⟨111749307355074703561385393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297998152946865876163694381 111749307355074703561385393)
              ·
                refine ⟨83811980516306027671039045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111749307355074703561385393 83811980516306027671039045)
                ·
                  refine ⟨15714746346807380188319821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83811980516306027671039045 15714746346807380188319821)
                  ·
                    refine ⟨5893029880052767570619933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15714746346807380188319821 5893029880052767570619933)
                    ·
                      refine ⟨2209886205019787838982475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893029880052767570619933 2209886205019787838982475)
                      ·
                        rfl

theorem cell23_4303738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_4303738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303738 prefixEnd_4303738 := by exact prefixLift 4303738
  have htrace : WordTrace (prefixWord ++ tailWord_4303738) baseStart_4303738 baseEnd_4303738 := by
    simpa [prefixWord, tailWord_4303738, baseEnd_4303738] using wordTrace_append hprefix tailTrace_4303738
  have hstable : (prefixWord ++ tailWord_4303738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303738).length < 2 ^ (prefixWord ++ tailWord_4303738).sum := by decide
  have hdescent : baseEnd_4303738 < baseStart_4303738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303765 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_4303765 : Nat := 118140960795 + 4303765 * 2 ^ 59
def prefixEnd_4303765 : Nat := 4983230072969 + 3 ^ 40 * 4303765 * 2
def baseEnd_4303765 : Nat := 2209900068997459233344851

theorem tailTrace_4303765 : CollatzResearch.WordTrace tailWord_4303765 prefixEnd_4303765 2209900068997459233344851 := by
  unfold tailWord_4303765
  simp only [CollatzResearch.WordTrace]
  refine ⟨156971205253201904388816749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104647470168801269592544499 156971205253201904388816749)
  ·
    refine ⟨58864201969950714145806281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156971205253201904388816749 58864201969950714145806281)
    ·
      refine ⟨44148151477463035609354711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58864201969950714145806281 44148151477463035609354711)
      ·
        refine ⟨66222227216194553414032067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44148151477463035609354711 66222227216194553414032067)
        ·
          refine ⟨99333340824291830121048101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66222227216194553414032067 99333340824291830121048101)
          ·
            refine ⟨18625001404554718147696519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99333340824291830121048101 18625001404554718147696519)
            ·
              refine ⟨27937502106832077221544779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18625001404554718147696519 27937502106832077221544779)
              ·
                refine ⟨41906253160248115832317169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27937502106832077221544779 41906253160248115832317169)
                ·
                  refine ⟨31429689870186086874237877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41906253160248115832317169 31429689870186086874237877)
                  ·
                    refine ⟨2946533425329945644459801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31429689870186086874237877 2946533425329945644459801)
                    ·
                      refine ⟨2209900068997459233344851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946533425329945644459801 2209900068997459233344851)
                      ·
                        rfl

theorem cell23_4303765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_4303765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303765 prefixEnd_4303765 := by exact prefixLift 4303765
  have htrace : WordTrace (prefixWord ++ tailWord_4303765) baseStart_4303765 baseEnd_4303765 := by
    simpa [prefixWord, tailWord_4303765, baseEnd_4303765] using wordTrace_append hprefix tailTrace_4303765
  have hstable : (prefixWord ++ tailWord_4303765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303765).length < 2 ^ (prefixWord ++ tailWord_4303765).sum := by decide
  have hdescent : baseEnd_4303765 < baseStart_4303765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303772 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4303772 : Nat := 118140960795 + 4303772 * 2 ^ 59
def prefixEnd_4303772 : Nat := 4983230072969 + 3 ^ 40 * 4303772 * 2
def baseEnd_4303772 : Nat := 2209903663362040705957319

theorem tailTrace_4303772 : CollatzResearch.WordTrace tailWord_4303772 prefixEnd_4303772 2209903663362040705957319 := by
  unfold tailWord_4303772
  simp only [CollatzResearch.WordTrace]
  refine ⟨78485730282088272292160785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104647640376117696389547713 78485730282088272292160785)
  ·
    refine ⟨58864297711566204219120589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78485730282088272292160785 58864297711566204219120589)
    ·
      refine ⟨22074111641837326582170221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58864297711566204219120589 22074111641837326582170221)
      ·
        refine ⟨8277791865688997468313833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22074111641837326582170221 8277791865688997468313833)
        ·
          refine ⟨6208343899266748101235375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8277791865688997468313833 6208343899266748101235375)
          ·
            refine ⟨9312515848900122151853063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6208343899266748101235375 9312515848900122151853063)
            ·
              refine ⟨13968773773350183227779595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9312515848900122151853063 13968773773350183227779595)
              ·
                refine ⟨20953160660025274841669393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13968773773350183227779595 20953160660025274841669393)
                ·
                  refine ⟨15714870495018956131252045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20953160660025274841669393 15714870495018956131252045)
                  ·
                    refine ⟨5893076435632108549219517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15714870495018956131252045 5893076435632108549219517)
                    ·
                      refine ⟨2209903663362040705957319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893076435632108549219517 2209903663362040705957319)
                      ·
                        rfl

theorem cell23_4303772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4303772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303772 prefixEnd_4303772 := by exact prefixLift 4303772
  have htrace : WordTrace (prefixWord ++ tailWord_4303772) baseStart_4303772 baseEnd_4303772 := by
    simpa [prefixWord, tailWord_4303772, baseEnd_4303772] using wordTrace_append hprefix tailTrace_4303772
  have hstable : (prefixWord ++ tailWord_4303772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303772).length < 2 ^ (prefixWord ++ tailWord_4303772).sum := by decide
  have hdescent : baseEnd_4303772 < baseStart_4303772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303808 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_4303808 : Nat := 118140960795 + 4303808 * 2 ^ 59
def prefixEnd_4303808 : Nat := 4983230072969 + 3 ^ 40 * 4303808 * 2
def baseEnd_4303808 : Nat := 2209922148665602565107153

theorem tailTrace_4303808 : CollatzResearch.WordTrace tailWord_4303808 prefixEnd_4303808 2209922148665602565107153 := by
  unfold tailWord_4303808
  simp only [CollatzResearch.WordTrace]
  refine ⟨78486386796023061366316039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104648515728030748488421385 78486386796023061366316039)
  ·
    refine ⟨117729580194034592049474059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78486386796023061366316039 117729580194034592049474059)
    ·
      refine ⟨176594370291051888074211089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117729580194034592049474059 176594370291051888074211089)
      ·
        refine ⟨132445777718288916055658317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176594370291051888074211089 132445777718288916055658317)
        ·
          refine ⟨49667166644358343520871869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132445777718288916055658317 49667166644358343520871869)
          ·
            refine ⟨18625187491634378820326951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49667166644358343520871869 18625187491634378820326951)
            ·
              refine ⟨27937781237451568230490427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18625187491634378820326951 27937781237451568230490427)
              ·
                refine ⟨41906671856177352345735641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27937781237451568230490427 41906671856177352345735641)
                ·
                  refine ⟨31430003892133014259301731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41906671856177352345735641 31430003892133014259301731)
                  ·
                    refine ⟨47145005838199521388952597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31430003892133014259301731 47145005838199521388952597)
                    ·
                      refine ⟨2209922148665602565107153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47145005838199521388952597 2209922148665602565107153)
                      ·
                        rfl

theorem cell23_4303808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_4303808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303808 prefixEnd_4303808 := by exact prefixLift 4303808
  have htrace : WordTrace (prefixWord ++ tailWord_4303808) baseStart_4303808 baseEnd_4303808 := by
    simpa [prefixWord, tailWord_4303808, baseEnd_4303808] using wordTrace_append hprefix tailTrace_4303808
  have hstable : (prefixWord ++ tailWord_4303808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303808).length < 2 ^ (prefixWord ++ tailWord_4303808).sum := by decide
  have hdescent : baseEnd_4303808 < baseStart_4303808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303815 : List Nat := [1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3]
def baseStart_4303815 : Nat := 118140960795 + 4303815 * 2 ^ 59
def prefixEnd_4303815 : Nat := 4983230072969 + 3 ^ 40 * 4303815 * 2
def baseEnd_4303815 : Nat := 2209925743030184037719621

theorem tailTrace_4303815 : CollatzResearch.WordTrace tailWord_4303815 prefixEnd_4303815 2209925743030184037719621 := by
  unfold tailWord_4303815
  simp only [CollatzResearch.WordTrace]
  refine ⟨156973028903020762928136899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104648685935347175285424599 156973028903020762928136899)
  ·
    refine ⟨235459543354531144392205349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156973028903020762928136899 235459543354531144392205349)
    ·
      refine ⟨44148664378974589573538503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235459543354531144392205349 44148664378974589573538503)
      ·
        refine ⟨66222996568461884360307755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44148664378974589573538503 66222996568461884360307755)
        ·
          refine ⟨99334494852692826540461633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66222996568461884360307755 99334494852692826540461633)
          ·
            refine ⟨74500871139519619905346225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99334494852692826540461633 74500871139519619905346225)
            ·
              refine ⟨55875653354639714929009669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74500871139519619905346225 55875653354639714929009669)
              ·
                refine ⟨10476685003994946549189313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55875653354639714929009669 10476685003994946549189313)
                ·
                  refine ⟨7857513752996209911891985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10476685003994946549189313 7857513752996209911891985)
                  ·
                    refine ⟨5893135314747157433918989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7857513752996209911891985 5893135314747157433918989)
                    ·
                      refine ⟨2209925743030184037719621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893135314747157433918989 2209925743030184037719621)
                      ·
                        rfl

theorem cell23_4303815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_4303815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303815 prefixEnd_4303815 := by exact prefixLift 4303815
  have htrace : WordTrace (prefixWord ++ tailWord_4303815) baseStart_4303815 baseEnd_4303815 := by
    simpa [prefixWord, tailWord_4303815, baseEnd_4303815] using wordTrace_append hprefix tailTrace_4303815
  have hstable : (prefixWord ++ tailWord_4303815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303815).length < 2 ^ (prefixWord ++ tailWord_4303815).sum := by decide
  have hdescent : baseEnd_4303815 < baseStart_4303815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303822 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_4303822 : Nat := 118140960795 + 4303822 * 2 ^ 59
def prefixEnd_4303822 : Nat := 4983230072969 + 3 ^ 40 * 4303822 * 2
def baseEnd_4303822 : Nat := 736643112464921836777363

theorem tailTrace_4303822 : CollatzResearch.WordTrace tailWord_4303822 prefixEnd_4303822 736643112464921836777363 := by
  unfold tailWord_4303822
  simp only [CollatzResearch.WordTrace]
  refine ⟨19621660526749425390455215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104648856142663602082427813 19621660526749425390455215)
  ·
    refine ⟨29432490790124138085682823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19621660526749425390455215 29432490790124138085682823)
    ·
      refine ⟨44148736185186207128524235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29432490790124138085682823 44148736185186207128524235)
      ·
        refine ⟨66223104277779310692786353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44148736185186207128524235 66223104277779310692786353)
        ·
          refine ⟨49667328208334483019589765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66223104277779310692786353 49667328208334483019589765)
          ·
            refine ⟨9312624039062715566173081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49667328208334483019589765 9312624039062715566173081)
            ·
              refine ⟨6984468029297036674629811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9312624039062715566173081 6984468029297036674629811)
              ·
                refine ⟨10476702043945555011944717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984468029297036674629811 10476702043945555011944717)
                ·
                  refine ⟨3928763266479583129479269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10476702043945555011944717 3928763266479583129479269)
                  ·
                    refine ⟨736643112464921836777363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928763266479583129479269 736643112464921836777363)
                    ·
                      rfl

theorem cell23_4303822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_4303822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303822 prefixEnd_4303822 := by exact prefixLift 4303822
  have htrace : WordTrace (prefixWord ++ tailWord_4303822) baseStart_4303822 baseEnd_4303822 := by
    simpa [prefixWord, tailWord_4303822, baseEnd_4303822] using wordTrace_append hprefix tailTrace_4303822
  have hstable : (prefixWord ++ tailWord_4303822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303822).length < 2 ^ (prefixWord ++ tailWord_4303822).sum := by decide
  have hdescent : baseEnd_4303822 < baseStart_4303822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303865 : List Nat := [1, 2, 1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_4303865 : Nat := 118140960795 + 4303865 * 2 ^ 59
def prefixEnd_4303865 : Nat := 4983230072969 + 3 ^ 40 * 4303865 * 2
def baseEnd_4303865 : Nat := 736650472354302947364797

theorem tailTrace_4303865 : CollatzResearch.WordTrace tailWord_4303865 prefixEnd_4303865 736650472354302947364797 := by
  unfold tailWord_4303865
  simp only [CollatzResearch.WordTrace]
  refine ⟨156974852552839621467457049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104649901701893080978304699 156974852552839621467457049)
  ·
    refine ⟨117731139414629716100592787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156974852552839621467457049 117731139414629716100592787)
    ·
      refine ⟨176596709121944574150889181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117731139414629716100592787 176596709121944574150889181)
      ·
        refine ⟨66223765920729215306583443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176596709121944574150889181 66223765920729215306583443)
        ·
          refine ⟨99335648881093822959875165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66223765920729215306583443 99335648881093822959875165)
          ·
            refine ⟨37250868330410183609953187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99335648881093822959875165 37250868330410183609953187)
            ·
              refine ⟨55876302495615275414929781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37250868330410183609953187 55876302495615275414929781)
              ·
                refine ⟨5238403358963932070149667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55876302495615275414929781 5238403358963932070149667)
                ·
                  refine ⟨7857605038445898105224501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5238403358963932070149667 7857605038445898105224501)
                  ·
                    refine ⟨736650472354302947364797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7857605038445898105224501 736650472354302947364797)
                    ·
                      rfl

theorem cell23_4303865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_4303865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303865 prefixEnd_4303865 := by exact prefixLift 4303865
  have htrace : WordTrace (prefixWord ++ tailWord_4303865) baseStart_4303865 baseEnd_4303865 := by
    simpa [prefixWord, tailWord_4303865, baseEnd_4303865] using wordTrace_append hprefix tailTrace_4303865
  have hstable : (prefixWord ++ tailWord_4303865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303865).length < 2 ^ (prefixWord ++ tailWord_4303865).sum := by decide
  have hdescent : baseEnd_4303865 < baseStart_4303865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303915 : List Nat := [1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4]
def baseStart_4303915 : Nat := 118140960795 + 4303915 * 2 ^ 59
def prefixEnd_4303915 : Nat := 4983230072969 + 3 ^ 40 * 4303915 * 2
def baseEnd_4303915 : Nat := 2209977091095633646469161

theorem tailTrace_4303915 : CollatzResearch.WordTrace tailWord_4303915 prefixEnd_4303915 2209977091095633646469161 := by
  unfold tailWord_4303915
  simp only [CollatzResearch.WordTrace]
  refine ⟨156976676202658480006777199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104651117468438986671184799 156976676202658480006777199)
  ·
    refine ⟨235465014303987720010165799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156976676202658480006777199 235465014303987720010165799)
    ·
      refine ⟨353197521455981580015248699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235465014303987720010165799 353197521455981580015248699)
      ·
        refine ⟨529796282183972370022873049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353197521455981580015248699 529796282183972370022873049)
        ·
          refine ⟨397347211637979277517154787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529796282183972370022873049 397347211637979277517154787)
          ·
            refine ⟨596020817456968916275732181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397347211637979277517154787 596020817456968916275732181)
            ·
              refine ⟨13969237909147708975212473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 596020817456968916275732181 13969237909147708975212473)
              ·
                refine ⟨10476928431860781731409355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13969237909147708975212473 10476928431860781731409355)
                ·
                  refine ⟨15715392647791172597114033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10476928431860781731409355 15715392647791172597114033)
                  ·
                    refine ⟨11786544485843379447835525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15715392647791172597114033 11786544485843379447835525)
                    ·
                      refine ⟨2209977091095633646469161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11786544485843379447835525 2209977091095633646469161)
                      ·
                        rfl

theorem cell23_4303915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 4].length) (baseStart_4303915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303915 prefixEnd_4303915 := by exact prefixLift 4303915
  have htrace : WordTrace (prefixWord ++ tailWord_4303915) baseStart_4303915 baseEnd_4303915 := by
    simpa [prefixWord, tailWord_4303915, baseEnd_4303915] using wordTrace_append hprefix tailTrace_4303915
  have hstable : (prefixWord ++ tailWord_4303915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303915).length < 2 ^ (prefixWord ++ tailWord_4303915).sum := by decide
  have hdescent : baseEnd_4303915 < baseStart_4303915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303929 : List Nat := [1, 2, 1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_4303929 : Nat := 118140960795 + 4303929 * 2 ^ 59
def prefixEnd_4303929 : Nat := 4983230072969 + 3 ^ 40 * 4303929 * 2
def baseEnd_4303929 : Nat := 736661426608265530564699

theorem tailTrace_4303929 : CollatzResearch.WordTrace tailWord_4303929 prefixEnd_4303929 736661426608265530564699 := by
  unfold tailWord_4303929
  simp only [CollatzResearch.WordTrace]
  refine ⟨156977186824607760397786841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104651457883071840265191227 156977186824607760397786841)
  ·
    refine ⟨117732890118455820298340131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156977186824607760397786841 117732890118455820298340131)
    ·
      refine ⟨176599335177683730447510197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117732890118455820298340131 176599335177683730447510197)
      ·
        refine ⟨16556187672907849729454081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176599335177683730447510197 16556187672907849729454081)
        ·
          refine ⟨12417140754680887297090561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16556187672907849729454081 12417140754680887297090561)
          ·
            refine ⟨9312855566010665472817921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12417140754680887297090561 9312855566010665472817921)
            ·
              refine ⟨6984641674507999104613441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9312855566010665472817921 6984641674507999104613441)
              ·
                refine ⟨5238481255880999328460081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6984641674507999104613441 5238481255880999328460081)
                ·
                  refine ⟨3928860941910749496345061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5238481255880999328460081 3928860941910749496345061)
                  ·
                    refine ⟨736661426608265530564699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3928860941910749496345061 736661426608265530564699)
                    ·
                      rfl

theorem cell23_4303929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_4303929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303929 prefixEnd_4303929 := by exact prefixLift 4303929
  have htrace : WordTrace (prefixWord ++ tailWord_4303929) baseStart_4303929 baseEnd_4303929 := by
    simpa [prefixWord, tailWord_4303929, baseEnd_4303929] using wordTrace_append hprefix tailTrace_4303929
  have hstable : (prefixWord ++ tailWord_4303929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303929).length < 2 ^ (prefixWord ++ tailWord_4303929).sum := by decide
  have hdescent : baseEnd_4303929 < baseStart_4303929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303935 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_4303935 : Nat := 118140960795 + 4303935 * 2 ^ 59
def prefixEnd_4303935 : Nat := 4983230072969 + 3 ^ 40 * 4303935 * 2
def baseEnd_4303935 : Nat := 2209987360708723568219069

theorem tailTrace_4303935 : CollatzResearch.WordTrace tailWord_4303935 prefixEnd_4303935 2209987360708723568219069 := by
  unfold tailWord_4303935
  simp only [CollatzResearch.WordTrace]
  refine ⟨156977405662586023422505259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104651603775057348948336839 156977405662586023422505259)
  ·
    refine ⟨235466108493879035133757889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156977405662586023422505259 235466108493879035133757889)
    ·
      refine ⟨176599581370409276350318417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235466108493879035133757889 176599581370409276350318417)
      ·
        refine ⟨132449686027806957262738813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176599581370409276350318417 132449686027806957262738813)
        ·
          refine ⟨49668632260427608973527055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132449686027806957262738813 49668632260427608973527055)
          ·
            refine ⟨74502948390641413460290583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49668632260427608973527055 74502948390641413460290583)
            ·
              refine ⟨111754422585962120190435875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74502948390641413460290583 111754422585962120190435875)
              ·
                refine ⟨167631633878943180285653813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111754422585962120190435875 167631633878943180285653813)
                ·
                  refine ⟨15715465676150923151780045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167631633878943180285653813 15715465676150923151780045)
                  ·
                    refine ⟨5893299628556596181917517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15715465676150923151780045 5893299628556596181917517)
                    ·
                      refine ⟨2209987360708723568219069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893299628556596181917517 2209987360708723568219069)
                      ·
                        rfl

theorem cell23_4303935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_4303935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303935 prefixEnd_4303935 := by exact prefixLift 4303935
  have htrace : WordTrace (prefixWord ++ tailWord_4303935) baseStart_4303935 baseEnd_4303935 := by
    simpa [prefixWord, tailWord_4303935, baseEnd_4303935] using wordTrace_append hprefix tailTrace_4303935
  have hstable : (prefixWord ++ tailWord_4303935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303935).length < 2 ^ (prefixWord ++ tailWord_4303935).sum := by decide
  have hdescent : baseEnd_4303935 < baseStart_4303935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303936 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 1, 2, 2]
def baseStart_4303936 : Nat := 118140960795 + 4303936 * 2 ^ 59
def prefixEnd_4303936 : Nat := 4983230072969 + 3 ^ 40 * 4303936 * 2
def baseEnd_4303936 : Nat := 2209987874189378064306565

theorem tailTrace_4303936 : CollatzResearch.WordTrace tailWord_4303936 prefixEnd_4303936 2209987874189378064306565 := by
  unfold tailWord_4303936
  simp only [CollatzResearch.WordTrace]
  refine ⟨78488721067791200296645831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104651628090388267062194441 78488721067791200296645831)
  ·
    refine ⟨117733081601686800444968747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78488721067791200296645831 117733081601686800444968747)
    ·
      refine ⟨176599622402530200667453121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117733081601686800444968747 176599622402530200667453121)
      ·
        refine ⟨132449716801897650500589841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176599622402530200667453121 132449716801897650500589841)
        ·
          refine ⟨99337287601423237875442381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132449716801897650500589841 99337287601423237875442381)
          ·
            refine ⟨37251482850533714203290893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 99337287601423237875442381 37251482850533714203290893)
            ·
              refine ⟨13969306068950142826234085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37251482850533714203290893 13969306068950142826234085)
              ·
                refine ⟨2619244887928151779918891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13969306068950142826234085 2619244887928151779918891)
                ·
                  refine ⟨3928867331892227669878337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619244887928151779918891 3928867331892227669878337)
                  ·
                    refine ⟨2946650498919170752408753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928867331892227669878337 2946650498919170752408753)
                    ·
                      refine ⟨2209987874189378064306565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946650498919170752408753 2209987874189378064306565)
                      ·
                        rfl

theorem cell23_4303936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_4303936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303936 prefixEnd_4303936 := by exact prefixLift 4303936
  have htrace : WordTrace (prefixWord ++ tailWord_4303936) baseStart_4303936 baseEnd_4303936 := by
    simpa [prefixWord, tailWord_4303936, baseEnd_4303936] using wordTrace_append hprefix tailTrace_4303936
  have hstable : (prefixWord ++ tailWord_4303936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303936).length < 2 ^ (prefixWord ++ tailWord_4303936).sum := by decide
  have hdescent : baseEnd_4303936 < baseStart_4303936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303949 : List Nat := [1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4303949 : Nat := 118140960795 + 4303949 * 2 ^ 59
def prefixEnd_4303949 : Nat := 4983230072969 + 3 ^ 40 * 4303949 * 2
def baseEnd_4303949 : Nat := 2209994549437886513444005

theorem tailTrace_4303949 : CollatzResearch.WordTrace tailWord_4303949 prefixEnd_4303949 2209994549437886513444005 := by
  unfold tailWord_4303949
  simp only [CollatzResearch.WordTrace]
  refine ⟨156977916284535303813514901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104651944189690202542343267 156977916284535303813514901)
  ·
    refine ⟨7358339825837592366258511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 156977916284535303813514901 7358339825837592366258511)
    ·
      refine ⟨11037509738756388549387767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7358339825837592366258511 11037509738756388549387767)
      ·
        refine ⟨16556264608134582824081651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11037509738756388549387767 16556264608134582824081651)
        ·
          refine ⟨24834396912201874236122477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16556264608134582824081651 24834396912201874236122477)
          ·
            refine ⟨9312898842075702838545929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24834396912201874236122477 9312898842075702838545929)
            ·
              refine ⟨6984674131556777128909447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9312898842075702838545929 6984674131556777128909447)
              ·
                refine ⟨10477011197335165693364171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984674131556777128909447 10477011197335165693364171)
                ·
                  refine ⟨15715516796002748540046257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10477011197335165693364171 15715516796002748540046257)
                  ·
                    refine ⟨11786637597002061405034693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15715516796002748540046257 11786637597002061405034693)
                    ·
                      refine ⟨2209994549437886513444005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11786637597002061405034693 2209994549437886513444005)
                      ·
                        rfl

theorem cell23_4303949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4303949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303949 prefixEnd_4303949 := by exact prefixLift 4303949
  have htrace : WordTrace (prefixWord ++ tailWord_4303949) baseStart_4303949 baseEnd_4303949 := by
    simpa [prefixWord, tailWord_4303949, baseEnd_4303949] using wordTrace_append hprefix tailTrace_4303949
  have hstable : (prefixWord ++ tailWord_4303949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303949).length < 2 ^ (prefixWord ++ tailWord_4303949).sum := by decide
  have hdescent : baseEnd_4303949 < baseStart_4303949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303966 : List Nat := [4, 4, 1, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4303966 : Nat := 118140960795 + 4303966 * 2 ^ 59
def prefixEnd_4303966 : Nat := 4983230072969 + 3 ^ 40 * 4303966 * 2
def baseEnd_4303966 : Nat := 2210003278609012946931427

theorem tailTrace_4303966 : CollatzResearch.WordTrace tailWord_4303966 prefixEnd_4303966 2210003278609012946931427 := by
  unfold tailWord_4303966
  simp only [CollatzResearch.WordTrace]
  refine ⟨19622317040684214464610469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104652357550315810477922501 19622317040684214464610469)
  ·
    refine ⟨3679184445128290212114463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19622317040684214464610469 3679184445128290212114463)
    ·
      refine ⟨5518776667692435318171695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679184445128290212114463 5518776667692435318171695)
      ·
        refine ⟨8278165001538652977257543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5518776667692435318171695 8278165001538652977257543)
        ·
          refine ⟨12417247502307979465886315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278165001538652977257543 12417247502307979465886315)
          ·
            refine ⟨18625871253461969198829473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12417247502307979465886315 18625871253461969198829473)
            ·
              refine ⟨13969403440096476899122105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18625871253461969198829473 13969403440096476899122105)
              ·
                refine ⟨10477052580072357674341579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13969403440096476899122105 10477052580072357674341579)
                ·
                  refine ⟨15715578870108536511512369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10477052580072357674341579 15715578870108536511512369)
                  ·
                    refine ⟨11786684152581402383634277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15715578870108536511512369 11786684152581402383634277)
                    ·
                      refine ⟨2210003278609012946931427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11786684152581402383634277 2210003278609012946931427)
                      ·
                        rfl

theorem cell23_4303966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4303966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303966 prefixEnd_4303966 := by exact prefixLift 4303966
  have htrace : WordTrace (prefixWord ++ tailWord_4303966) baseStart_4303966 baseEnd_4303966 := by
    simpa [prefixWord, tailWord_4303966, baseEnd_4303966] using wordTrace_append hprefix tailTrace_4303966
  have hstable : (prefixWord ++ tailWord_4303966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303966).length < 2 ^ (prefixWord ++ tailWord_4303966).sum := by decide
  have hdescent : baseEnd_4303966 < baseStart_4303966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303970 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4303970 : Nat := 118140960795 + 4303970 * 2 ^ 59
def prefixEnd_4303970 : Nat := 4983230072969 + 3 ^ 40 * 4303970 * 2
def baseEnd_4303970 : Nat := 2210005332531630931281409

theorem tailTrace_4303970 : CollatzResearch.WordTrace tailWord_4303970 prefixEnd_4303970 2210005332531630931281409 := by
  unfold tailWord_4303970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39244670554364806100007341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104652454811639482933352909 39244670554364806100007341)
  ·
    refine ⟨14716751457886802287502753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39244670554364806100007341 14716751457886802287502753)
    ·
      refine ⟨11037563593415101715627065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14716751457886802287502753 11037563593415101715627065)
      ·
        refine ⟨8278172695061326286720299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037563593415101715627065 8278172695061326286720299)
        ·
          refine ⟨12417259042591989430080449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278172695061326286720299 12417259042591989430080449)
          ·
            refine ⟨9312944281943992072560337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12417259042591989430080449 9312944281943992072560337)
            ·
              refine ⟨6984708211457994054420253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9312944281943992072560337 6984708211457994054420253)
              ·
                refine ⟨2619265579296747770407595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6984708211457994054420253 2619265579296747770407595)
                ·
                  refine ⟨3928898368945121655611393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619265579296747770407595 3928898368945121655611393)
                  ·
                    refine ⟨2946673776708841241708545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928898368945121655611393 2946673776708841241708545)
                    ·
                      refine ⟨2210005332531630931281409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946673776708841241708545 2210005332531630931281409)
                      ·
                        rfl

theorem cell23_4303970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4303970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303970 prefixEnd_4303970 := by exact prefixLift 4303970
  have htrace : WordTrace (prefixWord ++ tailWord_4303970) baseStart_4303970 baseEnd_4303970 := by
    simpa [prefixWord, tailWord_4303970, baseEnd_4303970] using wordTrace_append hprefix tailTrace_4303970
  have hstable : (prefixWord ++ tailWord_4303970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303970).length < 2 ^ (prefixWord ++ tailWord_4303970).sum := by decide
  have hdescent : baseEnd_4303970 < baseStart_4303970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303992 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2]
def baseStart_4303992 : Nat := 118140960795 + 4303992 * 2 ^ 59
def prefixEnd_4303992 : Nat := 4983230072969 + 3 ^ 40 * 4303992 * 2
def baseEnd_4303992 : Nat := 2210016629106029845206307

theorem tailTrace_4303992 : CollatzResearch.WordTrace tailWord_4303992 prefixEnd_4303992 2210016629106029845206307 := by
  unfold tailWord_4303992
  simp only [CollatzResearch.WordTrace]
  refine ⟨78489742311689761078665115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104652989748919681438220153 78489742311689761078665115)
  ·
    refine ⟨117734613467534641617997673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78489742311689761078665115 117734613467534641617997673)
    ·
      refine ⟨88300960100650981213498255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117734613467534641617997673 88300960100650981213498255)
      ·
        refine ⟨132451440150976471820247383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88300960100650981213498255 132451440150976471820247383)
        ·
          refine ⟨198677160226464707730371075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132451440150976471820247383 198677160226464707730371075)
          ·
            refine ⟨298015740339697061595556613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198677160226464707730371075 298015740339697061595556613)
            ·
              refine ⟨55877951313693199049166865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298015740339697061595556613 55877951313693199049166865)
              ·
                refine ⟨41908463485269899286875149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55877951313693199049166865 41908463485269899286875149)
                ·
                  refine ⟨15715673806976212232578181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41908463485269899286875149 15715673806976212232578181)
                  ·
                    refine ⟨2946688838808039793608409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15715673806976212232578181 2946688838808039793608409)
                    ·
                      refine ⟨2210016629106029845206307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946688838808039793608409 2210016629106029845206307)
                      ·
                        rfl

theorem cell23_4303992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_4303992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303992 prefixEnd_4303992 := by exact prefixLift 4303992
  have htrace : WordTrace (prefixWord ++ tailWord_4303992) baseStart_4303992 baseEnd_4303992 := by
    simpa [prefixWord, tailWord_4303992, baseEnd_4303992] using wordTrace_append hprefix tailTrace_4303992
  have hstable : (prefixWord ++ tailWord_4303992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303992).length < 2 ^ (prefixWord ++ tailWord_4303992).sum := by decide
  have hdescent : baseEnd_4303992 < baseStart_4303992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4303995 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3]
def baseStart_4303995 : Nat := 118140960795 + 4303995 * 2 ^ 59
def prefixEnd_4303995 : Nat := 4983230072969 + 3 ^ 40 * 4303995 * 2
def baseEnd_4303995 : Nat := 2210018169547993333468793

theorem tailTrace_4303995 : CollatzResearch.WordTrace tailWord_4303995 prefixEnd_4303995 2210018169547993333468793 := by
  unfold tailWord_4303995
  simp only [CollatzResearch.WordTrace]
  refine ⟨156979594042368653669689439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104653062694912435779792959 156979594042368653669689439)
  ·
    refine ⟨235469391063552980504534159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156979594042368653669689439 235469391063552980504534159)
    ·
      refine ⟨353204086595329470756801239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235469391063552980504534159 353204086595329470756801239)
      ·
        refine ⟨529806129892994206135201859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353204086595329470756801239 529806129892994206135201859)
        ·
          refine ⟨794709194839491309202802789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529806129892994206135201859 794709194839491309202802789)
          ·
            refine ⟨149007974032404620475525523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 794709194839491309202802789 149007974032404620475525523)
            ·
              refine ⟨223511961048606930713288285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149007974032404620475525523 223511961048606930713288285)
              ·
                refine ⟨83816985393227599017483107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223511961048606930713288285 83816985393227599017483107)
                ·
                  refine ⟨125725478089841398526224661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83816985393227599017483107 125725478089841398526224661)
                  ·
                    refine ⟨5893381785461315555916781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125725478089841398526224661 5893381785461315555916781)
                    ·
                      refine ⟨2210018169547993333468793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893381785461315555916781 2210018169547993333468793)
                      ·
                        rfl

theorem cell23_4303995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 6, 3].length) (baseStart_4303995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4303995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4303995 prefixEnd_4303995 := by exact prefixLift 4303995
  have htrace : WordTrace (prefixWord ++ tailWord_4303995) baseStart_4303995 baseEnd_4303995 := by
    simpa [prefixWord, tailWord_4303995, baseEnd_4303995] using wordTrace_append hprefix tailTrace_4303995
  have hstable : (prefixWord ++ tailWord_4303995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4303995).length < 2 ^ (prefixWord ++ tailWord_4303995).sum := by decide
  have hdescent : baseEnd_4303995 < baseStart_4303995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4303995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304009 : List Nat := [1, 2, 1, 1, 4, 3, 3, 1, 1, 4, 2]
def baseStart_4304009 : Nat := 118140960795 + 4304009 * 2 ^ 59
def prefixEnd_4304009 : Nat := 4983230072969 + 3 ^ 40 * 4304009 * 2
def baseEnd_4304009 : Nat := 2210025358277156278693729

theorem tailTrace_4304009 : CollatzResearch.WordTrace tailWord_4304009 prefixEnd_4304009 2210025358277156278693729 := by
  unfold tailWord_4304009
  simp only [CollatzResearch.WordTrace]
  refine ⟨156980104664317934060699081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104653403109545289373799387 156980104664317934060699081)
  ·
    refine ⟨117735078498238450545524311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156980104664317934060699081 117735078498238450545524311)
    ·
      refine ⟨176602617747357675818286467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117735078498238450545524311 176602617747357675818286467)
      ·
        refine ⟨264903926621036513727429701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176602617747357675818286467 264903926621036513727429701)
        ·
          refine ⟨49669486241444346323893069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 264903926621036513727429701 49669486241444346323893069)
          ·
            refine ⟨18626057340541629871459901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49669486241444346323893069 18626057340541629871459901)
            ·
              refine ⟨6984771502703111201797463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18626057340541629871459901 6984771502703111201797463)
              ·
                refine ⟨10477157254054666802696195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984771502703111201797463 10477157254054666802696195)
                ·
                  refine ⟨15715735881082000204044293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10477157254054666802696195 15715735881082000204044293)
                  ·
                    refine ⟨2946700477702875038258305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15715735881082000204044293 2946700477702875038258305)
                    ·
                      refine ⟨2210025358277156278693729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946700477702875038258305 2210025358277156278693729)
                      ·
                        rfl

theorem cell23_4304009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 4, 2].length) (baseStart_4304009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304009 prefixEnd_4304009 := by exact prefixLift 4304009
  have htrace : WordTrace (prefixWord ++ tailWord_4304009) baseStart_4304009 baseEnd_4304009 := by
    simpa [prefixWord, tailWord_4304009, baseEnd_4304009] using wordTrace_append hprefix tailTrace_4304009
  have hstable : (prefixWord ++ tailWord_4304009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304009).length < 2 ^ (prefixWord ++ tailWord_4304009).sum := by decide
  have hdescent : baseEnd_4304009 < baseStart_4304009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304026 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4304026 : Nat := 118140960795 + 4304026 * 2 ^ 59
def prefixEnd_4304026 : Nat := 4983230072969 + 3 ^ 40 * 4304026 * 2
def baseEnd_4304026 : Nat := 2210034087448282712181151

theorem tailTrace_4304026 : CollatzResearch.WordTrace tailWord_4304026 prefixEnd_4304026 2210034087448282712181151 := by
  unfold tailWord_4304026
  simp only [CollatzResearch.WordTrace]
  refine ⟨39245181176314086491016983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104653816470170897309378621 39245181176314086491016983)
  ·
    refine ⟨58867771764471129736525475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39245181176314086491016983 58867771764471129736525475)
    ·
      refine ⟨88301657646706694604788213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58867771764471129736525475 88301657646706694604788213)
      ·
        refine ⟨8278280404378752619198895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88301657646706694604788213 8278280404378752619198895)
        ·
          refine ⟨12417420606568128928798343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278280404378752619198895 12417420606568128928798343)
          ·
            refine ⟨18626130909852193393197515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12417420606568128928798343 18626130909852193393197515)
            ·
              refine ⟨27939196364778290089796273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18626130909852193393197515 27939196364778290089796273)
              ·
                refine ⟨20954397273583717567347205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27939196364778290089796273 20954397273583717567347205)
                ·
                  refine ⟨3928949488796947043877601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20954397273583717567347205 3928949488796947043877601)
                  ·
                    refine ⟨2946712116597710282908201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928949488796947043877601 2946712116597710282908201)
                    ·
                      refine ⟨2210034087448282712181151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946712116597710282908201 2210034087448282712181151)
                      ·
                        rfl

theorem cell23_4304026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4304026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304026 prefixEnd_4304026 := by exact prefixLift 4304026
  have htrace : WordTrace (prefixWord ++ tailWord_4304026) baseStart_4304026 baseEnd_4304026 := by
    simpa [prefixWord, tailWord_4304026, baseEnd_4304026] using wordTrace_append hprefix tailTrace_4304026
  have hstable : (prefixWord ++ tailWord_4304026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304026).length < 2 ^ (prefixWord ++ tailWord_4304026).sum := by decide
  have hdescent : baseEnd_4304026 < baseStart_4304026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304049 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 7]
def baseStart_4304049 : Nat := 118140960795 + 4304049 * 2 ^ 59
def prefixEnd_4304049 : Nat := 4983230072969 + 3 ^ 40 * 4304049 * 2
def baseEnd_4304049 : Nat := 245560655278148458021505

theorem tailTrace_4304049 : CollatzResearch.WordTrace tailWord_4304049 prefixEnd_4304049 245560655278148458021505 := by
  unfold tailWord_4304049
  simp only [CollatzResearch.WordTrace]
  refine ⟨156981563584173020892155201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104654375722782013928103467 156981563584173020892155201)
  ·
    refine ⟨117736172688129765669116401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156981563584173020892155201 117736172688129765669116401)
    ·
      refine ⟨88302129516097324251837301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117736172688129765669116401 88302129516097324251837301)
      ·
        refine ⟨8278324642134124148609747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88302129516097324251837301 8278324642134124148609747)
        ·
          refine ⟨12417486963201186222914621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278324642134124148609747 12417486963201186222914621)
          ·
            refine ⟨4656557611200444833592983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12417486963201186222914621 4656557611200444833592983)
            ·
              refine ⟨6984836416800667250389475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656557611200444833592983 6984836416800667250389475)
              ·
                refine ⟨10477254625201000875584213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6984836416800667250389475 10477254625201000875584213)
                ·
                  refine ⟨245560655278148458021505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10477254625201000875584213 245560655278148458021505)
                  ·
                    rfl

theorem cell23_4304049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_4304049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304049 prefixEnd_4304049 := by exact prefixLift 4304049
  have htrace : WordTrace (prefixWord ++ tailWord_4304049) baseStart_4304049 baseEnd_4304049 := by
    simpa [prefixWord, tailWord_4304049, baseEnd_4304049] using wordTrace_append hprefix tailTrace_4304049
  have hstable : (prefixWord ++ tailWord_4304049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304049).length < 2 ^ (prefixWord ++ tailWord_4304049).sum := by decide
  have hdescent : baseEnd_4304049 < baseStart_4304049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304054 : List Nat := [5, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4304054 : Nat := 118140960795 + 4304054 * 2 ^ 59
def prefixEnd_4304054 : Nat := 4983230072969 + 3 ^ 40 * 4304054 * 2
def baseEnd_4304054 : Nat := 2210048464906608602631023

theorem tailTrace_4304054 : CollatzResearch.WordTrace tailWord_4304054 prefixEnd_4304054 2210048464906608602631023 := by
  unfold tailWord_4304054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9811359121822181671630451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104654497299436604497391477 9811359121822181671630451)
  ·
    refine ⟨14717038682733272507445677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9811359121822181671630451 14717038682733272507445677)
    ·
      refine ⟨5518889506024977190292129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14717038682733272507445677 5518889506024977190292129)
      ·
        refine ⟨4139167129518732892719097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5518889506024977190292129 4139167129518732892719097)
        ·
          refine ⟨3104375347139049669539323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139167129518732892719097 3104375347139049669539323)
          ·
            refine ⟨4656563020708574504308985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104375347139049669539323 4656563020708574504308985)
            ·
              refine ⟨3492422265531430878231739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4656563020708574504308985 3492422265531430878231739)
              ·
                refine ⟨5238633398297146317347609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492422265531430878231739 5238633398297146317347609)
                ·
                  refine ⟨3928975048722859738010707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5238633398297146317347609 3928975048722859738010707)
                  ·
                    refine ⟨5893462573084289607016061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3928975048722859738010707 5893462573084289607016061)
                    ·
                      refine ⟨2210048464906608602631023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893462573084289607016061 2210048464906608602631023)
                      ·
                        rfl

theorem cell23_4304054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4304054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304054 prefixEnd_4304054 := by exact prefixLift 4304054
  have htrace : WordTrace (prefixWord ++ tailWord_4304054) baseStart_4304054 baseEnd_4304054 := by
    simpa [prefixWord, tailWord_4304054, baseEnd_4304054] using wordTrace_append hprefix tailTrace_4304054
  have hstable : (prefixWord ++ tailWord_4304054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304054).length < 2 ^ (prefixWord ++ tailWord_4304054).sum := by decide
  have hdescent : baseEnd_4304054 < baseStart_4304054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304060 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 2, 2, 2]
def baseStart_4304060 : Nat := 118140960795 + 4304060 * 2 ^ 59
def prefixEnd_4304060 : Nat := 4983230072969 + 3 ^ 40 * 4304060 * 2
def baseEnd_4304060 : Nat := 2210051545790535579155995

theorem tailTrace_4304060 : CollatzResearch.WordTrace tailWord_4304060 prefixEnd_4304060 2210051545790535579155995 := by
  unfold tailWord_4304060
  simp only [CollatzResearch.WordTrace]
  refine ⟨78490982393566584885402817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104654643191422113180537089 78490982393566584885402817)
  ·
    refine ⟨58868236795174938664052113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78490982393566584885402817 58868236795174938664052113)
    ·
      refine ⟨44151177596381203998039085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58868236795174938664052113 44151177596381203998039085)
      ·
        refine ⟨16556691598642951499264657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44151177596381203998039085 16556691598642951499264657)
        ·
          refine ⟨12417518698982213624448493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16556691598642951499264657 12417518698982213624448493)
          ·
            refine ⟨4656569512118330109168185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12417518698982213624448493 4656569512118330109168185)
            ·
              refine ⟨3492427134088747581876139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4656569512118330109168185 3492427134088747581876139)
              ·
                refine ⟨5238640701133121372814209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492427134088747581876139 5238640701133121372814209)
                ·
                  refine ⟨3928980525849841029610657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5238640701133121372814209 3928980525849841029610657)
                  ·
                    refine ⟨2946735394387380772207993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3928980525849841029610657 2946735394387380772207993)
                    ·
                      refine ⟨2210051545790535579155995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946735394387380772207993 2210051545790535579155995)
                      ·
                        rfl

theorem cell23_4304060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_4304060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304060 prefixEnd_4304060 := by exact prefixLift 4304060
  have htrace : WordTrace (prefixWord ++ tailWord_4304060) baseStart_4304060 baseEnd_4304060 := by
    simpa [prefixWord, tailWord_4304060, baseEnd_4304060] using wordTrace_append hprefix tailTrace_4304060
  have hstable : (prefixWord ++ tailWord_4304060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304060).length < 2 ^ (prefixWord ++ tailWord_4304060).sum := by decide
  have hdescent : baseEnd_4304060 < baseStart_4304060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304122 : List Nat := [3, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_4304122 : Nat := 118140960795 + 4304122 * 2 ^ 59
def prefixEnd_4304122 : Nat := 4983230072969 + 3 ^ 40 * 4304122 * 2
def baseEnd_4304122 : Nat := 245564820176790481842301

theorem tailTrace_4304122 : CollatzResearch.WordTrace tailWord_4304122 prefixEnd_4304122 245564820176790481842301 := by
  unfold tailWord_4304122
  simp only [CollatzResearch.WordTrace]
  refine ⟨39246056528227138589890655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104656150741939036239708413 39246056528227138589890655)
  ·
    refine ⟨58869084792340707884835983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39246056528227138589890655 58869084792340707884835983)
    ·
      refine ⟨88303627188511061827253975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58869084792340707884835983 88303627188511061827253975)
      ·
        refine ⟨132455440782766592740880963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88303627188511061827253975 132455440782766592740880963)
        ·
          refine ⟨198683161174149889111321445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132455440782766592740880963 198683161174149889111321445)
          ·
            refine ⟨37253092720153104208372771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198683161174149889111321445 37253092720153104208372771)
            ·
              refine ⟨55879639080229656312559157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37253092720153104208372771 55879639080229656312559157)
              ·
                refine ⟨5238716163771530279302421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55879639080229656312559157 5238716163771530279302421)
                ·
                  refine ⟨245564820176790481842301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5238716163771530279302421 245564820176790481842301)
                  ·
                    rfl

theorem cell23_4304122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_4304122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304122 prefixEnd_4304122 := by exact prefixLift 4304122
  have htrace : WordTrace (prefixWord ++ tailWord_4304122) baseStart_4304122 baseEnd_4304122 := by
    simpa [prefixWord, tailWord_4304122, baseEnd_4304122] using wordTrace_append hprefix tailTrace_4304122
  have hstable : (prefixWord ++ tailWord_4304122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304122).length < 2 ^ (prefixWord ++ tailWord_4304122).sum := by decide
  have hdescent : baseEnd_4304122 < baseStart_4304122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304126 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4304126 : Nat := 118140960795 + 4304126 * 2 ^ 59
def prefixEnd_4304126 : Nat := 4983230072969 + 3 ^ 40 * 4304126 * 2
def baseEnd_4304126 : Nat := 736695145171244106976897

theorem tailTrace_4304126 : CollatzResearch.WordTrace tailWord_4304126 prefixEnd_4304126 736695145171244106976897 := by
  unfold tailWord_4304126
  simp only [CollatzResearch.WordTrace]
  refine ⟨19623046500611757880338529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104656248003262708695138821 19623046500611757880338529)
  ·
    refine ⟨14717284875458818410253897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19623046500611757880338529 14717284875458818410253897)
    ·
      refine ⟨11037963656594113807690423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14717284875458818410253897 11037963656594113807690423)
      ·
        refine ⟨16556945484891170711535635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11037963656594113807690423 16556945484891170711535635)
        ·
          refine ⟨24835418227336756067303453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16556945484891170711535635 24835418227336756067303453)
          ·
            refine ⟨9313281835251283525238795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24835418227336756067303453 9313281835251283525238795)
            ·
              refine ⟨13969922752876925287858193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9313281835251283525238795 13969922752876925287858193)
              ·
                refine ⟨10477442064657693965893645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13969922752876925287858193 10477442064657693965893645)
                ·
                  refine ⟨3929040774246635237210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10477442064657693965893645 3929040774246635237210117)
                  ·
                    refine ⟨736695145171244106976897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929040774246635237210117 736695145171244106976897)
                    ·
                      rfl

theorem cell23_4304126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4304126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304126 prefixEnd_4304126 := by exact prefixLift 4304126
  have htrace : WordTrace (prefixWord ++ tailWord_4304126) baseStart_4304126 baseEnd_4304126 := by
    simpa [prefixWord, tailWord_4304126, baseEnd_4304126] using wordTrace_append hprefix tailTrace_4304126
  have hstable : (prefixWord ++ tailWord_4304126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304126).length < 2 ^ (prefixWord ++ tailWord_4304126).sum := by decide
  have hdescent : baseEnd_4304126 < baseStart_4304126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304149 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_4304149 : Nat := 118140960795 + 4304149 * 2 ^ 59
def prefixEnd_4304149 : Nat := 4983230072969 + 3 ^ 40 * 4304149 * 2
def baseEnd_4304149 : Nat := 2210097245568785730943085

theorem tailTrace_4304149 : CollatzResearch.WordTrace tailWord_4304149 prefixEnd_4304149 2210097245568785730943085 := by
  unfold tailWord_4304149
  simp only [CollatzResearch.WordTrace]
  refine ⟨156985210883810737970795501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104656807255873825313863667 156985210883810737970795501)
  ·
    refine ⟨58869454081429026739048313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156985210883810737970795501 58869454081429026739048313)
    ·
      refine ⟨44152090561071770054286235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58869454081429026739048313 44152090561071770054286235)
      ·
        refine ⟨66228135841607655081429353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44152090561071770054286235 66228135841607655081429353)
        ·
          refine ⟨49671101881205741311072015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66228135841607655081429353 49671101881205741311072015)
          ·
            refine ⟨74506652821808611966608023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49671101881205741311072015 74506652821808611966608023)
            ·
              refine ⟨111759979232712917949912035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74506652821808611966608023 111759979232712917949912035)
              ·
                refine ⟨167639968849069376924868053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111759979232712917949912035 167639968849069376924868053)
                ·
                  refine ⟨3929061769900063521676595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 167639968849069376924868053 3929061769900063521676595)
                  ·
                    refine ⟨5893592654850095282514893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929061769900063521676595 5893592654850095282514893)
                    ·
                      refine ⟨2210097245568785730943085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893592654850095282514893 2210097245568785730943085)
                      ·
                        rfl

theorem cell23_4304149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_4304149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304149 prefixEnd_4304149 := by exact prefixLift 4304149
  have htrace : WordTrace (prefixWord ++ tailWord_4304149) baseStart_4304149 baseEnd_4304149 := by
    simpa [prefixWord, tailWord_4304149, baseEnd_4304149] using wordTrace_append hprefix tailTrace_4304149
  have hstable : (prefixWord ++ tailWord_4304149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304149).length < 2 ^ (prefixWord ++ tailWord_4304149).sum := by decide
  have hdescent : baseEnd_4304149 < baseStart_4304149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304173 : List Nat := [1, 5, 3, 1, 1, 2, 3, 1, 6]
def baseStart_4304173 : Nat := 118140960795 + 4304173 * 2 ^ 59
def prefixEnd_4304173 : Nat := 4983230072969 + 3 ^ 40 * 4304173 * 2
def baseEnd_4304173 : Nat := 245567729900499293004775

theorem tailTrace_4304173 : CollatzResearch.WordTrace tailWord_4304173 prefixEnd_4304173 245567729900499293004775 := by
  unfold tailWord_4304173
  simp only [CollatzResearch.WordTrace]
  refine ⟨156986086235723790069669173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104657390823815860046446115 156986086235723790069669173)
  ·
    refine ⟨14717445584599105319031485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 156986086235723790069669173 14717445584599105319031485)
    ·
      refine ⟨5519042094224664494636807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14717445584599105319031485 5519042094224664494636807)
      ·
        refine ⟨8278563141336996741955211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5519042094224664494636807 8278563141336996741955211)
        ·
          refine ⟨12417844712005495112932817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278563141336996741955211 12417844712005495112932817)
          ·
            refine ⟨9313383534004121334699613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12417844712005495112932817 9313383534004121334699613)
            ·
              refine ⟨3492518825251545500512355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9313383534004121334699613 3492518825251545500512355)
              ·
                refine ⟨5238778237877318250768533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492518825251545500512355 5238778237877318250768533)
                ·
                  refine ⟨245567729900499293004775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5238778237877318250768533 245567729900499293004775)
                  ·
                    rfl

theorem cell23_4304173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_4304173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304173 prefixEnd_4304173 := by exact prefixLift 4304173
  have htrace : WordTrace (prefixWord ++ tailWord_4304173) baseStart_4304173 baseEnd_4304173 := by
    simpa [prefixWord, tailWord_4304173, baseEnd_4304173] using wordTrace_append hprefix tailTrace_4304173
  have hstable : (prefixWord ++ tailWord_4304173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304173).length < 2 ^ (prefixWord ++ tailWord_4304173).sum := by decide
  have hdescent : baseEnd_4304173 < baseStart_4304173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304192 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_4304192 : Nat := 118140960795 + 4304192 * 2 ^ 59
def prefixEnd_4304192 : Nat := 4983230072969 + 3 ^ 40 * 4304192 * 2
def baseEnd_4304192 : Nat := 2210119325236929062705387

theorem tailTrace_4304192 : CollatzResearch.WordTrace tailWord_4304192 prefixEnd_4304192 2210119325236929062705387 := by
  unfold tailWord_4304192
  simp only [CollatzResearch.WordTrace]
  refine ⟨78493389611327478157305415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104657852815103304209740553 78493389611327478157305415)
  ·
    refine ⟨117740084416991217235958123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78493389611327478157305415 117740084416991217235958123)
    ·
      refine ⟨176610126625486825853937185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117740084416991217235958123 176610126625486825853937185)
      ·
        refine ⟨132457594969115119390452889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176610126625486825853937185 132457594969115119390452889)
        ·
          refine ⟨99343196226836339542839667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132457594969115119390452889 99343196226836339542839667)
          ·
            refine ⟨149014794340254509314259501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99343196226836339542839667 149014794340254509314259501)
            ·
              refine ⟨55880547877595440992847313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149014794340254509314259501 55880547877595440992847313)
              ·
                refine ⟨41910410908196580744635485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55880547877595440992847313 41910410908196580744635485)
                ·
                  refine ⟨15716404090573717779238307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41910410908196580744635485 15716404090573717779238307)
                  ·
                    refine ⟨23574606135860576668857461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15716404090573717779238307 23574606135860576668857461)
                    ·
                      refine ⟨2210119325236929062705387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23574606135860576668857461 2210119325236929062705387)
                      ·
                        rfl

theorem cell23_4304192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_4304192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304192 prefixEnd_4304192 := by exact prefixLift 4304192
  have htrace : WordTrace (prefixWord ++ tailWord_4304192) baseStart_4304192 baseEnd_4304192 := by
    simpa [prefixWord, tailWord_4304192, baseEnd_4304192] using wordTrace_append hprefix tailTrace_4304192
  have hstable : (prefixWord ++ tailWord_4304192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304192).length < 2 ^ (prefixWord ++ tailWord_4304192).sum := by decide
  have hdescent : baseEnd_4304192 < baseStart_4304192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304199 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 4, 4]
def baseStart_4304199 : Nat := 118140960795 + 4304199 * 2 ^ 59
def prefixEnd_4304199 : Nat := 4983230072969 + 3 ^ 40 * 4304199 * 2
def baseEnd_4304199 : Nat := 736707639867170178439285

theorem tailTrace_4304199 : CollatzResearch.WordTrace tailWord_4304199 prefixEnd_4304199 736707639867170178439285 := by
  unfold tailWord_4304199
  simp only [CollatzResearch.WordTrace]
  refine ⟨156987034533629596510115651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104658023022419731006743767 156987034533629596510115651)
  ·
    refine ⟨235480551800444394765173477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156987034533629596510115651 235480551800444394765173477)
    ·
      refine ⟨44152603462583324018470027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235480551800444394765173477 44152603462583324018470027)
      ·
        refine ⟨66228905193874986027705041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44152603462583324018470027 66228905193874986027705041)
        ·
          refine ⟨49671678895406239520778781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66228905193874986027705041 49671678895406239520778781)
          ·
            refine ⟨18626879585777339820292043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49671678895406239520778781 18626879585777339820292043)
            ·
              refine ⟨27940319378666009730438065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18626879585777339820292043 27940319378666009730438065)
              ·
                refine ⟨20955239533999507297828549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27940319378666009730438065 20955239533999507297828549)
                ·
                  refine ⟨3929107412624907618342853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20955239533999507297828549 3929107412624907618342853)
                  ·
                    refine ⟨736707639867170178439285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929107412624907618342853 736707639867170178439285)
                    ·
                      rfl

theorem cell23_4304199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_4304199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304199 prefixEnd_4304199 := by exact prefixLift 4304199
  have htrace : WordTrace (prefixWord ++ tailWord_4304199) baseStart_4304199 baseEnd_4304199 := by
    simpa [prefixWord, tailWord_4304199, baseEnd_4304199] using wordTrace_append hprefix tailTrace_4304199
  have hstable : (prefixWord ++ tailWord_4304199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304199).length < 2 ^ (prefixWord ++ tailWord_4304199).sum := by decide
  have hdescent : baseEnd_4304199 < baseStart_4304199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304209 : List Nat := [1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_4304209 : Nat := 118140960795 + 4304209 * 2 ^ 59
def prefixEnd_4304209 : Nat := 4983230072969 + 3 ^ 40 * 4304209 * 2
def baseEnd_4304209 : Nat := 2210128054408055496192809

theorem tailTrace_4304209 : CollatzResearch.WordTrace tailWord_4304209 prefixEnd_4304209 2210128054408055496192809 := by
  unfold tailWord_4304209
  simp only [CollatzResearch.WordTrace]
  refine ⟨156987399263593368217979681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104658266175728912145319787 156987399263593368217979681)
  ·
    refine ⟨117740549447695026163484761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156987399263593368217979681 117740549447695026163484761)
    ·
      refine ⟨88305412085771269622613571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117740549447695026163484761 88305412085771269622613571)
      ·
        refine ⟨132458118128656904433920357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88305412085771269622613571 132458118128656904433920357)
        ·
          refine ⟨24835897149123169581360067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132458118128656904433920357 24835897149123169581360067)
          ·
            refine ⟨37253845723684754372040101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24835897149123169581360067 37253845723684754372040101)
            ·
              refine ⟨6985096073190891444757519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37253845723684754372040101 6985096073190891444757519)
              ·
                refine ⟨10477644109786337167136279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6985096073190891444757519 10477644109786337167136279)
                ·
                  refine ⟨15716466164679505750704419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10477644109786337167136279 15716466164679505750704419)
                  ·
                    refine ⟨23574699247019258626056629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15716466164679505750704419 23574699247019258626056629)
                    ·
                      refine ⟨2210128054408055496192809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23574699247019258626056629 2210128054408055496192809)
                      ·
                        rfl

theorem cell23_4304209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_4304209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304209 prefixEnd_4304209 := by exact prefixLift 4304209
  have htrace : WordTrace (prefixWord ++ tailWord_4304209) baseStart_4304209 baseEnd_4304209 := by
    simpa [prefixWord, tailWord_4304209, baseEnd_4304209] using wordTrace_append hprefix tailTrace_4304209
  have hstable : (prefixWord ++ tailWord_4304209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304209).length < 2 ^ (prefixWord ++ tailWord_4304209).sum := by decide
  have hdescent : baseEnd_4304209 < baseStart_4304209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304226 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4304226 : Nat := 118140960795 + 4304226 * 2 ^ 59
def prefixEnd_4304226 : Nat := 4983230072969 + 3 ^ 40 * 4304226 * 2
def baseEnd_4304226 : Nat := 2210136783579181929680231

theorem tailTrace_4304226 : CollatzResearch.WordTrace tailWord_4304226 prefixEnd_4304226 2210136783579181929680231 := by
  unfold tailWord_4304226
  simp only [CollatzResearch.WordTrace]
  refine ⟨39247004826132945030337133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104658679536354520080899021 39247004826132945030337133)
  ·
    refine ⟨14717626809799854386376425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39247004826132945030337133 14717626809799854386376425)
    ·
      refine ⟨11038220107349890789782319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14717626809799854386376425 11038220107349890789782319)
      ·
        refine ⟨16557330161024836184673479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11038220107349890789782319 16557330161024836184673479)
        ·
          refine ⟨24835995241537254277010219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16557330161024836184673479 24835995241537254277010219)
          ·
            refine ⟨37253992862305881415515329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24835995241537254277010219 37253992862305881415515329)
            ·
              refine ⟨27940494646729411061636497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37253992862305881415515329 27940494646729411061636497)
              ·
                refine ⟨20955370985047058296227373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27940494646729411061636497 20955370985047058296227373)
                ·
                  refine ⟨7858264119392646861085265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20955370985047058296227373 7858264119392646861085265)
                  ·
                    refine ⟨5893698089544485145813949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7858264119392646861085265 5893698089544485145813949)
                    ·
                      refine ⟨2210136783579181929680231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893698089544485145813949 2210136783579181929680231)
                      ·
                        rfl

theorem cell23_4304226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4304226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304226 prefixEnd_4304226 := by exact prefixLift 4304226
  have htrace : WordTrace (prefixWord ++ tailWord_4304226) baseStart_4304226 baseEnd_4304226 := by
    simpa [prefixWord, tailWord_4304226, baseEnd_4304226] using wordTrace_append hprefix tailTrace_4304226
  have hstable : (prefixWord ++ tailWord_4304226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304226).length < 2 ^ (prefixWord ++ tailWord_4304226).sum := by decide
  have hdescent : baseEnd_4304226 < baseStart_4304226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304239 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_4304239 : Nat := 118140960795 + 4304239 * 2 ^ 59
def prefixEnd_4304239 : Nat := 4983230072969 + 3 ^ 40 * 4304239 * 2
def baseEnd_4304239 : Nat := 2210143458827690378817671

theorem tailTrace_4304239 : CollatzResearch.WordTrace tailWord_4304239 prefixEnd_4304239 2210143458827690378817671 := by
  unfold tailWord_4304239
  simp only [CollatzResearch.WordTrace]
  refine ⟨156988493453484683341571771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104658995635656455561047847 156988493453484683341571771)
  ·
    refine ⟨235482740180227025012357657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156988493453484683341571771 235482740180227025012357657)
    ·
      refine ⟨176612055135170268759268243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235482740180227025012357657 176612055135170268759268243)
      ·
        refine ⟨264918082702755403138902365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176612055135170268759268243 264918082702755403138902365)
        ·
          refine ⟨99344281013533276177088387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264918082702755403138902365 99344281013533276177088387)
          ·
            refine ⟨149016421520299914265632581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99344281013533276177088387 149016421520299914265632581)
            ·
              refine ⟨27940579035056233924806109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149016421520299914265632581 27940579035056233924806109)
              ·
                refine ⟨10477717138146087721802291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27940579035056233924806109 10477717138146087721802291)
                ·
                  refine ⟨15716575707219131582703437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10477717138146087721802291 15716575707219131582703437)
                  ·
                    refine ⟨5893715890207174343513789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15716575707219131582703437 5893715890207174343513789)
                    ·
                      refine ⟨2210143458827690378817671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893715890207174343513789 2210143458827690378817671)
                      ·
                        rfl

theorem cell23_4304239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_4304239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304239 prefixEnd_4304239 := by exact prefixLift 4304239
  have htrace : WordTrace (prefixWord ++ tailWord_4304239) baseStart_4304239 baseEnd_4304239 := by
    simpa [prefixWord, tailWord_4304239, baseEnd_4304239] using wordTrace_append hprefix tailTrace_4304239
  have hstable : (prefixWord ++ tailWord_4304239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304239).length < 2 ^ (prefixWord ++ tailWord_4304239).sum := by decide
  have hdescent : baseEnd_4304239 < baseStart_4304239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304274 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_4304274 : Nat := 118140960795 + 4304274 * 2 ^ 59
def prefixEnd_4304274 : Nat := 4983230072969 + 3 ^ 40 * 4304274 * 2
def baseEnd_4304274 : Nat := 2210161430650597741880011

theorem tailTrace_4304274 : CollatzResearch.WordTrace tailWord_4304274 prefixEnd_4304274 2210161430650597741880011 := by
  unfold tailWord_4304274
  simp only [CollatzResearch.WordTrace]
  refine ⟨39247442502089471079773969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104659846672238589546063917 39247442502089471079773969)
  ·
    refine ⟨29435581876567103309830477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39247442502089471079773969 29435581876567103309830477)
    ·
      refine ⟨11038343203712663741186429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29435581876567103309830477 11038343203712663741186429)
      ·
        refine ⟨4139378701392248902944911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11038343203712663741186429 4139378701392248902944911)
        ·
          refine ⟨6209068052088373354417367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4139378701392248902944911 6209068052088373354417367)
          ·
            refine ⟨9313602078132560031626051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209068052088373354417367 9313602078132560031626051)
            ·
              refine ⟨13970403117198840047439077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9313602078132560031626051 13970403117198840047439077)
              ·
                refine ⟨2619450584474782508894827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13970403117198840047439077 2619450584474782508894827)
                ·
                  refine ⟨3929175876712173763342241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619450584474782508894827 3929175876712173763342241)
                  ·
                    refine ⟨2946881907534130322506681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929175876712173763342241 2946881907534130322506681)
                    ·
                      refine ⟨2210161430650597741880011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946881907534130322506681 2210161430650597741880011)
                      ·
                        rfl

theorem cell23_4304274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_4304274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304274 prefixEnd_4304274 := by exact prefixLift 4304274
  have htrace : WordTrace (prefixWord ++ tailWord_4304274) baseStart_4304274 baseEnd_4304274 := by
    simpa [prefixWord, tailWord_4304274, baseEnd_4304274] using wordTrace_append hprefix tailTrace_4304274
  have hstable : (prefixWord ++ tailWord_4304274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304274).length < 2 ^ (prefixWord ++ tailWord_4304274).sum := by decide
  have hdescent : baseEnd_4304274 < baseStart_4304274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304330 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2]
def baseStart_4304330 : Nat := 118140960795 + 4304330 * 2 ^ 59
def prefixEnd_4304330 : Nat := 4983230072969 + 3 ^ 40 * 4304330 * 2
def baseEnd_4304330 : Nat := 2210190185567249522779753

theorem tailTrace_4304330 : CollatzResearch.WordTrace tailWord_4304330 prefixEnd_4304330 2210190185567249522779753 := by
  unfold tailWord_4304330
  simp only [CollatzResearch.WordTrace]
  refine ⟨39247953124038751470783611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104661208330770003922089629 39247953124038751470783611)
  ·
    refine ⟨58871929686058127206175417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39247953124038751470783611 58871929686058127206175417)
    ·
      refine ⟨44153947264543595404631563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58871929686058127206175417 44153947264543595404631563)
      ·
        refine ⟨66230920896815393106947345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44153947264543595404631563 66230920896815393106947345)
        ·
          refine ⟨49673190672611544830210509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66230920896815393106947345 49673190672611544830210509)
          ·
            refine ⟨18627446502229329311328941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49673190672611544830210509 18627446502229329311328941)
            ·
              refine ⟨6985292438335998491748353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18627446502229329311328941 6985292438335998491748353)
              ·
                refine ⟨5238969328751998868811265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6985292438335998491748353 5238969328751998868811265)
                ·
                  refine ⟨3929226996563999151608449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5238969328751998868811265 3929226996563999151608449)
                  ·
                    refine ⟨2946920247422999363706337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929226996563999151608449 2946920247422999363706337)
                    ·
                      refine ⟨2210190185567249522779753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946920247422999363706337 2210190185567249522779753)
                      ·
                        rfl

theorem cell23_4304330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_4304330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304330 prefixEnd_4304330 := by exact prefixLift 4304330
  have htrace : WordTrace (prefixWord ++ tailWord_4304330) baseStart_4304330 baseEnd_4304330 := by
    simpa [prefixWord, tailWord_4304330, baseEnd_4304330] using wordTrace_append hprefix tailTrace_4304330
  have hstable : (prefixWord ++ tailWord_4304330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304330).length < 2 ^ (prefixWord ++ tailWord_4304330).sum := by decide
  have hdescent : baseEnd_4304330 < baseStart_4304330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304346 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3]
def baseStart_4304346 : Nat := 118140960795 + 4304346 * 2 ^ 59
def prefixEnd_4304346 : Nat := 4983230072969 + 3 ^ 40 * 4304346 * 2
def baseEnd_4304346 : Nat := 2210198401257721460179679

theorem tailTrace_4304346 : CollatzResearch.WordTrace tailWord_4304346 prefixEnd_4304346 2210198401257721460179679 := by
  unfold tailWord_4304346
  simp only [CollatzResearch.WordTrace]
  refine ⟨39248099016024260153929223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104661597376064693743811261 39248099016024260153929223)
  ·
    refine ⟨58872148524036390230893835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39248099016024260153929223 58872148524036390230893835)
    ·
      refine ⟨88308222786054585346340753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58872148524036390230893835 88308222786054585346340753)
      ·
        refine ⟨66231167089540939009755565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88308222786054585346340753 66231167089540939009755565)
        ·
          refine ⟨24836687658577852128658337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66231167089540939009755565 24836687658577852128658337)
          ·
            refine ⟨18627515743933389096493753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24836687658577852128658337 18627515743933389096493753)
            ·
              refine ⟨13970636807950041822370315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18627515743933389096493753 13970636807950041822370315)
              ·
                refine ⟨20955955211925062733555473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13970636807950041822370315 20955955211925062733555473)
                ·
                  refine ⟨15716966408943797050166605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20955955211925062733555473 15716966408943797050166605)
                  ·
                    refine ⟨5893862403353923893812477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15716966408943797050166605 5893862403353923893812477)
                    ·
                      refine ⟨2210198401257721460179679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5893862403353923893812477 2210198401257721460179679)
                      ·
                        rfl

theorem cell23_4304346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_4304346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304346 prefixEnd_4304346 := by exact prefixLift 4304346
  have htrace : WordTrace (prefixWord ++ tailWord_4304346) baseStart_4304346 baseEnd_4304346 := by
    simpa [prefixWord, tailWord_4304346, baseEnd_4304346] using wordTrace_append hprefix tailTrace_4304346
  have hstable : (prefixWord ++ tailWord_4304346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304346).length < 2 ^ (prefixWord ++ tailWord_4304346).sum := by decide
  have hdescent : baseEnd_4304346 < baseStart_4304346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304356 : List Nat := [2, 3, 1, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_4304356 : Nat := 118140960795 + 4304356 * 2 ^ 59
def prefixEnd_4304356 : Nat := 4983230072969 + 3 ^ 40 * 4304356 * 2
def baseEnd_4304356 : Nat := 2210203536064266421054633

theorem tailTrace_4304356 : CollatzResearch.WordTrace tailWord_4304356 prefixEnd_4304356 2210203536064266421054633 := by
  unfold tailWord_4304356
  simp only [CollatzResearch.WordTrace]
  refine ⟨78496380397030406161790461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104661840529373874882387281 78496380397030406161790461)
  ·
    refine ⟨29436142648886402310671423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78496380397030406161790461 29436142648886402310671423)
    ·
      refine ⟨44154213973329603466007135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29436142648886402310671423 44154213973329603466007135)
      ·
        refine ⟨66231320959994405199010703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44154213973329603466007135 66231320959994405199010703)
        ·
          refine ⟨99346981439991607798516055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66231320959994405199010703 99346981439991607798516055)
          ·
            refine ⟨149020472159987411697774083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99346981439991607798516055 149020472159987411697774083)
            ·
              refine ⟨223530708239981117546661125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149020472159987411697774083 223530708239981117546661125)
              ·
                refine ⟨41912007794996459539998961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223530708239981117546661125 41912007794996459539998961)
                ·
                  refine ⟨31434005846247344654999221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41912007794996459539998961 31434005846247344654999221)
                  ·
                    refine ⟨2946938048085688561406177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31434005846247344654999221 2946938048085688561406177)
                    ·
                      refine ⟨2210203536064266421054633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2946938048085688561406177 2210203536064266421054633)
                      ·
                        rfl

theorem cell23_4304356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_4304356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304356 prefixEnd_4304356 := by exact prefixLift 4304356
  have htrace : WordTrace (prefixWord ++ tailWord_4304356) baseStart_4304356 baseEnd_4304356 := by
    simpa [prefixWord, tailWord_4304356, baseEnd_4304356] using wordTrace_append hprefix tailTrace_4304356
  have hstable : (prefixWord ++ tailWord_4304356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304356).length < 2 ^ (prefixWord ++ tailWord_4304356).sum := by decide
  have hdescent : baseEnd_4304356 < baseStart_4304356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304366 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_4304366 : Nat := 118140960795 + 4304366 * 2 ^ 59
def prefixEnd_4304366 : Nat := 4983230072969 + 3 ^ 40 * 4304366 * 2
def baseEnd_4304366 : Nat := 736736223623603793976529

theorem tailTrace_4304366 : CollatzResearch.WordTrace tailWord_4304366 prefixEnd_4304366 736736223623603793976529 := by
  unfold tailWord_4304366
  simp only [CollatzResearch.WordTrace]
  refine ⟨19624140690503073003930619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104662083682683056020963301 19624140690503073003930619)
  ·
    refine ⟨29436211035754609505895929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19624140690503073003930619 29436211035754609505895929)
    ·
      refine ⟨22077158276815957129421947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29436211035754609505895929 22077158276815957129421947)
      ·
        refine ⟨33115737415223935694132921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22077158276815957129421947 33115737415223935694132921)
        ·
          refine ⟨24836803061417951770599691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33115737415223935694132921 24836803061417951770599691)
          ·
            refine ⟨37255204592126927655899537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24836803061417951770599691 37255204592126927655899537)
            ·
              refine ⟨27941403444095195741924653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37255204592126927655899537 27941403444095195741924653)
              ·
                refine ⟨10478026291535698403221745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27941403444095195741924653 10478026291535698403221745)
                ·
                  refine ⟨7858519718651773802416309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10478026291535698403221745 7858519718651773802416309)
                  ·
                    refine ⟨736736223623603793976529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7858519718651773802416309 736736223623603793976529)
                    ·
                      rfl

theorem cell23_4304366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_4304366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304366 prefixEnd_4304366 := by exact prefixLift 4304366
  have htrace : WordTrace (prefixWord ++ tailWord_4304366) baseStart_4304366 baseEnd_4304366 := by
    simpa [prefixWord, tailWord_4304366, baseEnd_4304366] using wordTrace_append hprefix tailTrace_4304366
  have hstable : (prefixWord ++ tailWord_4304366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304366).length < 2 ^ (prefixWord ++ tailWord_4304366).sum := by decide
  have hdescent : baseEnd_4304366 < baseStart_4304366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304370 : List Nat := [3, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_4304370 : Nat := 118140960795 + 4304370 * 2 ^ 59
def prefixEnd_4304370 : Nat := 4983230072969 + 3 ^ 40 * 4304370 * 2
def baseEnd_4304370 : Nat := 245578969421492151808841

theorem tailTrace_4304370 : CollatzResearch.WordTrace tailWord_4304370 prefixEnd_4304370 245578969421492151808841 := by
  unfold tailWord_4304370
  simp only [CollatzResearch.WordTrace]
  refine ⟨39248317854002523178647641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104662180944006728476393709 39248317854002523178647641)
  ·
    refine ⟨29436238390501892383985731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39248317854002523178647641 29436238390501892383985731)
    ·
      refine ⟨44154357585752838575978597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29436238390501892383985731 44154357585752838575978597)
      ·
        refine ⟨8278942047328657232995987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44154357585752838575978597 8278942047328657232995987)
        ·
          refine ⟨12418413070992985849493981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8278942047328657232995987 12418413070992985849493981)
          ·
            refine ⟨4656904901622369693560243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12418413070992985849493981 4656904901622369693560243)
            ·
              refine ⟨6985357352433554540340365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4656904901622369693560243 6985357352433554540340365)
              ·
                refine ⟨2619509007162582952627637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6985357352433554540340365 2619509007162582952627637)
                ·
                  refine ⟨245578969421492151808841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619509007162582952627637 245578969421492151808841)
                  ·
                    rfl

theorem cell23_4304370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_4304370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304370 prefixEnd_4304370 := by exact prefixLift 4304370
  have htrace : WordTrace (prefixWord ++ tailWord_4304370) baseStart_4304370 baseEnd_4304370 := by
    simpa [prefixWord, tailWord_4304370, baseEnd_4304370] using wordTrace_append hprefix tailTrace_4304370
  have hstable : (prefixWord ++ tailWord_4304370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304370).length < 2 ^ (prefixWord ++ tailWord_4304370).sum := by decide
  have hdescent : baseEnd_4304370 < baseStart_4304370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304447 : List Nat := [1, 1, 2, 2, 3, 5, 2, 2, 1, 4]
def baseStart_4304447 : Nat := 118140960795 + 4304447 * 2 ^ 59
def prefixEnd_4304447 : Nat := 4983230072969 + 3 ^ 40 * 4304447 * 2
def baseEnd_4304447 : Nat := 736750087601275188338905

theorem tailTrace_4304447 : CollatzResearch.WordTrace tailWord_4304447 prefixEnd_4304447 736750087601275188338905 := by
  unfold tailWord_4304447
  simp only [CollatzResearch.WordTrace]
  refine ⟨156996079836731134865143595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104664053224487423243429063 156996079836731134865143595)
  ·
    refine ⟨235494119755096702297715393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 156996079836731134865143595 235494119755096702297715393)
    ·
      refine ⟨176620589816322526723286545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235494119755096702297715393 176620589816322526723286545)
      ·
        refine ⟨132465442362241895042464909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176620589816322526723286545 132465442362241895042464909)
        ·
          refine ⟨49674540885840710640924341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132465442362241895042464909 49674540885840710640924341)
          ·
            refine ⟨4656988208047566622586657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49674540885840710640924341 4656988208047566622586657)
            ·
              refine ⟨3492741156035674966939993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4656988208047566622586657 3492741156035674966939993)
              ·
                refine ⟨2619555867026756225204995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3492741156035674966939993 2619555867026756225204995)
                ·
                  refine ⟨3929333800540134337807493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619555867026756225204995 3929333800540134337807493)
                  ·
                    refine ⟨736750087601275188338905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929333800540134337807493 736750087601275188338905)
                    ·
                      rfl

theorem cell23_4304447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2, 1, 4].length) (baseStart_4304447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304447 prefixEnd_4304447 := by exact prefixLift 4304447
  have htrace : WordTrace (prefixWord ++ tailWord_4304447) baseStart_4304447 baseEnd_4304447 := by
    simpa [prefixWord, tailWord_4304447, baseEnd_4304447] using wordTrace_append hprefix tailTrace_4304447
  have hstable : (prefixWord ++ tailWord_4304447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304447).length < 2 ^ (prefixWord ++ tailWord_4304447).sum := by decide
  have hdescent : baseEnd_4304447 < baseStart_4304447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304453 : List Nat := [1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_4304453 : Nat := 118140960795 + 4304453 * 2 ^ 59
def prefixEnd_4304453 : Nat := 4983230072969 + 3 ^ 40 * 4304453 * 2
def baseEnd_4304453 : Nat := 2210253343687752541541687

theorem tailTrace_4304453 : CollatzResearch.WordTrace tailWord_4304453 prefixEnd_4304453 2210253343687752541541687 := by
  unfold tailWord_4304453
  simp only [CollatzResearch.WordTrace]
  refine ⟨156996298674709397889862013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104664199116472931926574675 156996298674709397889862013)
  ·
    refine ⟨58873612003016024208698255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 156996298674709397889862013 58873612003016024208698255)
    ·
      refine ⟨88310418004524036313047383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58873612003016024208698255 88310418004524036313047383)
      ·
        refine ⟨132465627006786054469571075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88310418004524036313047383 132465627006786054469571075)
        ·
          refine ⟨198698440510179081704356613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132465627006786054469571075 198698440510179081704356613)
          ·
            refine ⟨37255957595658577819566865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198698440510179081704356613 37255957595658577819566865)
            ·
              refine ⟨27941968196743933364675149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37255957595658577819566865 27941968196743933364675149)
              ·
                refine ⟨10478238073778975011753181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27941968196743933364675149 10478238073778975011753181)
                ·
                  refine ⟨3929339277667115629407443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10478238073778975011753181 3929339277667115629407443)
                  ·
                    refine ⟨5894008916500673444111165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929339277667115629407443 5894008916500673444111165)
                    ·
                      refine ⟨2210253343687752541541687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894008916500673444111165 2210253343687752541541687)
                      ·
                        rfl

theorem cell23_4304453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_4304453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304453 prefixEnd_4304453 := by exact prefixLift 4304453
  have htrace : WordTrace (prefixWord ++ tailWord_4304453) baseStart_4304453 baseEnd_4304453 := by
    simpa [prefixWord, tailWord_4304453, baseEnd_4304453] using wordTrace_append hprefix tailTrace_4304453
  have hstable : (prefixWord ++ tailWord_4304453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304453).length < 2 ^ (prefixWord ++ tailWord_4304453).sum := by decide
  have hdescent : baseEnd_4304453 < baseStart_4304453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304490 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_4304490 : Nat := 118140960795 + 4304490 * 2 ^ 59
def prefixEnd_4304490 : Nat := 4983230072969 + 3 ^ 40 * 4304490 * 2
def baseEnd_4304490 : Nat := 736757447490656298926339

theorem tailTrace_4304490 : CollatzResearch.WordTrace tailWord_4304490 prefixEnd_4304490 736757447490656298926339 := by
  unfold tailWord_4304490
  simp only [CollatzResearch.WordTrace]
  refine ⟨39249412043893838302239731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104665098783716902139305949 39249412043893838302239731)
  ·
    refine ⟨58874118065840757453359597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39249412043893838302239731 58874118065840757453359597)
    ·
      refine ⟨22077794274690284045009849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58874118065840757453359597 22077794274690284045009849)
      ·
        refine ⟨16558345706017713033757387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22077794274690284045009849 16558345706017713033757387)
        ·
          refine ⟨24837518559026569550636081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16558345706017713033757387 24837518559026569550636081)
          ·
            refine ⟨18628138919269927162977061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24837518559026569550636081 18628138919269927162977061)
            ·
              refine ⟨3492776047363111343058199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18628138919269927162977061 3492776047363111343058199)
              ·
                refine ⟨5239164071044667014587299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3492776047363111343058199 5239164071044667014587299)
                ·
                  refine ⟨7858746106567000521880949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239164071044667014587299 7858746106567000521880949)
                  ·
                    refine ⟨736757447490656298926339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7858746106567000521880949 736757447490656298926339)
                    ·
                      rfl

theorem cell23_4304490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_4304490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304490 prefixEnd_4304490 := by exact prefixLift 4304490
  have htrace : WordTrace (prefixWord ++ tailWord_4304490) baseStart_4304490 baseEnd_4304490 := by
    simpa [prefixWord, tailWord_4304490, baseEnd_4304490] using wordTrace_append hprefix tailTrace_4304490
  have hstable : (prefixWord ++ tailWord_4304490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304490).length < 2 ^ (prefixWord ++ tailWord_4304490).sum := by decide
  have hdescent : baseEnd_4304490 < baseStart_4304490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304513 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4304513 : Nat := 118140960795 + 4304513 * 2 ^ 59
def prefixEnd_4304513 : Nat := 4983230072969 + 3 ^ 40 * 4304513 * 2
def baseEnd_4304513 : Nat := 2210284152527022306791411

theorem tailTrace_4304513 : CollatzResearch.WordTrace tailWord_4304513 prefixEnd_4304513 2210284152527022306791411 := by
  unfold tailWord_4304513
  simp only [CollatzResearch.WordTrace]
  refine ⟨156998487054492028137046193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104665658036328018758030795 156998487054492028137046193)
  ·
    refine ⟨117748865290869021102784645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 156998487054492028137046193 117748865290869021102784645)
    ·
      refine ⟨22077912242037941456772121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 117748865290869021102784645 22077912242037941456772121)
      ·
        refine ⟨16558434181528456092579091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22077912242037941456772121 16558434181528456092579091)
        ·
          refine ⟨24837651272292684138868637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16558434181528456092579091 24837651272292684138868637)
          ·
            refine ⟨9314119227109756552075739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24837651272292684138868637 9314119227109756552075739)
            ·
              refine ⟨13971178840664634828113609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314119227109756552075739 13971178840664634828113609)
              ·
                refine ⟨10478384130498476121085207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13971178840664634828113609 10478384130498476121085207)
                ·
                  refine ⟨15717576195747714181627811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10478384130498476121085207 15717576195747714181627811)
                  ·
                    refine ⟨23576364293621571272441717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15717576195747714181627811 23576364293621571272441717)
                    ·
                      refine ⟨2210284152527022306791411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23576364293621571272441717 2210284152527022306791411)
                      ·
                        rfl

theorem cell23_4304513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4304513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304513 prefixEnd_4304513 := by exact prefixLift 4304513
  have htrace : WordTrace (prefixWord ++ tailWord_4304513) baseStart_4304513 baseEnd_4304513 := by
    simpa [prefixWord, tailWord_4304513, baseEnd_4304513] using wordTrace_append hprefix tailTrace_4304513
  have hstable : (prefixWord ++ tailWord_4304513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304513).length < 2 ^ (prefixWord ++ tailWord_4304513).sum := by decide
  have hdescent : baseEnd_4304513 < baseStart_4304513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304544 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 1, 2, 2]
def baseStart_4304544 : Nat := 118140960795 + 4304544 * 2 ^ 59
def prefixEnd_4304544 : Nat := 4983230072969 + 3 ^ 40 * 4304544 * 2
def baseEnd_4304544 : Nat := 2210300070427311685503769

theorem tailTrace_4304544 : CollatzResearch.WordTrace tailWord_4304544 prefixEnd_4304544 2210300070427311685503769 := by
  unfold tailWord_4304544
  simp only [CollatzResearch.WordTrace]
  refine ⟨78499808858689860215712343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104666411811586480287616457 78499808858689860215712343)
  ·
    refine ⟨117749713288034790323568515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78499808858689860215712343 117749713288034790323568515)
    ·
      refine ⟨176624569932052185485352773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117749713288034790323568515 176624569932052185485352773)
      ·
        refine ⟨33117106862259784778503645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176624569932052185485352773 33117106862259784778503645)
        ·
          refine ⟨12418915073347419291938867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33117106862259784778503645 12418915073347419291938867)
          ·
            refine ⟨18628372610021128937908301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12418915073347419291938867 18628372610021128937908301)
            ·
              refine ⟨6985639728757923351715613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18628372610021128937908301 6985639728757923351715613)
              ·
                refine ⟨2619614898284221256893355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6985639728757923351715613 2619614898284221256893355)
                ·
                  refine ⟨3929422347426331885340033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619614898284221256893355 3929422347426331885340033)
                  ·
                    refine ⟨2947066760569748914005025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929422347426331885340033 2947066760569748914005025)
                    ·
                      refine ⟨2210300070427311685503769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947066760569748914005025 2210300070427311685503769)
                      ·
                        rfl

theorem cell23_4304544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_4304544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304544 prefixEnd_4304544 := by exact prefixLift 4304544
  have htrace : WordTrace (prefixWord ++ tailWord_4304544) baseStart_4304544 baseEnd_4304544 := by
    simpa [prefixWord, tailWord_4304544, baseEnd_4304544] using wordTrace_append hprefix tailTrace_4304544
  have hstable : (prefixWord ++ tailWord_4304544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304544).length < 2 ^ (prefixWord ++ tailWord_4304544).sum := by decide
  have hdescent : baseEnd_4304544 < baseStart_4304544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304576 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 8]
def baseStart_4304576 : Nat := 118140960795 + 4304576 * 2 ^ 59
def prefixEnd_4304576 : Nat := 4983230072969 + 3 ^ 40 * 4304576 * 2
def baseEnd_4304576 : Nat := 736772167269418520101207

theorem tailTrace_4304576 : CollatzResearch.WordTrace tailWord_4304576 prefixEnd_4304576 736772167269418520101207 := by
  unfold tailWord_4304576
  simp only [CollatzResearch.WordTrace]
  refine ⟨78500392426631894948294791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104667189902175859931059721 78500392426631894948294791)
  ·
    refine ⟨117750588639947842422442187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78500392426631894948294791 117750588639947842422442187)
    ·
      refine ⟨176625882959921763633663281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117750588639947842422442187 176625882959921763633663281)
      ·
        refine ⟨132469412219941322725247461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176625882959921763633663281 132469412219941322725247461)
        ·
          refine ⟨24838014791238998010983899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132469412219941322725247461 24838014791238998010983899)
          ·
            refine ⟨37257022186858497016475849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24838014791238998010983899 37257022186858497016475849)
            ·
              refine ⟨27942766640143872762356887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37257022186858497016475849 27942766640143872762356887)
              ·
                refine ⟨41914149960215809143535331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27942766640143872762356887 41914149960215809143535331)
                ·
                  refine ⟨62871224940323713715302997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41914149960215809143535331 62871224940323713715302997)
                  ·
                    refine ⟨736772167269418520101207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62871224940323713715302997 736772167269418520101207)
                    ·
                      rfl

theorem cell23_4304576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_4304576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304576 prefixEnd_4304576 := by exact prefixLift 4304576
  have htrace : WordTrace (prefixWord ++ tailWord_4304576) baseStart_4304576 baseEnd_4304576 := by
    simpa [prefixWord, tailWord_4304576, baseEnd_4304576] using wordTrace_append hprefix tailTrace_4304576
  have hstable : (prefixWord ++ tailWord_4304576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304576).length < 2 ^ (prefixWord ++ tailWord_4304576).sum := by decide
  have hdescent : baseEnd_4304576 < baseStart_4304576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304578 : List Nat := [3, 5, 1, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4304578 : Nat := 118140960795 + 4304578 * 2 ^ 59
def prefixEnd_4304578 : Nat := 4983230072969 + 3 ^ 40 * 4304578 * 2
def baseEnd_4304578 : Nat := 2210317528769564552478613

theorem tailTrace_4304578 : CollatzResearch.WordTrace tailWord_4304578 prefixEnd_4304578 2210317528769564552478613 := by
  unfold tailWord_4304578
  simp only [CollatzResearch.WordTrace]
  refine ⟨39250214449814136059540597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104667238532837696158774925 39250214449814136059540597)
  ·
    refine ⟨3679707604670075255581931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39250214449814136059540597 3679707604670075255581931)
    ·
      refine ⟨5519561407005112883372897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679707604670075255581931 5519561407005112883372897)
      ·
        refine ⟨4139671055253834662529673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5519561407005112883372897 4139671055253834662529673)
        ·
          refine ⟨3104753291440375996897255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139671055253834662529673 3104753291440375996897255)
          ·
            refine ⟨4657129937160563995345883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104753291440375996897255 4657129937160563995345883)
            ·
              refine ⟨6985694905740845993018825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657129937160563995345883 6985694905740845993018825)
              ·
                refine ⟨5239271179305634494764119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6985694905740845993018825 5239271179305634494764119)
                ·
                  refine ⟨7858906768958451742146179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239271179305634494764119 7858906768958451742146179)
                  ·
                    refine ⟨11788360153437677613219269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7858906768958451742146179 11788360153437677613219269)
                    ·
                      refine ⟨2210317528769564552478613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11788360153437677613219269 2210317528769564552478613)
                      ·
                        rfl

theorem cell23_4304578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4304578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304578 prefixEnd_4304578 := by exact prefixLift 4304578
  have htrace : WordTrace (prefixWord ++ tailWord_4304578) baseStart_4304578 baseEnd_4304578 := by
    simpa [prefixWord, tailWord_4304578, baseEnd_4304578] using wordTrace_append hprefix tailTrace_4304578
  have hstable : (prefixWord ++ tailWord_4304578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304578).length < 2 ^ (prefixWord ++ tailWord_4304578).sum := by decide
  have hdescent : baseEnd_4304578 < baseStart_4304578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304600 : List Nat := [2, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2]
def baseStart_4304600 : Nat := 118140960795 + 4304600 * 2 ^ 59
def prefixEnd_4304600 : Nat := 4983230072969 + 3 ^ 40 * 4304600 * 2
def baseEnd_4304600 : Nat := 2210328825343963466403511

theorem tailTrace_4304600 : CollatzResearch.WordTrace tailWord_4304600 prefixEnd_4304600 2210328825343963466403511 := by
  unfold tailWord_4304600
  simp only [CollatzResearch.WordTrace]
  refine ⟨78500830102588420997731627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104667773470117894663642169 78500830102588420997731627)
  ·
    refine ⟨117751245153882631496597441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78500830102588420997731627 117751245153882631496597441)
    ·
      refine ⟨88313433865411973622448081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117751245153882631496597441 88313433865411973622448081)
      ·
        refine ⟨66235075399058980216836061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88313433865411973622448081 66235075399058980216836061)
        ·
          refine ⟨24838153274647117581313523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66235075399058980216836061 24838153274647117581313523)
          ·
            refine ⟨37257229911970676371970285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24838153274647117581313523 37257229911970676371970285)
            ·
              refine ⟨13971461216989003639488857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37257229911970676371970285 13971461216989003639488857)
              ·
                refine ⟨10478595912741752729616643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13971461216989003639488857 10478595912741752729616643)
                ·
                  refine ⟨15717893869112629094424965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10478595912741752729616643 15717893869112629094424965)
                  ·
                    refine ⟨2947105100458617955204681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15717893869112629094424965 2947105100458617955204681)
                    ·
                      refine ⟨2210328825343963466403511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947105100458617955204681 2210328825343963466403511)
                      ·
                        rfl

theorem cell23_4304600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_4304600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304600 prefixEnd_4304600 := by exact prefixLift 4304600
  have htrace : WordTrace (prefixWord ++ tailWord_4304600) baseStart_4304600 baseEnd_4304600 := by
    simpa [prefixWord, tailWord_4304600, baseEnd_4304600] using wordTrace_append hprefix tailTrace_4304600
  have hstable : (prefixWord ++ tailWord_4304600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304600).length < 2 ^ (prefixWord ++ tailWord_4304600).sum := by decide
  have hdescent : baseEnd_4304600 < baseStart_4304600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304613 : List Nat := [1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4304613 : Nat := 118140960795 + 4304613 * 2 ^ 59
def prefixEnd_4304613 : Nat := 4983230072969 + 3 ^ 40 * 4304613 * 2
def baseEnd_4304613 : Nat := 2210335500592471915540951

theorem tailTrace_4304613 : CollatzResearch.WordTrace tailWord_4304613 prefixEnd_4304613 2210335500592471915540951 := by
  unfold tailWord_4304613
  simp only [CollatzResearch.WordTrace]
  refine ⟨157002134354129745215686493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104668089569419830143790995 157002134354129745215686493)
  ·
    refine ⟨58875800382798654455882435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157002134354129745215686493 58875800382798654455882435)
    ·
      refine ⟨88313700574197981683823653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58875800382798654455882435 88313700574197981683823653)
      ·
        refine ⟨16558818857662121565716935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88313700574197981683823653 16558818857662121565716935)
        ·
          refine ⟨24838228286493182348575403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16558818857662121565716935 24838228286493182348575403)
          ·
            refine ⟨37257342429739773522863105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24838228286493182348575403 37257342429739773522863105)
            ·
              refine ⟨27943006822304830142147329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37257342429739773522863105 27943006822304830142147329)
              ·
                refine ⟨20957255116728622606610497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27943006822304830142147329 20957255116728622606610497)
                ·
                  refine ⟨15717941337546466954957873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20957255116728622606610497 15717941337546466954957873)
                  ·
                    refine ⟨11788456003159850216218405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15717941337546466954957873 11788456003159850216218405)
                    ·
                      refine ⟨2210335500592471915540951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11788456003159850216218405 2210335500592471915540951)
                      ·
                        rfl

theorem cell23_4304613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4304613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304613 prefixEnd_4304613 := by exact prefixLift 4304613
  have htrace : WordTrace (prefixWord ++ tailWord_4304613) baseStart_4304613 baseEnd_4304613 := by
    simpa [prefixWord, tailWord_4304613, baseEnd_4304613] using wordTrace_append hprefix tailTrace_4304613
  have hstable : (prefixWord ++ tailWord_4304613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304613).length < 2 ^ (prefixWord ++ tailWord_4304613).sum := by decide
  have hdescent : baseEnd_4304613 < baseStart_4304613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304630 : List Nat := [5, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4304630 : Nat := 118140960795 + 4304630 * 2 ^ 59
def prefixEnd_4304630 : Nat := 4983230072969 + 3 ^ 40 * 4304630 * 2
def baseEnd_4304630 : Nat := 2210344229763598349028373

theorem tailTrace_4304630 : CollatzResearch.WordTrace tailWord_4304630 prefixEnd_4304630 2210344229763598349028373 := by
  unfold tailWord_4304630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9812672149691759819940959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104668502930045438079370229 9812672149691759819940959)
  ·
    refine ⟨14719008224537639729911439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9812672149691759819940959 14719008224537639729911439)
    ·
      refine ⟨22078512336806459594867159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14719008224537639729911439 22078512336806459594867159)
      ·
        refine ⟨33117768505209689392300739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22078512336806459594867159 33117768505209689392300739)
        ·
          refine ⟨49676652757814534088451109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33117768505209689392300739 49676652757814534088451109)
          ·
            refine ⟨9314372392090225141584583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49676652757814534088451109 9314372392090225141584583)
            ·
              refine ⟨13971558588135337712376875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314372392090225141584583 13971558588135337712376875)
              ·
                refine ⟨20957337882203006568565313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13971558588135337712376875 20957337882203006568565313)
                ·
                  refine ⟨15718003411652254926423985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20957337882203006568565313 15718003411652254926423985)
                  ·
                    refine ⟨11788502558739191194817989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15718003411652254926423985 11788502558739191194817989)
                    ·
                      refine ⟨2210344229763598349028373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11788502558739191194817989 2210344229763598349028373)
                      ·
                        rfl

theorem cell23_4304630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4304630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304630 prefixEnd_4304630 := by exact prefixLift 4304630
  have htrace : WordTrace (prefixWord ++ tailWord_4304630) baseStart_4304630 baseEnd_4304630 := by
    simpa [prefixWord, tailWord_4304630, baseEnd_4304630] using wordTrace_append hprefix tailTrace_4304630
  have hstable : (prefixWord ++ tailWord_4304630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304630).length < 2 ^ (prefixWord ++ tailWord_4304630).sum := by decide
  have hdescent : baseEnd_4304630 < baseStart_4304630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304700 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 3, 4]
def baseStart_4304700 : Nat := 118140960795 + 4304700 * 2 ^ 59
def prefixEnd_4304700 : Nat := 4983230072969 + 3 ^ 40 * 4304700 * 2
def baseEnd_4304700 : Nat := 736793391136471025051017

theorem tailTrace_4304700 : CollatzResearch.WordTrace tailWord_4304700 prefixEnd_4304700 736793391136471025051017 := by
  unfold tailWord_4304700
  simp only [CollatzResearch.WordTrace]
  refine ⟨78502653752407279537051777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104670205003209706049402369 78502653752407279537051777)
  ·
    refine ⟨58876990314305459652788833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78502653752407279537051777 58876990314305459652788833)
    ·
      refine ⟨44157742735729094739591625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58876990314305459652788833 44157742735729094739591625)
      ·
        refine ⟨33118307051796821054693719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44157742735729094739591625 33118307051796821054693719)
        ·
          refine ⟨49677460577695231582040579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33118307051796821054693719 49677460577695231582040579)
          ·
            refine ⟨74516190866542847373060869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49677460577695231582040579 74516190866542847373060869)
            ·
              refine ⟨13971785787476783882448913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74516190866542847373060869 13971785787476783882448913)
              ·
                refine ⟨10478839340607587911836685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13971785787476783882448913 10478839340607587911836685)
                ·
                  refine ⟨3929564752727845466938757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10478839340607587911836685 3929564752727845466938757)
                  ·
                    refine ⟨736793391136471025051017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929564752727845466938757 736793391136471025051017)
                    ·
                      rfl

theorem cell23_4304700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_4304700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304700 prefixEnd_4304700 := by exact prefixLift 4304700
  have htrace : WordTrace (prefixWord ++ tailWord_4304700) baseStart_4304700 baseEnd_4304700 := by
    simpa [prefixWord, tailWord_4304700, baseEnd_4304700] using wordTrace_append hprefix tailTrace_4304700
  have hstable : (prefixWord ++ tailWord_4304700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304700).length < 2 ^ (prefixWord ++ tailWord_4304700).sum := by decide
  have hdescent : baseEnd_4304700 < baseStart_4304700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304727 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3]
def baseStart_4304727 : Nat := 118140960795 + 4304727 * 2 ^ 59
def prefixEnd_4304727 : Nat := 4983230072969 + 3 ^ 40 * 4304727 * 2
def baseEnd_4304727 : Nat := 2210394037387084469515427

theorem tailTrace_4304727 : CollatzResearch.WordTrace tailWord_4304727 prefixEnd_4304727 2210394037387084469515427 := by
  unfold tailWord_4304727
  simp only [CollatzResearch.WordTrace]
  refine ⟨157006292275716742685336435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104670861517144495123557623 157006292275716742685336435)
  ·
    refine ⟨235509438413575114028004653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157006292275716742685336435 235509438413575114028004653)
    ·
      refine ⟨88316039405090667760501745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235509438413575114028004653 88316039405090667760501745)
      ·
        refine ⟨66237029553818000820376309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88316039405090667760501745 66237029553818000820376309)
        ·
          refine ⟨6209721520670437576910279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66237029553818000820376309 6209721520670437576910279)
          ·
            refine ⟨9314582281005656365365419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6209721520670437576910279 9314582281005656365365419)
            ·
              refine ⟨13971873421508484548048129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9314582281005656365365419 13971873421508484548048129)
              ·
                refine ⟨10478905066131363411036097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13971873421508484548048129 10478905066131363411036097)
                ·
                  refine ⟨7859178799598522558277073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10478905066131363411036097 7859178799598522558277073)
                  ·
                    refine ⟨5894384099698891918707805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7859178799598522558277073 5894384099698891918707805)
                    ·
                      refine ⟨2210394037387084469515427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894384099698891918707805 2210394037387084469515427)
                      ·
                        rfl

theorem cell23_4304727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_4304727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304727 prefixEnd_4304727 := by exact prefixLift 4304727
  have htrace : WordTrace (prefixWord ++ tailWord_4304727) baseStart_4304727 baseEnd_4304727 := by
    simpa [prefixWord, tailWord_4304727, baseEnd_4304727] using wordTrace_append hprefix tailTrace_4304727
  have hstable : (prefixWord ++ tailWord_4304727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304727).length < 2 ^ (prefixWord ++ tailWord_4304727).sum := by decide
  have hdescent : baseEnd_4304727 < baseStart_4304727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304757 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_4304757 : Nat := 118140960795 + 4304757 * 2 ^ 59
def prefixEnd_4304757 : Nat := 4983230072969 + 3 ^ 40 * 4304757 * 2
def baseEnd_4304757 : Nat := 2210409441806719352140289

theorem tailTrace_4304757 : CollatzResearch.WordTrace tailWord_4304757 prefixEnd_4304757 2210409441806719352140289 := by
  unfold tailWord_4304757
  simp only [CollatzResearch.WordTrace]
  refine ⟨157007386465608057808928525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104671590977072038539285683 157007386465608057808928525)
  ·
    refine ⟨58877769924603021678348197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157007386465608057808928525 58877769924603021678348197)
    ·
      refine ⟨11039581860863066564690287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 58877769924603021678348197 11039581860863066564690287)
      ·
        refine ⟨16559372791294599847035431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11039581860863066564690287 16559372791294599847035431)
        ·
          refine ⟨24839059186941899770553147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16559372791294599847035431 24839059186941899770553147)
          ·
            refine ⟨37258588780412849655829721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24839059186941899770553147 37258588780412849655829721)
            ·
              refine ⟨27943941585309637241872291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37258588780412849655829721 27943941585309637241872291)
              ·
                refine ⟨41915912377964455862808437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27943941585309637241872291 41915912377964455862808437)
                ·
                  refine ⟨3929616785434167737138291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41915912377964455862808437 3929616785434167737138291)
                  ·
                    refine ⟨5894425178151251605707437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929616785434167737138291 5894425178151251605707437)
                    ·
                      refine ⟨2210409441806719352140289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894425178151251605707437 2210409441806719352140289)
                      ·
                        rfl

theorem cell23_4304757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_4304757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304757 prefixEnd_4304757 := by exact prefixLift 4304757
  have htrace : WordTrace (prefixWord ++ tailWord_4304757) baseStart_4304757 baseEnd_4304757 := by
    simpa [prefixWord, tailWord_4304757, baseEnd_4304757] using wordTrace_append hprefix tailTrace_4304757
  have hstable : (prefixWord ++ tailWord_4304757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304757).length < 2 ^ (prefixWord ++ tailWord_4304757).sum := by decide
  have hdescent : baseEnd_4304757 < baseStart_4304757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304777 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 1, 5]
def baseStart_4304777 : Nat := 118140960795 + 4304777 * 2 ^ 59
def prefixEnd_4304777 : Nat := 4983230072969 + 3 ^ 40 * 4304777 * 2
def baseEnd_4304777 : Nat := 736806570473269757963399

theorem tailTrace_4304777 : CollatzResearch.WordTrace tailWord_4304777 prefixEnd_4304777 736806570473269757963399 := by
  unfold tailWord_4304777
  simp only [CollatzResearch.WordTrace]
  refine ⟨157008115925535601224656585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104672077283690400816437723 157008115925535601224656585)
  ·
    refine ⟨117756086944151700918492439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157008115925535601224656585 117756086944151700918492439)
    ·
      refine ⟨176634130416227551377738659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117756086944151700918492439 176634130416227551377738659)
      ·
        refine ⟨264951195624341327066607989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176634130416227551377738659 264951195624341327066607989)
        ·
          refine ⟨24839174589781999412494499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 264951195624341327066607989 24839174589781999412494499)
          ·
            refine ⟨37258761884672999118741749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24839174589781999412494499 37258761884672999118741749)
            ·
              refine ⟨3493008926688093667382039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37258761884672999118741749 3493008926688093667382039)
              ·
                refine ⟨5239513390032140501073059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493008926688093667382039 5239513390032140501073059)
                ·
                  refine ⟨7859270085048210751609589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239513390032140501073059 7859270085048210751609589)
                  ·
                    refine ⟨736806570473269757963399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7859270085048210751609589 736806570473269757963399)
                    ·
                      rfl

theorem cell23_4304777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_4304777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304777 prefixEnd_4304777 := by exact prefixLift 4304777
  have htrace : WordTrace (prefixWord ++ tailWord_4304777) baseStart_4304777 baseEnd_4304777 := by
    simpa [prefixWord, tailWord_4304777, baseEnd_4304777] using wordTrace_append hprefix tailTrace_4304777
  have hstable : (prefixWord ++ tailWord_4304777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304777).length < 2 ^ (prefixWord ++ tailWord_4304777).sum := by decide
  have hdescent : baseEnd_4304777 < baseStart_4304777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304791 : List Nat := [1, 1, 3, 3, 1, 3, 4, 2, 1, 1, 3]
def baseStart_4304791 : Nat := 118140960795 + 4304791 * 2 ^ 59
def prefixEnd_4304791 : Nat := 4983230072969 + 3 ^ 40 * 4304791 * 2
def baseEnd_4304791 : Nat := 2210426900148972219115133

theorem tailTrace_4304791 : CollatzResearch.WordTrace tailWord_4304791 prefixEnd_4304791 2210426900148972219115133 := by
  unfold tailWord_4304791
  simp only [CollatzResearch.WordTrace]
  refine ⟨157008626547484881615666227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104672417698323254410444151 157008626547484881615666227)
  ·
    refine ⟨235512939821227322423499341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157008626547484881615666227 235512939821227322423499341)
    ·
      refine ⟨88317352432960245908812253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235512939821227322423499341 88317352432960245908812253)
      ·
        refine ⟨33119007162360092215804595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88317352432960245908812253 33119007162360092215804595)
        ·
          refine ⟨49678510743540138323706893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33119007162360092215804595 49678510743540138323706893)
          ·
            refine ⟨18629441528827551871390085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49678510743540138323706893 18629441528827551871390085)
            ·
              refine ⟨3493020286655165975885641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18629441528827551871390085 3493020286655165975885641)
              ·
                refine ⟨2619765214991374481914231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493020286655165975885641 2619765214991374481914231)
                ·
                  refine ⟨3929647822487061722871347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619765214991374481914231 3929647822487061722871347)
                  ·
                    refine ⟨5894471733730592584307021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929647822487061722871347 5894471733730592584307021)
                    ·
                      refine ⟨2210426900148972219115133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894471733730592584307021 2210426900148972219115133)
                      ·
                        rfl

theorem cell23_4304791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_4304791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304791 prefixEnd_4304791 := by exact prefixLift 4304791
  have htrace : WordTrace (prefixWord ++ tailWord_4304791) baseStart_4304791 baseEnd_4304791 := by
    simpa [prefixWord, tailWord_4304791, baseEnd_4304791] using wordTrace_append hprefix tailTrace_4304791
  have hstable : (prefixWord ++ tailWord_4304791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304791).length < 2 ^ (prefixWord ++ tailWord_4304791).sum := by decide
  have hdescent : baseEnd_4304791 < baseStart_4304791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304793 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_4304793 : Nat := 118140960795 + 4304793 * 2 ^ 59
def prefixEnd_4304793 : Nat := 4983230072969 + 3 ^ 40 * 4304793 * 2
def baseEnd_4304793 : Nat := 2210427927110281211290123

theorem tailTrace_4304793 : CollatzResearch.WordTrace tailWord_4304793 prefixEnd_4304793 2210427927110281211290123 := by
  unfold tailWord_4304793
  simp only [CollatzResearch.WordTrace]
  refine ⟨157008699493477635957239033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104672466328985090638159355 157008699493477635957239033)
  ·
    refine ⟨117756524620108226967929275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157008699493477635957239033 117756524620108226967929275)
    ·
      refine ⟨176634786930162340451893913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117756524620108226967929275 176634786930162340451893913)
      ·
        refine ⟨132476090197621755338920435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176634786930162340451893913 132476090197621755338920435)
        ·
          refine ⟨198714135296432633008380653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132476090197621755338920435 198714135296432633008380653)
          ·
            refine ⟨74517800736162237378142745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 198714135296432633008380653 74517800736162237378142745)
            ·
              refine ⟨55888350552121678033607059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74517800736162237378142745 55888350552121678033607059)
              ·
                refine ⟨83832525828182517050410589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55888350552121678033607059 83832525828182517050410589)
                ·
                  refine ⟨31437197185568443893903971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83832525828182517050410589 31437197185568443893903971)
                  ·
                    refine ⟨47155795778352665840855957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31437197185568443893903971 47155795778352665840855957)
                    ·
                      refine ⟨2210427927110281211290123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47155795778352665840855957 2210427927110281211290123)
                      ·
                        rfl

theorem cell23_4304793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_4304793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304793 prefixEnd_4304793 := by exact prefixLift 4304793
  have htrace : WordTrace (prefixWord ++ tailWord_4304793) baseStart_4304793 baseEnd_4304793 := by
    simpa [prefixWord, tailWord_4304793, baseEnd_4304793] using wordTrace_append hprefix tailTrace_4304793
  have hstable : (prefixWord ++ tailWord_4304793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304793).length < 2 ^ (prefixWord ++ tailWord_4304793).sum := by decide
  have hdescent : baseEnd_4304793 < baseStart_4304793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304807 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 1, 6]
def baseStart_4304807 : Nat := 118140960795 + 4304807 * 2 ^ 59
def prefixEnd_4304807 : Nat := 4983230072969 + 3 ^ 40 * 4304807 * 2
def baseEnd_4304807 : Nat := 736811705279814718838353

theorem tailTrace_4304807 : CollatzResearch.WordTrace tailWord_4304807 prefixEnd_4304807 736811705279814718838353 := by
  unfold tailWord_4304807
  simp only [CollatzResearch.WordTrace]
  refine ⟨157009210115426916348248675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104672806743617944232165783 157009210115426916348248675)
  ·
    refine ⟨235513815173140374522373013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157009210115426916348248675 235513815173140374522373013)
    ·
      refine ⟨11039710086240955055736235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 235513815173140374522373013 11039710086240955055736235)
      ·
        refine ⟨16559565129361432583604353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11039710086240955055736235 16559565129361432583604353)
        ·
          refine ⟨12419673847021074437703265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16559565129361432583604353 12419673847021074437703265)
          ·
            refine ⟨9314755385265805828277449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12419673847021074437703265 9314755385265805828277449)
            ·
              refine ⟨6986066538949354371208087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9314755385265805828277449 6986066538949354371208087)
              ·
                refine ⟨10479099808424031556812131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6986066538949354371208087 10479099808424031556812131)
                ·
                  refine ⟨15718649712636047335218197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10479099808424031556812131 15718649712636047335218197)
                  ·
                    refine ⟨736811705279814718838353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15718649712636047335218197 736811705279814718838353)
                    ·
                      rfl

theorem cell23_4304807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_4304807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304807 prefixEnd_4304807 := by exact prefixLift 4304807
  have htrace : WordTrace (prefixWord ++ tailWord_4304807) baseStart_4304807 baseEnd_4304807 := by
    simpa [prefixWord, tailWord_4304807, baseEnd_4304807] using wordTrace_append hprefix tailTrace_4304807
  have hstable : (prefixWord ++ tailWord_4304807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304807).length < 2 ^ (prefixWord ++ tailWord_4304807).sum := by decide
  have hdescent : baseEnd_4304807 < baseStart_4304807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304817 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4304817 : Nat := 118140960795 + 4304817 * 2 ^ 59
def prefixEnd_4304817 : Nat := 4983230072969 + 3 ^ 40 * 4304817 * 2
def baseEnd_4304817 : Nat := 2210440250645989117390013

theorem tailTrace_4304817 : CollatzResearch.WordTrace tailWord_4304817 prefixEnd_4304817 2210440250645989117390013 := by
  unfold tailWord_4304817
  simp only [CollatzResearch.WordTrace]
  refine ⟨157009574845390688056112705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104673049896927125370741803 157009574845390688056112705)
  ·
    refine ⟨117757181134043016042084529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157009574845390688056112705 117757181134043016042084529)
    ·
      refine ⟨88317885850532262031563397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117757181134043016042084529 88317885850532262031563397)
      ·
        refine ⟨16559603596974799130918137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88317885850532262031563397 16559603596974799130918137)
        ·
          refine ⟨12419702697731099348188603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16559603596974799130918137 12419702697731099348188603)
          ·
            refine ⟨18629554046596649022282905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12419702697731099348188603 18629554046596649022282905)
            ·
              refine ⟨13972165534947486766712179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18629554046596649022282905 13972165534947486766712179)
              ·
                refine ⟨20958248302421230150068269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13972165534947486766712179 20958248302421230150068269)
                ·
                  refine ⟨7859343113407961306275601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20958248302421230150068269 7859343113407961306275601)
                  ·
                    refine ⟨5894507335055970979706701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7859343113407961306275601 5894507335055970979706701)
                    ·
                      refine ⟨2210440250645989117390013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894507335055970979706701 2210440250645989117390013)
                      ·
                        rfl

theorem cell23_4304817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4304817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304817 prefixEnd_4304817 := by exact prefixLift 4304817
  have htrace : WordTrace (prefixWord ++ tailWord_4304817) baseStart_4304817 baseEnd_4304817 := by
    simpa [prefixWord, tailWord_4304817, baseEnd_4304817] using wordTrace_append hprefix tailTrace_4304817
  have hstable : (prefixWord ++ tailWord_4304817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304817).length < 2 ^ (prefixWord ++ tailWord_4304817).sum := by decide
  have hdescent : baseEnd_4304817 < baseStart_4304817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304828 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 1, 5]
def baseStart_4304828 : Nat := 118140960795 + 4304828 * 2 ^ 59
def prefixEnd_4304828 : Nat := 4983230072969 + 3 ^ 40 * 4304828 * 2
def baseEnd_4304828 : Nat := 736815299644396191450821

theorem tailTrace_4304828 : CollatzResearch.WordTrace tailWord_4304828 prefixEnd_4304828 736815299644396191450821 := by
  unfold tailWord_4304828
  simp only [CollatzResearch.WordTrace]
  refine ⟨78504988024175418467381569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104673317365567224623175425 78504988024175418467381569)
  ·
    refine ⟨58878741018131563850536177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78504988024175418467381569 58878741018131563850536177)
    ·
      refine ⟨44159055763598672887902133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58878741018131563850536177 44159055763598672887902133)
      ·
        refine ⟨4139911477837375583240825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44159055763598672887902133 4139911477837375583240825)
        ·
          refine ⟨3104933608378031687430619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4139911477837375583240825 3104933608378031687430619)
          ·
            refine ⟨4657400412567047531145929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104933608378031687430619 4657400412567047531145929)
            ·
              refine ⟨3493050309425285648359447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4657400412567047531145929 3493050309425285648359447)
              ·
                refine ⟨5239575464137928472539171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493050309425285648359447 5239575464137928472539171)
                ·
                  refine ⟨7859363196206892708808757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5239575464137928472539171 7859363196206892708808757)
                  ·
                    refine ⟨736815299644396191450821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7859363196206892708808757 736815299644396191450821)
                    ·
                      rfl

theorem cell23_4304828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_4304828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304828 prefixEnd_4304828 := by exact prefixLift 4304828
  have htrace : WordTrace (prefixWord ++ tailWord_4304828) baseStart_4304828 baseEnd_4304828 := by
    simpa [prefixWord, tailWord_4304828, baseEnd_4304828] using wordTrace_append hprefix tailTrace_4304828
  have hstable : (prefixWord ++ tailWord_4304828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304828).length < 2 ^ (prefixWord ++ tailWord_4304828).sum := by decide
  have hdescent : baseEnd_4304828 < baseStart_4304828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304831 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 1, 2, 2]
def baseStart_4304831 : Nat := 118140960795 + 4304831 * 2 ^ 59
def prefixEnd_4304831 : Nat := 4983230072969 + 3 ^ 40 * 4304831 * 2
def baseEnd_4304831 : Nat := 2210447439375152062614949

theorem tailTrace_4304831 : CollatzResearch.WordTrace tailWord_4304831 prefixEnd_4304831 2210447439375152062614949 := by
  unfold tailWord_4304831
  simp only [CollatzResearch.WordTrace]
  refine ⟨157010085467339968447122347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104673390311559978964748231 157010085467339968447122347)
  ·
    refine ⟨235515128201009952670683521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157010085467339968447122347 235515128201009952670683521)
    ·
      refine ⟨176636346150757464503012641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235515128201009952670683521 176636346150757464503012641)
      ·
        refine ⟨132477259613068098377259481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176636346150757464503012641 132477259613068098377259481)
        ·
          refine ⟨99357944709801073782944611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132477259613068098377259481 99357944709801073782944611)
          ·
            refine ⟨149036917064701610674416917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99357944709801073782944611 149036917064701610674416917)
            ·
              refine ⟨6986105487407888000363293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149036917064701610674416917 6986105487407888000363293)
              ·
                refine ⟨2619789557777958000136235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6986105487407888000363293 2619789557777958000136235)
                ·
                  refine ⟨3929684336666937000204353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619789557777958000136235 3929684336666937000204353)
                  ·
                    refine ⟨2947263252500202750153265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929684336666937000204353 2947263252500202750153265)
                    ·
                      refine ⟨2210447439375152062614949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947263252500202750153265 2210447439375152062614949)
                      ·
                        rfl

theorem cell23_4304831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_4304831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304831 prefixEnd_4304831 := by exact prefixLift 4304831
  have htrace : WordTrace (prefixWord ++ tailWord_4304831) baseStart_4304831 baseEnd_4304831 := by
    simpa [prefixWord, tailWord_4304831, baseEnd_4304831] using wordTrace_append hprefix tailTrace_4304831
  have hstable : (prefixWord ++ tailWord_4304831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304831).length < 2 ^ (prefixWord ++ tailWord_4304831).sum := by decide
  have hdescent : baseEnd_4304831 < baseStart_4304831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304847 : List Nat := [1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 3]
def baseStart_4304847 : Nat := 118140960795 + 4304847 * 2 ^ 59
def prefixEnd_4304847 : Nat := 4983230072969 + 3 ^ 40 * 4304847 * 2
def baseEnd_4304847 : Nat := 2210455655065624000014875

theorem tailTrace_4304847 : CollatzResearch.WordTrace tailWord_4304847 prefixEnd_4304847 2210455655065624000014875 := by
  unfold tailWord_4304847
  simp only [CollatzResearch.WordTrace]
  refine ⟨157010669035282003179704795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104673779356854668786469863 157010669035282003179704795)
  ·
    refine ⟨235516003552923004769557193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157010669035282003179704795 235516003552923004769557193)
    ·
      refine ⟨176637002664692253577167895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235516003552923004769557193 176637002664692253577167895)
      ·
        refine ⟨264955503997038380365751843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176637002664692253577167895 264955503997038380365751843)
        ·
          refine ⟨397433255995557570548627765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264955503997038380365751843 397433255995557570548627765)
          ·
            refine ⟨37259367749583522238933853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 397433255995557570548627765 37259367749583522238933853)
            ·
              refine ⟨13972262906093820839600195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37259367749583522238933853 13972262906093820839600195)
              ·
                refine ⟨20958394359140731259400293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13972262906093820839600195 20958394359140731259400293)
                ·
                  refine ⟨3929698942338887111137555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20958394359140731259400293 3929698942338887111137555)
                  ·
                    refine ⟨5894548413508330666706333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929698942338887111137555 5894548413508330666706333)
                    ·
                      refine ⟨2210455655065624000014875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894548413508330666706333 2210455655065624000014875)
                      ·
                        rfl

theorem cell23_4304847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 1, 3].length) (baseStart_4304847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304847 prefixEnd_4304847 := by exact prefixLift 4304847
  have htrace : WordTrace (prefixWord ++ tailWord_4304847) baseStart_4304847 baseEnd_4304847 := by
    simpa [prefixWord, tailWord_4304847, baseEnd_4304847] using wordTrace_append hprefix tailTrace_4304847
  have hstable : (prefixWord ++ tailWord_4304847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304847).length < 2 ^ (prefixWord ++ tailWord_4304847).sum := by decide
  have hdescent : baseEnd_4304847 < baseStart_4304847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304861 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_4304861 : Nat := 118140960795 + 4304861 * 2 ^ 59
def prefixEnd_4304861 : Nat := 4983230072969 + 3 ^ 40 * 4304861 * 2
def baseEnd_4304861 : Nat := 2210462843794786945239811

theorem tailTrace_4304861 : CollatzResearch.WordTrace tailWord_4304861 prefixEnd_4304861 2210462843794786945239811 := by
  unfold tailWord_4304861
  simp only [CollatzResearch.WordTrace]
  refine ⟨157011179657231283570714437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104674119771487522380476291 157011179657231283570714437)
  ·
    refine ⟨29439596185730865669508957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157011179657231283570714437 29439596185730865669508957)
    ·
      refine ⟨11039848569649074626065859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29439596185730865669508957 11039848569649074626065859)
      ·
        refine ⟨16559772854473611939098789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11039848569649074626065859 16559772854473611939098789)
        ·
          refine ⟨3104957410213802238581023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16559772854473611939098789 3104957410213802238581023)
          ·
            refine ⟨4657436115320703357871535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3104957410213802238581023 4657436115320703357871535)
            ·
              refine ⟨6986154172981055036807303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657436115320703357871535 6986154172981055036807303)
              ·
                refine ⟨10479231259471582555210955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6986154172981055036807303 10479231259471582555210955)
                ·
                  refine ⟨15718846889207373832816433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10479231259471582555210955 15718846889207373832816433)
                  ·
                    refine ⟨11789135166905530374612325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15718846889207373832816433 11789135166905530374612325)
                    ·
                      refine ⟨2210462843794786945239811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11789135166905530374612325 2210462843794786945239811)
                      ·
                        rfl

theorem cell23_4304861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_4304861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304861 prefixEnd_4304861 := by exact prefixLift 4304861
  have htrace : WordTrace (prefixWord ++ tailWord_4304861) baseStart_4304861 baseEnd_4304861 := by
    simpa [prefixWord, tailWord_4304861, baseEnd_4304861] using wordTrace_append hprefix tailTrace_4304861
  have hstable : (prefixWord ++ tailWord_4304861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304861).length < 2 ^ (prefixWord ++ tailWord_4304861).sum := by decide
  have hdescent : baseEnd_4304861 < baseStart_4304861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304890 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3]
def baseStart_4304890 : Nat := 118140960795 + 4304890 * 2 ^ 59
def prefixEnd_4304890 : Nat := 4983230072969 + 3 ^ 40 * 4304890 * 2
def baseEnd_4304890 : Nat := 2210477734733767331777177

theorem tailTrace_4304890 : CollatzResearch.WordTrace tailWord_4304890 prefixEnd_4304890 2210477734733767331777177 := by
  unfold tailWord_4304890
  simp only [CollatzResearch.WordTrace]
  refine ⟨39253059343531555380880031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104674824916084147682346749 39253059343531555380880031)
  ·
    refine ⟨58879589015297333071320047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39253059343531555380880031 58879589015297333071320047)
    ·
      refine ⟨88319383522945999606980071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58879589015297333071320047 88319383522945999606980071)
      ·
        refine ⟨132479075284418999410470107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88319383522945999606980071 132479075284418999410470107)
        ·
          refine ⟨198718612926628499115705161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132479075284418999410470107 198718612926628499115705161)
          ·
            refine ⟨149038959694971374336778871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198718612926628499115705161 149038959694971374336778871)
            ·
              refine ⟨223558439542457061505168307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149038959694971374336778871 223558439542457061505168307)
              ·
                refine ⟨335337659313685592257752461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223558439542457061505168307 335337659313685592257752461)
                ·
                  refine ⟨125751622242632097096657173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 335337659313685592257752461 125751622242632097096657173)
                  ·
                    refine ⟨5894607292623379551405805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125751622242632097096657173 5894607292623379551405805)
                    ·
                      refine ⟨2210477734733767331777177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894607292623379551405805 2210477734733767331777177)
                      ·
                        rfl

theorem cell23_4304890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_4304890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304890 prefixEnd_4304890 := by exact prefixLift 4304890
  have htrace : WordTrace (prefixWord ++ tailWord_4304890) baseStart_4304890 baseEnd_4304890 := by
    simpa [prefixWord, tailWord_4304890, baseEnd_4304890] using wordTrace_append hprefix tailTrace_4304890
  have hstable : (prefixWord ++ tailWord_4304890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304890).length < 2 ^ (prefixWord ++ tailWord_4304890).sum := by decide
  have hdescent : baseEnd_4304890 < baseStart_4304890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304904 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_4304904 : Nat := 118140960795 + 4304904 * 2 ^ 59
def prefixEnd_4304904 : Nat := 4983230072969 + 3 ^ 40 * 4304904 * 2
def baseEnd_4304904 : Nat := 2210484923462930277002113

theorem tailTrace_4304904 : CollatzResearch.WordTrace tailWord_4304904 prefixEnd_4304904 2210484923462930277002113 := by
  unfold tailWord_4304904
  simp only [CollatzResearch.WordTrace]
  refine ⟨78506373998037750957264883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104675165330717001276353177 78506373998037750957264883)
  ·
    refine ⟨117759560997056626435897325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78506373998037750957264883 117759560997056626435897325)
    ·
      refine ⟨44159835373896234913461497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117759560997056626435897325 44159835373896234913461497)
      ·
        refine ⟨33119876530422176185096123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44159835373896234913461497 33119876530422176185096123)
        ·
          refine ⟨49679814795633264277644185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33119876530422176185096123 49679814795633264277644185)
          ·
            refine ⟨37259861096724948208233139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49679814795633264277644185 37259861096724948208233139)
            ·
              refine ⟨55889791645087422312349709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37259861096724948208233139 55889791645087422312349709)
              ·
                refine ⟨20958671866907783367131141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55889791645087422312349709 20958671866907783367131141)
                ·
                  refine ⟨3929750975045209381337089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20958671866907783367131141 3929750975045209381337089)
                  ·
                    refine ⟨2947313231283907036002817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929750975045209381337089 2947313231283907036002817)
                    ·
                      refine ⟨2210484923462930277002113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947313231283907036002817 2210484923462930277002113)
                      ·
                        rfl

theorem cell23_4304904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_4304904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304904 prefixEnd_4304904 := by exact prefixLift 4304904
  have htrace : WordTrace (prefixWord ++ tailWord_4304904) baseStart_4304904 baseEnd_4304904 := by
    simpa [prefixWord, tailWord_4304904, baseEnd_4304904] using wordTrace_append hprefix tailTrace_4304904
  have hstable : (prefixWord ++ tailWord_4304904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304904).length < 2 ^ (prefixWord ++ tailWord_4304904).sum := by decide
  have hdescent : baseEnd_4304904 < baseStart_4304904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304957 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_4304957 : Nat := 118140960795 + 4304957 * 2 ^ 59
def prefixEnd_4304957 : Nat := 4983230072969 + 3 ^ 40 * 4304957 * 2
def baseEnd_4304957 : Nat := 736837379312539523213123

theorem tailTrace_4304957 : CollatzResearch.WordTrace tailWord_4304957 prefixEnd_4304957 736837379312539523213123 := by
  unfold tailWord_4304957
  simp only [CollatzResearch.WordTrace]
  refine ⟨157014681064883491966209125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104676454043255661310806083 157014681064883491966209125)
  ·
    refine ⟨29440252699665654743664211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157014681064883491966209125 29440252699665654743664211)
    ·
      refine ⟨44160379049498482115496317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29440252699665654743664211 44160379049498482115496317)
      ·
        refine ⟨16560142143561930793311119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44160379049498482115496317 16560142143561930793311119)
        ·
          refine ⟨24840213215342896189966679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16560142143561930793311119 24840213215342896189966679)
          ·
            refine ⟨37260319823014344284950019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24840213215342896189966679 37260319823014344284950019)
            ·
              refine ⟨55890479734521516427425029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37260319823014344284950019 55890479734521516427425029)
              ·
                refine ⟨10479464950222784330142193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55890479734521516427425029 10479464950222784330142193)
                ·
                  refine ⟨7859598712667088247606645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10479464950222784330142193 7859598712667088247606645)
                  ·
                    refine ⟨736837379312539523213123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7859598712667088247606645 736837379312539523213123)
                    ·
                      rfl

theorem cell23_4304957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_4304957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304957 prefixEnd_4304957 := by exact prefixLift 4304957
  have htrace : WordTrace (prefixWord ++ tailWord_4304957) baseStart_4304957 baseEnd_4304957 := by
    simpa [prefixWord, tailWord_4304957, baseEnd_4304957] using wordTrace_append hprefix tailTrace_4304957
  have hstable : (prefixWord ++ tailWord_4304957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304957).length < 2 ^ (prefixWord ++ tailWord_4304957).sum := by decide
  have hdescent : baseEnd_4304957 < baseStart_4304957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304961 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 5]
def baseStart_4304961 : Nat := 118140960795 + 4304961 * 2 ^ 59
def prefixEnd_4304961 : Nat := 4983230072969 + 3 ^ 40 * 4304961 * 2
def baseEnd_4304961 : Nat := 245612687984470728221039

theorem tailTrace_4304961 : CollatzResearch.WordTrace tailWord_4304961 prefixEnd_4304961 245612687984470728221039 := by
  unfold tailWord_4304961
  simp only [CollatzResearch.WordTrace]
  refine ⟨157014826956869000649354737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104676551304579333766236491 157014826956869000649354737)
  ·
    refine ⟨117761120217651750487016053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157014826956869000649354737 117761120217651750487016053)
    ·
      refine ⟨11040105020404851608157755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117761120217651750487016053 11040105020404851608157755)
      ·
        refine ⟨16560157530607277412236633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11040105020404851608157755 16560157530607277412236633)
        ·
          refine ⟨12420118147955458059177475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16560157530607277412236633 12420118147955458059177475)
          ·
            refine ⟨18630177221933187088766213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12420118147955458059177475 18630177221933187088766213)
            ·
              refine ⟨3493158229112472579143665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18630177221933187088766213 3493158229112472579143665)
              ·
                refine ⟨2619868671834354434357749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493158229112472579143665 2619868671834354434357749)
                ·
                  refine ⟨245612687984470728221039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2619868671834354434357749 245612687984470728221039)
                  ·
                    rfl

theorem cell23_4304961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 5].length) (baseStart_4304961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304961 prefixEnd_4304961 := by exact prefixLift 4304961
  have htrace : WordTrace (prefixWord ++ tailWord_4304961) baseStart_4304961 baseEnd_4304961 := by
    simpa [prefixWord, tailWord_4304961, baseEnd_4304961] using wordTrace_append hprefix tailTrace_4304961
  have hstable : (prefixWord ++ tailWord_4304961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304961).length < 2 ^ (prefixWord ++ tailWord_4304961).sum := by decide
  have hdescent : baseEnd_4304961 < baseStart_4304961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4304970 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_4304970 : Nat := 118140960795 + 4304970 * 2 ^ 59
def prefixEnd_4304970 : Nat := 4983230072969 + 3 ^ 40 * 4304970 * 2
def baseEnd_4304970 : Nat := 736839604395375672925603

theorem tailTrace_4304970 : CollatzResearch.WordTrace tailWord_4304970 prefixEnd_4304970 736839604395375672925603 := by
  unfold tailWord_4304970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39253788803459098796608091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104676770142557596790954909 39253788803459098796608091)
  ·
    refine ⟨58880683205188648194912137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39253788803459098796608091 58880683205188648194912137)
    ·
      refine ⟨44160512403891486146184103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58880683205188648194912137 44160512403891486146184103)
      ·
        refine ⟨66240768605837229219276155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44160512403891486146184103 66240768605837229219276155)
        ·
          refine ⟨99361152908755843828914233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66240768605837229219276155 99361152908755843828914233)
          ·
            refine ⟨74520864681566882871685675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99361152908755843828914233 74520864681566882871685675)
            ·
              refine ⟨111781297022350324307528513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74520864681566882871685675 111781297022350324307528513)
              ·
                refine ⟨83835972766762743230646385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111781297022350324307528513 83835972766762743230646385)
                ·
                  refine ⟨62876979575072057422984789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83835972766762743230646385 62876979575072057422984789)
                  ·
                    refine ⟨736839604395375672925603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62876979575072057422984789 736839604395375672925603)
                    ·
                      rfl

theorem cell23_4304970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_4304970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4304970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4304970 prefixEnd_4304970 := by exact prefixLift 4304970
  have htrace : WordTrace (prefixWord ++ tailWord_4304970) baseStart_4304970 baseEnd_4304970 := by
    simpa [prefixWord, tailWord_4304970, baseEnd_4304970] using wordTrace_append hprefix tailTrace_4304970
  have hstable : (prefixWord ++ tailWord_4304970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4304970).length < 2 ^ (prefixWord ++ tailWord_4304970).sum := by decide
  have hdescent : baseEnd_4304970 < baseStart_4304970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4304970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305017 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 8]
def baseStart_4305017 : Nat := 118140960795 + 4305017 * 2 ^ 59
def prefixEnd_4305017 : Nat := 4983230072969 + 3 ^ 40 * 4305017 * 2
def baseEnd_4305017 : Nat := 245615882975209814987677

theorem tailTrace_4305017 : CollatzResearch.WordTrace tailWord_4305017 prefixEnd_4305017 245615882975209814987677 := by
  unfold tailWord_4305017
  simp only [CollatzResearch.WordTrace]
  refine ⟨157016869444666122213393305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104677912963110748142262203 157016869444666122213393305)
  ·
    refine ⟨117762652083499591660044979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157016869444666122213393305 117762652083499591660044979)
    ·
      refine ⟨176643978125249387490067469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117762652083499591660044979 176643978125249387490067469)
      ·
        refine ⟨66241491796968520308775301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176643978125249387490067469 66241491796968520308775301)
        ·
          refine ⟨12420279711931597557895369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66241491796968520308775301 12420279711931597557895369)
          ·
            refine ⟨9315209783948698168421527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12420279711931597557895369 9315209783948698168421527)
            ·
              refine ⟨13972814675923047252632291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9315209783948698168421527 13972814675923047252632291)
              ·
                refine ⟨20959222013884570878948437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13972814675923047252632291 20959222013884570878948437)
                ·
                  refine ⟨245615882975209814987677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20959222013884570878948437 245615882975209814987677)
                  ·
                    rfl

theorem cell23_4305017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_4305017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305017 prefixEnd_4305017 := by exact prefixLift 4305017
  have htrace : WordTrace (prefixWord ++ tailWord_4305017) baseStart_4305017 baseEnd_4305017 := by
    simpa [prefixWord, tailWord_4305017, baseEnd_4305017] using wordTrace_append hprefix tailTrace_4305017
  have hstable : (prefixWord ++ tailWord_4305017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305017).length < 2 ^ (prefixWord ++ tailWord_4305017).sum := by decide
  have hdescent : baseEnd_4305017 < baseStart_4305017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305021 : List Nat := [1, 4, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_4305021 : Nat := 118140960795 + 4305021 * 2 ^ 59
def prefixEnd_4305021 : Nat := 4983230072969 + 3 ^ 40 * 4305021 * 2
def baseEnd_4305021 : Nat := 736848333566502106413025

theorem tailTrace_4305021 : CollatzResearch.WordTrace tailWord_4305021 prefixEnd_4305021 736848333566502106413025 := by
  unfold tailWord_4305021
  simp only [CollatzResearch.WordTrace]
  refine ⟨157017015336651630896538917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104678010224434420597692611 157017015336651630896538917)
  ·
    refine ⟨29440690375622180793101047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157017015336651630896538917 29440690375622180793101047)
    ·
      refine ⟨44161035563433271189651571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29440690375622180793101047 44161035563433271189651571)
      ·
        refine ⟨66241553345149906784477357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44161035563433271189651571 66241553345149906784477357)
        ·
          refine ⟨24840582504431215044179009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66241553345149906784477357 24840582504431215044179009)
          ·
            refine ⟨18630436878323411283134257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24840582504431215044179009 18630436878323411283134257)
            ·
              refine ⟨13972827658742558462350693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18630436878323411283134257 13972827658742558462350693)
              ·
                refine ⟨2619905186014229711690755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13972827658742558462350693 2619905186014229711690755)
                ·
                  refine ⟨3929857779021344567536133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619905186014229711690755 3929857779021344567536133)
                  ·
                    refine ⟨736848333566502106413025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3929857779021344567536133 736848333566502106413025)
                    ·
                      rfl

theorem cell23_4305021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_4305021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305021 prefixEnd_4305021 := by exact prefixLift 4305021
  have htrace : WordTrace (prefixWord ++ tailWord_4305021) baseStart_4305021 baseEnd_4305021 := by
    simpa [prefixWord, tailWord_4305021, baseEnd_4305021] using wordTrace_append hprefix tailTrace_4305021
  have hstable : (prefixWord ++ tailWord_4305021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305021).length < 2 ^ (prefixWord ++ tailWord_4305021).sum := by decide
  have hdescent : baseEnd_4305021 < baseStart_4305021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305087 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_4305087 : Nat := 118140960795 + 4305087 * 2 ^ 59
def prefixEnd_4305087 : Nat := 4983230072969 + 3 ^ 40 * 4305087 * 2
def baseEnd_4305087 : Nat := 2210578890422703061013771

theorem tailTrace_4305087 : CollatzResearch.WordTrace tailWord_4305087 prefixEnd_4305087 2210578890422703061013771 := by
  unfold tailWord_4305087
  simp only [CollatzResearch.WordTrace]
  refine ⟨157019422554412524168441515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104679615036275016112294343 157019422554412524168441515)
  ·
    refine ⟨235529133831618786252662273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157019422554412524168441515 235529133831618786252662273)
    ·
      refine ⟨176646850373714089689496705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235529133831618786252662273 176646850373714089689496705)
      ·
        refine ⟨132485137780285567267122529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176646850373714089689496705 132485137780285567267122529)
        ·
          refine ⟨99363853335214175450341897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132485137780285567267122529 99363853335214175450341897)
          ·
            refine ⟨74522890001410631587756423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99363853335214175450341897 74522890001410631587756423)
            ·
              refine ⟨111784335002115947381634635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74522890001410631587756423 111784335002115947381634635)
              ·
                refine ⟨167676502503173921072451953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111784335002115947381634635 167676502503173921072451953)
                ·
                  refine ⟨125757376877380440804338965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167676502503173921072451953 125757376877380440804338965)
                  ·
                    refine ⟨5894877041127208162703389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 125757376877380440804338965 5894877041127208162703389)
                    ·
                      refine ⟨2210578890422703061013771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894877041127208162703389 2210578890422703061013771)
                      ·
                        rfl

theorem cell23_4305087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_4305087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305087 prefixEnd_4305087 := by exact prefixLift 4305087
  have htrace : WordTrace (prefixWord ++ tailWord_4305087) baseStart_4305087 baseEnd_4305087 := by
    simpa [prefixWord, tailWord_4305087, baseEnd_4305087] using wordTrace_append hprefix tailTrace_4305087
  have hstable : (prefixWord ++ tailWord_4305087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305087).length < 2 ^ (prefixWord ++ tailWord_4305087).sum := by decide
  have hdescent : baseEnd_4305087 < baseStart_4305087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305134 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_4305134 : Nat := 118140960795 + 4305134 * 2 ^ 59
def prefixEnd_4305134 : Nat := 4983230072969 + 3 ^ 40 * 4305134 * 2
def baseEnd_4305134 : Nat := 2210603024013464377126055

theorem tailTrace_4305134 : CollatzResearch.WordTrace tailWord_4305134 prefixEnd_4305134 2210603024013464377126055 := by
  unfold tailWord_4305134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19627642098155281399425307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104680757856828167463601637 19627642098155281399425307)
  ·
    refine ⟨29441463147232922099137961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19627642098155281399425307 29441463147232922099137961)
    ·
      refine ⟨22081097360424691574353471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29441463147232922099137961 22081097360424691574353471)
      ·
        refine ⟨33121646040637037361530207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22081097360424691574353471 33121646040637037361530207)
        ·
          refine ⟨49682469060955556042295311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33121646040637037361530207 49682469060955556042295311)
          ·
            refine ⟨74523703591433334063442967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49682469060955556042295311 74523703591433334063442967)
            ·
              refine ⟨111785555387150001095164451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74523703591433334063442967 111785555387150001095164451)
              ·
                refine ⟨167678333080725001642746677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111785555387150001095164451 167678333080725001642746677)
                ·
                  refine ⟨15719843726317968904007501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167678333080725001642746677 15719843726317968904007501)
                  ·
                    refine ⟨5894941397369238339002813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15719843726317968904007501 5894941397369238339002813)
                    ·
                      refine ⟨2210603024013464377126055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894941397369238339002813 2210603024013464377126055)
                      ·
                        rfl

theorem cell23_4305134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_4305134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305134 prefixEnd_4305134 := by exact prefixLift 4305134
  have htrace : WordTrace (prefixWord ++ tailWord_4305134) baseStart_4305134 baseEnd_4305134 := by
    simpa [prefixWord, tailWord_4305134, baseEnd_4305134] using wordTrace_append hprefix tailTrace_4305134
  have hstable : (prefixWord ++ tailWord_4305134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305134).length < 2 ^ (prefixWord ++ tailWord_4305134).sum := by decide
  have hdescent : baseEnd_4305134 < baseStart_4305134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305135 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 1, 2, 2]
def baseStart_4305135 : Nat := 118140960795 + 4305135 * 2 ^ 59
def prefixEnd_4305135 : Nat := 4983230072969 + 3 ^ 40 * 4305135 * 2
def baseEnd_4305135 : Nat := 2210603537494118873213551

theorem tailTrace_4305135 : CollatzResearch.WordTrace tailWord_4305135 prefixEnd_4305135 2210603537494118873213551 := by
  unfold tailWord_4305135
  simp only [CollatzResearch.WordTrace]
  refine ⟨157021173258238628366188859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104680782172159085577459239 157021173258238628366188859)
  ·
    refine ⟨235531759887357942549283289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157021173258238628366188859 235531759887357942549283289)
    ·
      refine ⟨176648819915518456911962467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235531759887357942549283289 176648819915518456911962467)
      ·
        refine ⟨264973229873277685367943701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176648819915518456911962467 264973229873277685367943701)
        ·
          refine ⟨12420620150309891501622361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 264973229873277685367943701 12420620150309891501622361)
          ·
            refine ⟨9315465112732418626216771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12420620150309891501622361 9315465112732418626216771)
            ·
              refine ⟨13973197669098627939325157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9315465112732418626216771 13973197669098627939325157)
              ·
                refine ⟨2619974562955992738623467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13973197669098627939325157 2619974562955992738623467)
                ·
                  refine ⟨3929961844433989107935201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2619974562955992738623467 3929961844433989107935201)
                  ·
                    refine ⟨2947471383325491830951401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3929961844433989107935201 2947471383325491830951401)
                    ·
                      refine ⟨2210603537494118873213551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947471383325491830951401 2210603537494118873213551)
                      ·
                        rfl

theorem cell23_4305135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 1, 2, 2].length) (baseStart_4305135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305135 prefixEnd_4305135 := by exact prefixLift 4305135
  have htrace : WordTrace (prefixWord ++ tailWord_4305135) baseStart_4305135 baseEnd_4305135 := by
    simpa [prefixWord, tailWord_4305135, baseEnd_4305135] using wordTrace_append hprefix tailTrace_4305135
  have hstable : (prefixWord ++ tailWord_4305135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305135).length < 2 ^ (prefixWord ++ tailWord_4305135).sum := by decide
  have hdescent : baseEnd_4305135 < baseStart_4305135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305137 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_4305137 : Nat := 118140960795 + 4305137 * 2 ^ 59
def prefixEnd_4305137 : Nat := 4983230072969 + 3 ^ 40 * 4305137 * 2
def baseEnd_4305137 : Nat := 736868188151809288462847

theorem tailTrace_4305137 : CollatzResearch.WordTrace tailWord_4305137 prefixEnd_4305137 736868188151809288462847 := by
  unfold tailWord_4305137
  simp only [CollatzResearch.WordTrace]
  refine ⟨157021246204231382707761665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104680830802820921805174443 157021246204231382707761665)
  ·
    refine ⟨117765934653173537030821249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157021246204231382707761665 117765934653173537030821249)
    ·
      refine ⟨88324450989880152773115937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117765934653173537030821249 88324450989880152773115937)
      ·
        refine ⟨66243338242410114579836953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88324450989880152773115937 66243338242410114579836953)
        ·
          refine ⟨49682503681807585934877715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66243338242410114579836953 49682503681807585934877715)
          ·
            refine ⟨74523755522711378902316573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49682503681807585934877715 74523755522711378902316573)
            ·
              refine ⟨27946408321016767088368715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74523755522711378902316573 27946408321016767088368715)
              ·
                refine ⟨41919612481525150632553073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27946408321016767088368715 41919612481525150632553073)
                ·
                  refine ⟨31439709361143862974414805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41919612481525150632553073 31439709361143862974414805)
                  ·
                    refine ⟨736868188151809288462847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31439709361143862974414805 736868188151809288462847)
                    ·
                      rfl

theorem cell23_4305137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_4305137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305137 prefixEnd_4305137 := by exact prefixLift 4305137
  have htrace : WordTrace (prefixWord ++ tailWord_4305137) baseStart_4305137 baseEnd_4305137 := by
    simpa [prefixWord, tailWord_4305137, baseEnd_4305137] using wordTrace_append hprefix tailTrace_4305137
  have hstable : (prefixWord ++ tailWord_4305137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305137).length < 2 ^ (prefixWord ++ tailWord_4305137).sum := by decide
  have hdescent : baseEnd_4305137 < baseStart_4305137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305151 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 3]
def baseStart_4305151 : Nat := 118140960795 + 4305151 * 2 ^ 59
def prefixEnd_4305151 : Nat := 4983230072969 + 3 ^ 40 * 4305151 * 2
def baseEnd_4305151 : Nat := 2210611753184590810613477

theorem tailTrace_4305151 : CollatzResearch.WordTrace tailWord_4305151 prefixEnd_4305151 2210611753184590810613477 := by
  unfold tailWord_4305151
  simp only [CollatzResearch.WordTrace]
  refine ⟨157021756826180663098771307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104681171217453775399180871 157021756826180663098771307)
  ·
    refine ⟨235532635239270994648156961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157021756826180663098771307 235532635239270994648156961)
    ·
      refine ⟨176649476429453245986117721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235532635239270994648156961 176649476429453245986117721)
      ·
        refine ⟨132487107322089934489588291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176649476429453245986117721 132487107322089934489588291)
        ·
          refine ⟨198730660983134901734382437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132487107322089934489588291 198730660983134901734382437)
          ·
            refine ⟨37261998934337794075196707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 198730660983134901734382437 37261998934337794075196707)
            ·
              refine ⟨55892998401506691112795061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37261998934337794075196707 55892998401506691112795061)
              ·
                refine ⟨5239968600141252291824537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55892998401506691112795061 5239968600141252291824537)
                ·
                  refine ⟨3929976450105939218868403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5239968600141252291824537 3929976450105939218868403)
                  ·
                    refine ⟨5894964675158908828302605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3929976450105939218868403 5894964675158908828302605)
                    ·
                      refine ⟨2210611753184590810613477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5894964675158908828302605 2210611753184590810613477)
                      ·
                        rfl

theorem cell23_4305151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_4305151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305151 prefixEnd_4305151 := by exact prefixLift 4305151
  have htrace : WordTrace (prefixWord ++ tailWord_4305151) baseStart_4305151 baseEnd_4305151 := by
    simpa [prefixWord, tailWord_4305151, baseEnd_4305151] using wordTrace_append hprefix tailTrace_4305151
  have hstable : (prefixWord ++ tailWord_4305151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305151).length < 2 ^ (prefixWord ++ tailWord_4305151).sum := by decide
  have hdescent : baseEnd_4305151 < baseStart_4305151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305161 : List Nat := [1, 2, 1, 1, 3, 4, 2, 1, 3, 3, 2]
def baseStart_4305161 : Nat := 118140960795 + 4305161 * 2 ^ 59
def prefixEnd_4305161 : Nat := 4983230072969 + 3 ^ 40 * 4305161 * 2
def baseEnd_4305161 : Nat := 2210616887991135771488431

theorem tailTrace_4305161 : CollatzResearch.WordTrace tailWord_4305161 prefixEnd_4305161 2210616887991135771488431 := by
  unfold tailWord_4305161
  simp only [CollatzResearch.WordTrace]
  refine ⟨157022121556144434806635337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104681414370762956537756891 157022121556144434806635337)
  ·
    refine ⟨117766591167108326104976503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157022121556144434806635337 117766591167108326104976503)
    ·
      refine ⟨176649886750662489157464755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117766591167108326104976503 176649886750662489157464755)
      ·
        refine ⟨264974830125993733736197133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176649886750662489157464755 264974830125993733736197133)
        ·
          refine ⟨99365561297247650151073925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 264974830125993733736197133 99365561297247650151073925)
          ·
            refine ⟨18631042743233934403326361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99365561297247650151073925 18631042743233934403326361)
            ·
              refine ⟨13973282057425450802494771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18631042743233934403326361 13973282057425450802494771)
              ·
                refine ⟨20959923086138176203742157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13973282057425450802494771 20959923086138176203742157)
                ·
                  refine ⟨7859971157301816076403309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20959923086138176203742157 7859971157301816076403309)
                  ·
                    refine ⟨2947489183988181028651241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7859971157301816076403309 2947489183988181028651241)
                    ·
                      refine ⟨2210616887991135771488431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947489183988181028651241 2210616887991135771488431)
                      ·
                        rfl

theorem cell23_4305161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 3, 2].length) (baseStart_4305161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305161 prefixEnd_4305161 := by exact prefixLift 4305161
  have htrace : WordTrace (prefixWord ++ tailWord_4305161) baseStart_4305161 baseEnd_4305161 := by
    simpa [prefixWord, tailWord_4305161, baseEnd_4305161] using wordTrace_append hprefix tailTrace_4305161
  have hstable : (prefixWord ++ tailWord_4305161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305161).length < 2 ^ (prefixWord ++ tailWord_4305161).sum := by decide
  have hdescent : baseEnd_4305161 < baseStart_4305161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305184 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 2, 6]
def baseStart_4305184 : Nat := 118140960795 + 4305184 * 2 ^ 59
def prefixEnd_4305184 : Nat := 4983230072969 + 3 ^ 40 * 4305184 * 2
def baseEnd_4305184 : Nat := 736876232682063060500275

theorem tailTrace_4305184 : CollatzResearch.WordTrace tailWord_4305184 prefixEnd_4305184 736876232682063060500275 := by
  unfold tailWord_4305184
  simp only [CollatzResearch.WordTrace]
  refine ⟨78511480217530554867361303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104681973623374073156481737 78511480217530554867361303)
  ·
    refine ⟨117767220326295832301041955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78511480217530554867361303 117767220326295832301041955)
    ·
      refine ⟨176650830489443748451562933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117767220326295832301041955 176650830489443748451562933)
      ·
        refine ⟨16561015358385351417334025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 176650830489443748451562933 16561015358385351417334025)
        ·
          refine ⟨12420761518789013563000519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16561015358385351417334025 12420761518789013563000519)
          ·
            refine ⟨18631142278183520344500779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12420761518789013563000519 18631142278183520344500779)
            ·
              refine ⟨27946713417275280516751169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18631142278183520344500779 27946713417275280516751169)
              ·
                refine ⟨20960035062956460387563377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27946713417275280516751169 20960035062956460387563377)
                ·
                  refine ⟨15720026297217345290672533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20960035062956460387563377 15720026297217345290672533)
                  ·
                    refine ⟨736876232682063060500275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15720026297217345290672533 736876232682063060500275)
                    ·
                      rfl

theorem cell23_4305184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 2, 6].length) (baseStart_4305184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305184 prefixEnd_4305184 := by exact prefixLift 4305184
  have htrace : WordTrace (prefixWord ++ tailWord_4305184) baseStart_4305184 baseEnd_4305184 := by
    simpa [prefixWord, tailWord_4305184, baseEnd_4305184] using wordTrace_append hprefix tailTrace_4305184
  have hstable : (prefixWord ++ tailWord_4305184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305184).length < 2 ^ (prefixWord ++ tailWord_4305184).sum := by decide
  have hdescent : baseEnd_4305184 < baseStart_4305184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305207 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9]
def baseStart_4305207 : Nat := 118140960795 + 4305207 * 2 ^ 59
def prefixEnd_4305207 : Nat := 4983230072969 + 3 ^ 40 * 4305207 * 2
def baseEnd_4305207 : Nat := 2210640508101242591513219

theorem tailTrace_4305207 : CollatzResearch.WordTrace tailWord_4305207 prefixEnd_4305207 2210640508101242591513219 := by
  unfold tailWord_4305207
  simp only [CollatzResearch.WordTrace]
  refine ⟨157023799313977784662809875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104682532875985189775206583 157023799313977784662809875)
  ·
    refine ⟨235535698970966676994214813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157023799313977784662809875 235535698970966676994214813)
    ·
      refine ⟨88325887114112503872830555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235535698970966676994214813 88325887114112503872830555)
      ·
        refine ⟨132488830671168755809245833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88325887114112503872830555 132488830671168755809245833)
        ·
          refine ⟨99366623003376566856934375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132488830671168755809245833 99366623003376566856934375)
          ·
            refine ⟨149049934505064850285401563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99366623003376566856934375 149049934505064850285401563)
            ·
              refine ⟨223574901757597275428102345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149049934505064850285401563 223574901757597275428102345)
              ·
                refine ⟨167681176318197956571076759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223574901757597275428102345 167681176318197956571076759)
                ·
                  refine ⟨251521764477296934856615139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167681176318197956571076759 251521764477296934856615139)
                  ·
                    refine ⟨377282646715945402284922709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251521764477296934856615139 377282646715945402284922709)
                    ·
                      refine ⟨2210640508101242591513219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 377282646715945402284922709 2210640508101242591513219)
                      ·
                        rfl

theorem cell23_4305207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_4305207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305207 prefixEnd_4305207 := by exact prefixLift 4305207
  have htrace : WordTrace (prefixWord ++ tailWord_4305207) baseStart_4305207 baseEnd_4305207 := by
    simpa [prefixWord, tailWord_4305207, baseEnd_4305207] using wordTrace_append hprefix tailTrace_4305207
  have hstable : (prefixWord ++ tailWord_4305207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305207).length < 2 ^ (prefixWord ++ tailWord_4305207).sum := by decide
  have hdescent : baseEnd_4305207 < baseStart_4305207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305208 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2]
def baseStart_4305208 : Nat := 118140960795 + 4305208 * 2 ^ 59
def prefixEnd_4305208 : Nat := 4983230072969 + 3 ^ 40 * 4305208 * 2
def baseEnd_4305208 : Nat := 2210641021581897087600715

theorem tailTrace_4305208 : CollatzResearch.WordTrace tailWord_4305208 prefixEnd_4305208 2210641021581897087600715 := by
  unfold tailWord_4305208
  simp only [CollatzResearch.WordTrace]
  refine ⟨78511917893487080916798139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104682557191316107889064185 78511917893487080916798139)
  ·
    refine ⟨117767876840230621375197209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78511917893487080916798139 117767876840230621375197209)
    ·
      refine ⟨88325907630172966031397907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117767876840230621375197209 88325907630172966031397907)
      ·
        refine ⟨132488861445259449047096861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88325907630172966031397907 132488861445259449047096861)
        ·
          refine ⟨49683323041972293392661323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132488861445259449047096861 49683323041972293392661323)
          ·
            refine ⟨74524984562958440088991985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49683323041972293392661323 74524984562958440088991985)
            ·
              refine ⟨55893738422218830066743989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74524984562958440088991985 55893738422218830066743989)
              ·
                refine ⟨5240037977083015318757249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55893738422218830066743989 5240037977083015318757249)
                ·
                  refine ⟨3930028482812261489067937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240037977083015318757249 3930028482812261489067937)
                  ·
                    refine ⟨2947521362109196116800953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930028482812261489067937 2947521362109196116800953)
                    ·
                      refine ⟨2210641021581897087600715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947521362109196116800953 2210641021581897087600715)
                      ·
                        rfl

theorem cell23_4305208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_4305208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305208 prefixEnd_4305208 := by exact prefixLift 4305208
  have htrace : WordTrace (prefixWord ++ tailWord_4305208) baseStart_4305208 baseEnd_4305208 := by
    simpa [prefixWord, tailWord_4305208, baseEnd_4305208] using wordTrace_append hprefix tailTrace_4305208
  have hstable : (prefixWord ++ tailWord_4305208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305208).length < 2 ^ (prefixWord ++ tailWord_4305208).sum := by decide
  have hdescent : baseEnd_4305208 < baseStart_4305208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305224 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_4305224 : Nat := 118140960795 + 4305224 * 2 ^ 59
def prefixEnd_4305224 : Nat := 4983230072969 + 3 ^ 40 * 4305224 * 2
def baseEnd_4305224 : Nat := 2210649237272369025000641

theorem tailTrace_4305224 : CollatzResearch.WordTrace tailWord_4305224 prefixEnd_4305224 2210649237272369025000641 := by
  unfold tailWord_4305224
  simp only [CollatzResearch.WordTrace]
  refine ⟨78512209677458098283089363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104682946236610797710785817 78512209677458098283089363)
  ·
    refine ⟨117768314516187147424634045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78512209677458098283089363 117768314516187147424634045)
    ·
      refine ⟨44163117943570180284237767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117768314516187147424634045 44163117943570180284237767)
      ·
        refine ⟨66244676915355270426356651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44163117943570180284237767 66244676915355270426356651)
        ·
          refine ⟨99367015373032905639534977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66244676915355270426356651 99367015373032905639534977)
          ·
            refine ⟨74525261529774679229651233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99367015373032905639534977 74525261529774679229651233)
            ·
              refine ⟨55893946147331009422238425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74525261529774679229651233 55893946147331009422238425)
              ·
                refine ⟨41920459610498257066678819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55893946147331009422238425 41920459610498257066678819)
                ·
                  refine ⟨62880689415747385600018229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41920459610498257066678819 62880689415747385600018229)
                  ·
                    refine ⟨5895064632726317400001709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 62880689415747385600018229 5895064632726317400001709)
                    ·
                      refine ⟨2210649237272369025000641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5895064632726317400001709 2210649237272369025000641)
                      ·
                        rfl

theorem cell23_4305224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_4305224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305224 prefixEnd_4305224 := by exact prefixLift 4305224
  have htrace : WordTrace (prefixWord ++ tailWord_4305224) baseStart_4305224 baseEnd_4305224 := by
    simpa [prefixWord, tailWord_4305224, baseEnd_4305224] using wordTrace_append hprefix tailTrace_4305224
  have hstable : (prefixWord ++ tailWord_4305224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305224).length < 2 ^ (prefixWord ++ tailWord_4305224).sum := by decide
  have hdescent : baseEnd_4305224 < baseStart_4305224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305248 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 7]
def baseStart_4305248 : Nat := 118140960795 + 4305248 * 2 ^ 59
def prefixEnd_4305248 : Nat := 4983230072969 + 3 ^ 40 * 4305248 * 2
def baseEnd_4305248 : Nat := 245629062312008547900059

theorem tailTrace_4305248 : CollatzResearch.WordTrace tailWord_4305248 prefixEnd_4305248 245629062312008547900059 := by
  unfold tailWord_4305248
  simp only [CollatzResearch.WordTrace]
  refine ⟨78512647353414624332526199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104683529804552832443368265 78512647353414624332526199)
  ·
    refine ⟨117768971030121936498789299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78512647353414624332526199 117768971030121936498789299)
    ·
      refine ⟨176653456545182904748183949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117768971030121936498789299 176653456545182904748183949)
      ·
        refine ⟨66245046204443589280568981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176653456545182904748183949 66245046204443589280568981)
        ·
          refine ⟨3105236540833293247526671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66245046204443589280568981 3105236540833293247526671)
          ·
            refine ⟨4657854811249939871290007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105236540833293247526671 4657854811249939871290007)
            ·
              refine ⟨6986782216874909806935011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4657854811249939871290007 6986782216874909806935011)
              ·
                refine ⟨10480173325312364710402517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6986782216874909806935011 10480173325312364710402517)
                ·
                  refine ⟨245629062312008547900059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10480173325312364710402517 245629062312008547900059)
                  ·
                    rfl

theorem cell23_4305248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 7].length) (baseStart_4305248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305248 prefixEnd_4305248 := by exact prefixLift 4305248
  have htrace : WordTrace (prefixWord ++ tailWord_4305248) baseStart_4305248 baseEnd_4305248 := by
    simpa [prefixWord, tailWord_4305248, baseEnd_4305248] using wordTrace_append hprefix tailTrace_4305248
  have hstable : (prefixWord ++ tailWord_4305248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305248).length < 2 ^ (prefixWord ++ tailWord_4305248).sum := by decide
  have hdescent : baseEnd_4305248 < baseStart_4305248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305251 : List Nat := [1, 1, 1, 5, 2, 1, 2, 1, 2, 5, 2]
def baseStart_4305251 : Nat := 118140960795 + 4305251 * 2 ^ 59
def prefixEnd_4305251 : Nat := 4983230072969 + 3 ^ 40 * 4305251 * 2
def baseEnd_4305251 : Nat := 2210663101250040419363017

theorem tailTrace_4305251 : CollatzResearch.WordTrace tailWord_4305251 prefixEnd_4305251 2210663101250040419363017 := by
  unfold tailWord_4305251
  simp only [CollatzResearch.WordTrace]
  refine ⟨157025404125818380177411607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104683602750545586784941071 157025404125818380177411607)
  ·
    refine ⟨235538106188727570266117411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157025404125818380177411607 235538106188727570266117411)
    ·
      refine ⟨353307159283091355399176117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235538106188727570266117411 353307159283091355399176117)
      ·
        refine ⟨33122546182789814568672761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 353307159283091355399176117 33122546182789814568672761)
        ·
          refine ⟨24841909637092360926504571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33122546182789814568672761 24841909637092360926504571)
          ·
            refine ⟨37262864455638541389756857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24841909637092360926504571 37262864455638541389756857)
            ·
              refine ⟨27947148341728906042317643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37262864455638541389756857 27947148341728906042317643)
              ·
                refine ⟨41920722512593359063476465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27947148341728906042317643 41920722512593359063476465)
                ·
                  refine ⟨31440541884445019297607349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41920722512593359063476465 31440541884445019297607349)
                  ·
                    refine ⟨2947550801666720559150689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31440541884445019297607349 2947550801666720559150689)
                    ·
                      refine ⟨2210663101250040419363017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947550801666720559150689 2210663101250040419363017)
                      ·
                        rfl

theorem cell23_4305251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_4305251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305251 prefixEnd_4305251 := by exact prefixLift 4305251
  have htrace : WordTrace (prefixWord ++ tailWord_4305251) baseStart_4305251 baseEnd_4305251 := by
    simpa [prefixWord, tailWord_4305251, baseEnd_4305251] using wordTrace_append hprefix tailTrace_4305251
  have hstable : (prefixWord ++ tailWord_4305251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305251).length < 2 ^ (prefixWord ++ tailWord_4305251).sum := by decide
  have hdescent : baseEnd_4305251 < baseStart_4305251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305325 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_4305325 : Nat := 118140960795 + 4305325 * 2 ^ 59
def prefixEnd_4305325 : Nat := 4983230072969 + 3 ^ 40 * 4305325 * 2
def baseEnd_4305325 : Nat := 736900366272824376612559

theorem tailTrace_4305325 : CollatzResearch.WordTrace tailWord_4305325 prefixEnd_4305325 736900366272824376612559 := by
  unfold tailWord_4305325
  simp only [CollatzResearch.WordTrace]
  refine ⟨157028103127550290815605429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104685402085033527210403619 157028103127550290815605429)
  ·
    refine ⟨14721384668207839763963009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157028103127550290815605429 14721384668207839763963009)
    ·
      refine ⟨11041038501155879822972257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14721384668207839763963009 11041038501155879822972257)
      ·
        refine ⟨8280778875866909867229193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11041038501155879822972257 8280778875866909867229193)
        ·
          refine ⟨6210584156900182400421895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8280778875866909867229193 6210584156900182400421895)
          ·
            refine ⟨9315876235350273600632843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6210584156900182400421895 9315876235350273600632843)
            ·
              refine ⟨13973814353025410400949265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9315876235350273600632843 13973814353025410400949265)
              ·
                refine ⟨10480360764769057800711949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13973814353025410400949265 10480360764769057800711949)
                ·
                  refine ⟨3930135286788396675266981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10480360764769057800711949 3930135286788396675266981)
                  ·
                    refine ⟨736900366272824376612559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930135286788396675266981 736900366272824376612559)
                    ·
                      rfl

theorem cell23_4305325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_4305325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305325 prefixEnd_4305325 := by exact prefixLift 4305325
  have htrace : WordTrace (prefixWord ++ tailWord_4305325) baseStart_4305325 baseEnd_4305325 := by
    simpa [prefixWord, tailWord_4305325, baseEnd_4305325] using wordTrace_append hprefix tailTrace_4305325
  have hstable : (prefixWord ++ tailWord_4305325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305325).length < 2 ^ (prefixWord ++ tailWord_4305325).sum := by decide
  have hdescent : baseEnd_4305325 < baseStart_4305325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305344 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5]
def baseStart_4305344 : Nat := 118140960795 + 4305344 * 2 ^ 59
def prefixEnd_4305344 : Nat := 4983230072969 + 3 ^ 40 * 4305344 * 2
def baseEnd_4305344 : Nat := 2210710854950908555500089

theorem tailTrace_4305344 : CollatzResearch.WordTrace tailWord_4305344 prefixEnd_4305344 2210710854950908555500089 := by
  unfold tailWord_4305344
  simp only [CollatzResearch.WordTrace]
  refine ⟨78514398057240728530273543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104685864076320971373698057 78514398057240728530273543)
  ·
    refine ⟨117771597085861092795410315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78514398057240728530273543 117771597085861092795410315)
    ·
      refine ⟨176657395628791639193115473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117771597085861092795410315 176657395628791639193115473)
      ·
        refine ⟨132493046721593729394836605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176657395628791639193115473 132493046721593729394836605)
        ·
          refine ⟨49684892520597648523063727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132493046721593729394836605 49684892520597648523063727)
          ·
            refine ⟨74527338780896472784595591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49684892520597648523063727 74527338780896472784595591)
            ·
              refine ⟨111791008171344709176893387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74527338780896472784595591 111791008171344709176893387)
              ·
                refine ⟨167686512257017063765340081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111791008171344709176893387 167686512257017063765340081)
                ·
                  refine ⟨125764884192762797824005061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167686512257017063765340081 125764884192762797824005061)
                  ·
                    refine ⟨23580915786143024592000949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125764884192762797824005061 23580915786143024592000949)
                    ·
                      refine ⟨2210710854950908555500089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23580915786143024592000949 2210710854950908555500089)
                      ·
                        rfl

theorem cell23_4305344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_4305344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305344 prefixEnd_4305344 := by exact prefixLift 4305344
  have htrace : WordTrace (prefixWord ++ tailWord_4305344) baseStart_4305344 baseEnd_4305344 := by
    simpa [prefixWord, tailWord_4305344, baseEnd_4305344] using wordTrace_append hprefix tailTrace_4305344
  have hstable : (prefixWord ++ tailWord_4305344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305344).length < 2 ^ (prefixWord ++ tailWord_4305344).sum := by decide
  have hdescent : baseEnd_4305344 < baseStart_4305344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305358 : List Nat := [4, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_4305358 : Nat := 118140960795 + 4305358 * 2 ^ 59
def prefixEnd_4305358 : Nat := 4983230072969 + 3 ^ 40 * 4305358 * 2
def baseEnd_4305358 : Nat := 2210718043680071500725025

theorem tailTrace_4305358 : CollatzResearch.WordTrace tailWord_4305358 prefixEnd_4305358 2210718043680071500725025 := by
  unfold tailWord_4305358
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628663342053842181444591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104686204490953824967704485 19628663342053842181444591)
  ·
    refine ⟨29442995013080763272166887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19628663342053842181444591 29442995013080763272166887)
    ·
      refine ⟨44164492519621144908250331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29442995013080763272166887 44164492519621144908250331)
      ·
        refine ⟨66246738779431717362375497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44164492519621144908250331 66246738779431717362375497)
        ·
          refine ⟨49685054084573788021781623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66246738779431717362375497 49685054084573788021781623)
          ·
            refine ⟨74527581126860682032672435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49685054084573788021781623 74527581126860682032672435)
            ·
              refine ⟨111791371690291023049008653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74527581126860682032672435 111791371690291023049008653)
              ·
                refine ⟨41921764383859133643378245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111791371690291023049008653 41921764383859133643378245)
                ·
                  refine ⟨7860330821973587558133421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41921764383859133643378245 7860330821973587558133421)
                  ·
                    refine ⟨2947624058240095334300033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7860330821973587558133421 2947624058240095334300033)
                    ·
                      refine ⟨2210718043680071500725025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947624058240095334300033 2210718043680071500725025)
                      ·
                        rfl

theorem cell23_4305358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_4305358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305358 prefixEnd_4305358 := by exact prefixLift 4305358
  have htrace : WordTrace (prefixWord ++ tailWord_4305358) baseStart_4305358 baseEnd_4305358 := by
    simpa [prefixWord, tailWord_4305358, baseEnd_4305358] using wordTrace_append hprefix tailTrace_4305358
  have hstable : (prefixWord ++ tailWord_4305358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305358).length < 2 ^ (prefixWord ++ tailWord_4305358).sum := by decide
  have hdescent : baseEnd_4305358 < baseStart_4305358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305365 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4305365 : Nat := 118140960795 + 4305365 * 2 ^ 59
def prefixEnd_4305365 : Nat := 4983230072969 + 3 ^ 40 * 4305365 * 2
def baseEnd_4305365 : Nat := 2210721638044652973337493

theorem tailTrace_4305365 : CollatzResearch.WordTrace tailWord_4305365 prefixEnd_4305365 2210721638044652973337493 := by
  unfold tailWord_4305365
  simp only [CollatzResearch.WordTrace]
  refine ⟨157029562047405377647061549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104686374698270251764707699 157029562047405377647061549)
  ·
    refine ⟨58886085767777016617648081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157029562047405377647061549 58886085767777016617648081)
    ·
      refine ⟨44164564325832762463236061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58886085767777016617648081 44164564325832762463236061)
      ·
        refine ⟨16561711622187285923713523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44164564325832762463236061 16561711622187285923713523)
        ·
          refine ⟨24842567433280928885570285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16561711622187285923713523 24842567433280928885570285)
          ·
            refine ⟨9315962787480348332088857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24842567433280928885570285 9315962787480348332088857)
            ·
              refine ⟨6986972090610261249066643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9315962787480348332088857 6986972090610261249066643)
              ·
                refine ⟨10480458135915391873599965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6986972090610261249066643 10480458135915391873599965)
                ·
                  refine ⟨3930171800968271952599987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10480458135915391873599965 3930171800968271952599987)
                  ·
                    refine ⟨5895257701452407928899981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3930171800968271952599987 5895257701452407928899981)
                    ·
                      refine ⟨2210721638044652973337493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5895257701452407928899981 2210721638044652973337493)
                      ·
                        rfl

theorem cell23_4305365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4305365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305365 prefixEnd_4305365 := by exact prefixLift 4305365
  have htrace : WordTrace (prefixWord ++ tailWord_4305365) baseStart_4305365 baseEnd_4305365 := by
    simpa [prefixWord, tailWord_4305365, baseEnd_4305365] using wordTrace_append hprefix tailTrace_4305365
  have hstable : (prefixWord ++ tailWord_4305365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305365).length < 2 ^ (prefixWord ++ tailWord_4305365).sum := by decide
  have hdescent : baseEnd_4305365 < baseStart_4305365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305388 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_4305388 : Nat := 118140960795 + 4305388 * 2 ^ 59
def prefixEnd_4305388 : Nat := 4983230072969 + 3 ^ 40 * 4305388 * 2
def baseEnd_4305388 : Nat := 2210733448099706383349887

theorem tailTrace_4305388 : CollatzResearch.WordTrace tailWord_4305388 prefixEnd_4305388 2210733448099706383349887 := by
  unfold tailWord_4305388
  simp only [CollatzResearch.WordTrace]
  refine ⟨78515200463161026287574409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104686933950881368383432545 78515200463161026287574409)
  ·
    refine ⟨58886400347370769715680807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78515200463161026287574409 58886400347370769715680807)
    ·
      refine ⟨88329600521056154573521211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58886400347370769715680807 88329600521056154573521211)
      ·
        refine ⟨132494400781584231860281817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88329600521056154573521211 132494400781584231860281817)
        ·
          refine ⟨99370800586188173895211363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132494400781584231860281817 99370800586188173895211363)
          ·
            refine ⟨149056200879282260842817045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99370800586188173895211363 149056200879282260842817045)
            ·
              refine ⟨6987009416216355977007049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 149056200879282260842817045 6987009416216355977007049)
              ·
                refine ⟨5240257062162266982755287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6987009416216355977007049 5240257062162266982755287)
                ·
                  refine ⟨7860385593243400474132931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240257062162266982755287 7860385593243400474132931)
                  ·
                    refine ⟨11790578389865100711199397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7860385593243400474132931 11790578389865100711199397)
                    ·
                      refine ⟨2210733448099706383349887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11790578389865100711199397 2210733448099706383349887)
                      ·
                        rfl

theorem cell23_4305388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_4305388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305388 prefixEnd_4305388 := by exact prefixLift 4305388
  have htrace : WordTrace (prefixWord ++ tailWord_4305388) baseStart_4305388 baseEnd_4305388 := by
    simpa [prefixWord, tailWord_4305388, baseEnd_4305388] using wordTrace_append hprefix tailTrace_4305388
  have hstable : (prefixWord ++ tailWord_4305388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305388).length < 2 ^ (prefixWord ++ tailWord_4305388).sum := by decide
  have hdescent : baseEnd_4305388 < baseStart_4305388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305398 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_4305398 : Nat := 118140960795 + 4305398 * 2 ^ 59
def prefixEnd_4305398 : Nat := 4983230072969 + 3 ^ 40 * 4305398 * 2
def baseEnd_4305398 : Nat := 736912860968750448074947

theorem tailTrace_4305398 : CollatzResearch.WordTrace tailWord_4305398 prefixEnd_4305398 736912860968750448074947 := by
  unfold tailWord_4305398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9814422853517864017688303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104687177104190549522008565 9814422853517864017688303)
  ·
    refine ⟨14721634280276796026532455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9814422853517864017688303 14721634280276796026532455)
    ·
      refine ⟨22082451420415194039798683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14721634280276796026532455 22082451420415194039798683)
      ·
        refine ⟨33123677130622791059698025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22082451420415194039798683 33123677130622791059698025)
        ·
          refine ⟨24842757847967093294773519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33123677130622791059698025 24842757847967093294773519)
          ·
            refine ⟨37264136771950639942160279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24842757847967093294773519 37264136771950639942160279)
            ·
              refine ⟨55896205157925959913240419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37264136771950639942160279 55896205157925959913240419)
              ·
                refine ⟨83844307736888939869860629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55896205157925959913240419 83844307736888939869860629)
                ·
                  refine ⟨3930201925166669056399717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 83844307736888939869860629 3930201925166669056399717)
                  ·
                    refine ⟨736912860968750448074947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930201925166669056399717 736912860968750448074947)
                    ·
                      rfl

theorem cell23_4305398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_4305398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305398 prefixEnd_4305398 := by exact prefixLift 4305398
  have htrace : WordTrace (prefixWord ++ tailWord_4305398) baseStart_4305398 baseEnd_4305398 := by
    simpa [prefixWord, tailWord_4305398, baseEnd_4305398] using wordTrace_append hprefix tailTrace_4305398
  have hstable : (prefixWord ++ tailWord_4305398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305398).length < 2 ^ (prefixWord ++ tailWord_4305398).sum := by decide
  have hdescent : baseEnd_4305398 < baseStart_4305398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305401 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_4305401 : Nat := 118140960795 + 4305401 * 2 ^ 59
def prefixEnd_4305401 : Nat := 4983230072969 + 3 ^ 40 * 4305401 * 2
def baseEnd_4305401 : Nat := 2210740123348214832487327

theorem tailTrace_4305401 : CollatzResearch.WordTrace tailWord_4305401 prefixEnd_4305401 2210740123348214832487327 := by
  unfold tailWord_4305401
  simp only [CollatzResearch.WordTrace]
  refine ⟨157030875075274955795372057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104687250050183303863581371 157030875075274955795372057)
  ·
    refine ⟨117773156306456216846529043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157030875075274955795372057 117773156306456216846529043)
    ·
      refine ⟨176659734459684325269793565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117773156306456216846529043 176659734459684325269793565)
      ·
        refine ⟨66247400422381621976172587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176659734459684325269793565 66247400422381621976172587)
        ·
          refine ⟨99371100633572432964258881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66247400422381621976172587 99371100633572432964258881)
          ·
            refine ⟨74528325475179324723194161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99371100633572432964258881 74528325475179324723194161)
            ·
              refine ⟨55896244106384493542395621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74528325475179324723194161 55896244106384493542395621)
              ·
                refine ⟨10480545769947092539199179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55896244106384493542395621 10480545769947092539199179)
                ·
                  refine ⟨15720818654920638808798769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10480545769947092539199179 15720818654920638808798769)
                  ·
                    refine ⟨11790613991190479106599077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15720818654920638808798769 11790613991190479106599077)
                    ·
                      refine ⟨2210740123348214832487327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11790613991190479106599077 2210740123348214832487327)
                      ·
                        rfl

theorem cell23_4305401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_4305401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305401 prefixEnd_4305401 := by exact prefixLift 4305401
  have htrace : WordTrace (prefixWord ++ tailWord_4305401) baseStart_4305401 baseEnd_4305401 := by
    simpa [prefixWord, tailWord_4305401, baseEnd_4305401] using wordTrace_append hprefix tailTrace_4305401
  have hstable : (prefixWord ++ tailWord_4305401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305401).length < 2 ^ (prefixWord ++ tailWord_4305401).sum := by decide
  have hdescent : baseEnd_4305401 < baseStart_4305401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305422 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4305422 : Nat := 118140960795 + 4305422 * 2 ^ 59
def prefixEnd_4305422 : Nat := 4983230072969 + 3 ^ 40 * 4305422 * 2
def baseEnd_4305422 : Nat := 2210750906441959250324731

theorem tailTrace_4305422 : CollatzResearch.WordTrace tailWord_4305422 prefixEnd_4305422 2210750906441959250324731 := by
  unfold tailWord_4305422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19628955126024859547735815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104687760672132584254591013 19628955126024859547735815)
  ·
    refine ⟨29443432689037289321603723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19628955126024859547735815 29443432689037289321603723)
    ·
      refine ⟨44165149033555933982405585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29443432689037289321603723 44165149033555933982405585)
      ·
        refine ⟨33123861775166950486804189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44165149033555933982405585 33123861775166950486804189)
        ·
          refine ⟨12421448165687606432551571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33123861775166950486804189 12421448165687606432551571)
          ·
            refine ⟨18632172248531409648827357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12421448165687606432551571 18632172248531409648827357)
            ·
              refine ⟨6987064593199278618310259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18632172248531409648827357 6987064593199278618310259)
              ·
                refine ⟨10480596889798917927465389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6987064593199278618310259 10480596889798917927465389)
                ·
                  refine ⟨3930223833674594222799521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10480596889798917927465389 3930223833674594222799521)
                  ·
                    refine ⟨2947667875255945667099641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930223833674594222799521 2947667875255945667099641)
                    ·
                      refine ⟨2210750906441959250324731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947667875255945667099641 2210750906441959250324731)
                      ·
                        rfl

theorem cell23_4305422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4305422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305422 prefixEnd_4305422 := by exact prefixLift 4305422
  have htrace : WordTrace (prefixWord ++ tailWord_4305422) baseStart_4305422 baseEnd_4305422 := by
    simpa [prefixWord, tailWord_4305422, baseEnd_4305422] using wordTrace_append hprefix tailTrace_4305422
  have hstable : (prefixWord ++ tailWord_4305422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305422).length < 2 ^ (prefixWord ++ tailWord_4305422).sum := by decide
  have hdescent : baseEnd_4305422 < baseStart_4305422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305428 : List Nat := [2, 4, 3, 1, 1, 1, 1, 10]
def baseStart_4305428 : Nat := 118140960795 + 4305428 * 2 ^ 59
def prefixEnd_4305428 : Nat := 4983230072969 + 3 ^ 40 * 4305428 * 2
def baseEnd_4305428 : Nat := 81879777308366156549989

theorem tailTrace_4305428 : CollatzResearch.WordTrace tailWord_4305428 prefixEnd_4305428 81879777308366156549989 := by
  unfold tailWord_4305428
  simp only [CollatzResearch.WordTrace]
  refine ⟨78515929923088569703302469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104687906564118092937736625 78515929923088569703302469)
  ·
    refine ⟨14721736860579106819369213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78515929923088569703302469 14721736860579106819369213)
    ·
      refine ⟨5520651322717165057263455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14721736860579106819369213 5520651322717165057263455)
      ·
        refine ⟨8280976984075747585895183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520651322717165057263455 8280976984075747585895183)
        ·
          refine ⟨12421465476113621378842775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8280976984075747585895183 12421465476113621378842775)
          ·
            refine ⟨18632198214170432068264163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12421465476113621378842775 18632198214170432068264163)
            ·
              refine ⟨27948297321255648102396245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18632198214170432068264163 27948297321255648102396245)
              ·
                refine ⟨81879777308366156549989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27948297321255648102396245 81879777308366156549989)
                ·
                  rfl

theorem cell23_4305428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 10].length) (baseStart_4305428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305428 prefixEnd_4305428 := by exact prefixLift 4305428
  have htrace : WordTrace (prefixWord ++ tailWord_4305428) baseStart_4305428 baseEnd_4305428 := by
    simpa [prefixWord, tailWord_4305428, baseEnd_4305428] using wordTrace_append hprefix tailTrace_4305428
  have hstable : (prefixWord ++ tailWord_4305428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305428).length < 2 ^ (prefixWord ++ tailWord_4305428).sum := by decide
  have hdescent : baseEnd_4305428 < baseStart_4305428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305432 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 2, 4]
def baseStart_4305432 : Nat := 118140960795 + 4305432 * 2 ^ 59
def prefixEnd_4305432 : Nat := 4983230072969 + 3 ^ 40 * 4305432 * 2
def baseEnd_4305432 : Nat := 736918680416168070399895

theorem tailTrace_4305432 : CollatzResearch.WordTrace tailWord_4305432 prefixEnd_4305432 736918680416168070399895 := by
  unfold tailWord_4305432
  simp only [CollatzResearch.WordTrace]
  refine ⟨78516002869081324044875275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104688003825441765393167033 78516002869081324044875275)
  ·
    refine ⟨117774004303621986067312913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78516002869081324044875275 117774004303621986067312913)
    ·
      refine ⟨88330503227716489550484685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117774004303621986067312913 88330503227716489550484685)
      ·
        refine ⟨33123938710393683581431757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88330503227716489550484685 33123938710393683581431757)
        ·
          refine ⟨12421477016397631343036909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33123938710393683581431757 12421477016397631343036909)
          ·
            refine ⟨4658053881149111753638841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12421477016397631343036909 4658053881149111753638841)
            ·
              refine ⟨3493540410861833815229131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4658053881149111753638841 3493540410861833815229131)
              ·
                refine ⟨5240310616292750722843697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493540410861833815229131 5240310616292750722843697)
                ·
                  refine ⟨3930232962219563042132773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240310616292750722843697 3930232962219563042132773)
                  ·
                    refine ⟨736918680416168070399895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930232962219563042132773 736918680416168070399895)
                    ·
                      rfl

theorem cell23_4305432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 2, 4].length) (baseStart_4305432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305432 prefixEnd_4305432 := by exact prefixLift 4305432
  have htrace : WordTrace (prefixWord ++ tailWord_4305432) baseStart_4305432 baseEnd_4305432 := by
    simpa [prefixWord, tailWord_4305432, baseEnd_4305432] using wordTrace_append hprefix tailTrace_4305432
  have hstable : (prefixWord ++ tailWord_4305432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305432).length < 2 ^ (prefixWord ++ tailWord_4305432).sum := by decide
  have hdescent : baseEnd_4305432 < baseStart_4305432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305471 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 2, 6]
def baseStart_4305471 : Nat := 118140960795 + 4305471 * 2 ^ 59
def prefixEnd_4305471 : Nat := 4983230072969 + 3 ^ 40 * 4305471 * 2
def baseEnd_4305471 : Nat := 736925355664676519537335

theorem tailTrace_4305471 : CollatzResearch.WordTrace tailWord_4305471 prefixEnd_4305471 736925355664676519537335 := by
  unfold tailWord_4305471
  simp only [CollatzResearch.WordTrace]
  refine ⟨157033428185021357750420267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104688952123347571833613511 157033428185021357750420267)
  ·
    refine ⟨235550142277532036625630401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157033428185021357750420267 235550142277532036625630401)
    ·
      refine ⟨176662606708149027469222801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235550142277532036625630401 176662606708149027469222801)
      ·
        refine ⟨132496955031111770601917101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176662606708149027469222801 132496955031111770601917101)
        ·
          refine ⟨49686358136666913975718913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132496955031111770601917101 49686358136666913975718913)
          ·
            refine ⟨37264768602500185481789185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49686358136666913975718913 37264768602500185481789185)
            ·
              refine ⟨27948576451875139111341889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37264768602500185481789185 27948576451875139111341889)
              ·
                refine ⟨20961432338906354333506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27948576451875139111341889 20961432338906354333506417)
                ·
                  refine ⟨15721074254179765750129813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20961432338906354333506417 15721074254179765750129813)
                  ·
                    refine ⟨736925355664676519537335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15721074254179765750129813 736925355664676519537335)
                    ·
                      rfl

theorem cell23_4305471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_4305471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305471 prefixEnd_4305471 := by exact prefixLift 4305471
  have htrace : WordTrace (prefixWord ++ tailWord_4305471) baseStart_4305471 baseEnd_4305471 := by
    simpa [prefixWord, tailWord_4305471, baseEnd_4305471] using wordTrace_append hprefix tailTrace_4305471
  have hstable : (prefixWord ++ tailWord_4305471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305471).length < 2 ^ (prefixWord ++ tailWord_4305471).sum := by decide
  have hdescent : baseEnd_4305471 < baseStart_4305471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305495 : List Nat := [1, 1, 3, 2, 2, 2, 4, 1, 1, 4, 2]
def baseStart_4305495 : Nat := 118140960795 + 4305495 * 2 ^ 59
def prefixEnd_4305495 : Nat := 4983230072969 + 3 ^ 40 * 4305495 * 2
def baseEnd_4305495 : Nat := 2210788390529737464711895

theorem tailTrace_4305495 : CollatzResearch.WordTrace tailWord_4305495 prefixEnd_4305495 2210788390529737464711895 := by
  unfold tailWord_4305495
  simp only [CollatzResearch.WordTrace]
  refine ⟨157034303536934409849293939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104689535691289606566195959 157034303536934409849293939)
  ·
    refine ⟨235551455305401614773940909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157034303536934409849293939 235551455305401614773940909)
    ·
      refine ⟨88331795739525605540227841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235551455305401614773940909 88331795739525605540227841)
      ·
        refine ⟨66248846804644204155170881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88331795739525605540227841 66248846804644204155170881)
        ·
          refine ⟨49686635103483153116378161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66248846804644204155170881 49686635103483153116378161)
          ·
            refine ⟨37264976327612364837283621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49686635103483153116378161 37264976327612364837283621)
            ·
              refine ⟨6987183061427318406990679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37264976327612364837283621 6987183061427318406990679)
              ·
                refine ⟨10480774592140977610486019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6987183061427318406990679 10480774592140977610486019)
                ·
                  refine ⟨15721161888211466415729029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10480774592140977610486019 15721161888211466415729029)
                  ·
                    refine ⟨2947717854039649952949193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15721161888211466415729029 2947717854039649952949193)
                    ·
                      refine ⟨2210788390529737464711895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947717854039649952949193 2210788390529737464711895)
                      ·
                        rfl

theorem cell23_4305495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_4305495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305495 prefixEnd_4305495 := by exact prefixLift 4305495
  have htrace : WordTrace (prefixWord ++ tailWord_4305495) baseStart_4305495 baseEnd_4305495 := by
    simpa [prefixWord, tailWord_4305495, baseEnd_4305495] using wordTrace_append hprefix tailTrace_4305495
  have hstable : (prefixWord ++ tailWord_4305495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305495).length < 2 ^ (prefixWord ++ tailWord_4305495).sum := by decide
  have hdescent : baseEnd_4305495 < baseStart_4305495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305511 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7]
def baseStart_4305511 : Nat := 118140960795 + 4305511 * 2 ^ 59
def prefixEnd_4305511 : Nat := 4983230072969 + 3 ^ 40 * 4305511 * 2
def baseEnd_4305511 : Nat := 2210796606220209402111821

theorem tailTrace_4305511 : CollatzResearch.WordTrace tailWord_4305511 prefixEnd_4305511 2210796606220209402111821 := by
  unfold tailWord_4305511
  simp only [CollatzResearch.WordTrace]
  refine ⟨157034887104876444581876387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104689924736584296387917591 157034887104876444581876387)
  ·
    refine ⟨235552330657314666872814581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157034887104876444581876387 235552330657314666872814581)
    ·
      refine ⟨22083030999123250019326367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 235552330657314666872814581 22083030999123250019326367)
      ·
        refine ⟨33124546498684875028989551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22083030999123250019326367 33124546498684875028989551)
        ·
          refine ⟨49686819748027312543484327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33124546498684875028989551 49686819748027312543484327)
          ·
            refine ⟨74530229622040968815226491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49686819748027312543484327 74530229622040968815226491)
            ·
              refine ⟨111795344433061453222839737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74530229622040968815226491 111795344433061453222839737)
              ·
                refine ⟨83846508324796089917129803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111795344433061453222839737 83846508324796089917129803)
                ·
                  refine ⟨125769762487194134875694705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83846508324796089917129803 125769762487194134875694705)
                  ·
                    refine ⟨94327321865395601156771029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125769762487194134875694705 94327321865395601156771029)
                    ·
                      refine ⟨2210796606220209402111821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94327321865395601156771029 2210796606220209402111821)
                      ·
                        rfl

theorem cell23_4305511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_4305511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305511 prefixEnd_4305511 := by exact prefixLift 4305511
  have htrace : WordTrace (prefixWord ++ tailWord_4305511) baseStart_4305511 baseEnd_4305511 := by
    simpa [prefixWord, tailWord_4305511, baseEnd_4305511] using wordTrace_append hprefix tailTrace_4305511
  have hstable : (prefixWord ++ tailWord_4305511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305511).length < 2 ^ (prefixWord ++ tailWord_4305511).sum := by decide
  have hdescent : baseEnd_4305511 < baseStart_4305511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305529 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 2, 2, 2]
def baseStart_4305529 : Nat := 118140960795 + 4305529 * 2 ^ 59
def prefixEnd_4305529 : Nat := 4983230072969 + 3 ^ 40 * 4305529 * 2
def baseEnd_4305529 : Nat := 2210805848871990331686739

theorem tailTrace_4305529 : CollatzResearch.WordTrace tailWord_4305529 prefixEnd_4305529 2210805848871990331686739 := by
  unfold tailWord_4305529
  simp only [CollatzResearch.WordTrace]
  refine ⟨157035543618811233656031641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104690362412540822437354427 157035543618811233656031641)
  ·
    refine ⟨117776657714108425242023731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157035543618811233656031641 117776657714108425242023731)
    ·
      refine ⟨176664986571162637863035597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117776657714108425242023731 176664986571162637863035597)
      ·
        refine ⟨66249369964185989198638349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176664986571162637863035597 66249369964185989198638349)
        ·
          refine ⟨24843513736569745949489381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66249369964185989198638349 24843513736569745949489381)
          ·
            refine ⟨4658158825606827365529259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24843513736569745949489381 4658158825606827365529259)
            ·
              refine ⟨6987238238410241048293889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4658158825606827365529259 6987238238410241048293889)
              ·
                refine ⟨5240428678807680786220417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6987238238410241048293889 5240428678807680786220417)
                ·
                  refine ⟨3930321509105760589665313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240428678807680786220417 3930321509105760589665313)
                  ·
                    refine ⟨2947741131829320442248985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930321509105760589665313 2947741131829320442248985)
                    ·
                      refine ⟨2210805848871990331686739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947741131829320442248985 2210805848871990331686739)
                      ·
                        rfl

theorem cell23_4305529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_4305529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305529 prefixEnd_4305529 := by exact prefixLift 4305529
  have htrace : WordTrace (prefixWord ++ tailWord_4305529) baseStart_4305529 baseEnd_4305529 := by
    simpa [prefixWord, tailWord_4305529, baseEnd_4305529] using wordTrace_append hprefix tailTrace_4305529
  have hstable : (prefixWord ++ tailWord_4305529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305529).length < 2 ^ (prefixWord ++ tailWord_4305529).sum := by decide
  have hdescent : baseEnd_4305529 < baseStart_4305529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305546 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2]
def baseStart_4305546 : Nat := 118140960795 + 4305546 * 2 ^ 59
def prefixEnd_4305546 : Nat := 4983230072969 + 3 ^ 40 * 4305546 * 2
def baseEnd_4305546 : Nat := 2210814578043116765174161

theorem tailTrace_4305546 : CollatzResearch.WordTrace tailWord_4305546 prefixEnd_4305546 2210814578043116765174161 := by
  unfold tailWord_4305546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39259040914937411389850123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104690775773166430372933661 39259040914937411389850123)
  ·
    refine ⟨58888561372406117084775185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39259040914937411389850123 58888561372406117084775185)
    ·
      refine ⟨44166421029304587813581389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58888561372406117084775185 44166421029304587813581389)
      ·
        refine ⟨16562407885989220430093021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44166421029304587813581389 16562407885989220430093021)
        ·
          refine ⟨6210902957245957661284883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16562407885989220430093021 6210902957245957661284883)
          ·
            refine ⟨9316354435868936491927325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6210902957245957661284883 9316354435868936491927325)
            ·
              refine ⟨3493632913450851184472747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9316354435868936491927325 3493632913450851184472747)
              ·
                refine ⟨5240449370176276776709121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3493632913450851184472747 5240449370176276776709121)
                ·
                  refine ⟨3930337027632207582531841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5240449370176276776709121 3930337027632207582531841)
                  ·
                    refine ⟨2947752770724155686898881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3930337027632207582531841 2947752770724155686898881)
                    ·
                      refine ⟨2210814578043116765174161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947752770724155686898881 2210814578043116765174161)
                      ·
                        rfl

theorem cell23_4305546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_4305546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305546 prefixEnd_4305546 := by exact prefixLift 4305546
  have htrace : WordTrace (prefixWord ++ tailWord_4305546) baseStart_4305546 baseEnd_4305546 := by
    simpa [prefixWord, tailWord_4305546, baseEnd_4305546] using wordTrace_append hprefix tailTrace_4305546
  have hstable : (prefixWord ++ tailWord_4305546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305546).length < 2 ^ (prefixWord ++ tailWord_4305546).sum := by decide
  have hdescent : baseEnd_4305546 < baseStart_4305546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305561 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_4305561 : Nat := 118140960795 + 4305561 * 2 ^ 59
def prefixEnd_4305561 : Nat := 4983230072969 + 3 ^ 40 * 4305561 * 2
def baseEnd_4305561 : Nat := 736940760084311402162197

theorem tailTrace_4305561 : CollatzResearch.WordTrace tailWord_4305561 prefixEnd_4305561 736940760084311402162197 := by
  unfold tailWord_4305561
  simp only [CollatzResearch.WordTrace]
  refine ⟨157036710754695303121196537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104691140503130202080797691 157036710754695303121196537)
  ·
    refine ⟨117777533066021477340897403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157036710754695303121196537 117777533066021477340897403)
    ·
      refine ⟨176666299599032216011346105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117777533066021477340897403 176666299599032216011346105)
      ·
        refine ⟨132499724699274162008509579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176666299599032216011346105 132499724699274162008509579)
        ·
          refine ⟨198749587048911243012764369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132499724699274162008509579 198749587048911243012764369)
          ·
            refine ⟨149062190286683432259573277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198749587048911243012764369 149062190286683432259573277)
            ·
              refine ⟨55898321357506287097339979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149062190286683432259573277 55898321357506287097339979)
              ·
                refine ⟨83847482036259430646009969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55898321357506287097339979 83847482036259430646009969)
                ·
                  refine ⟨62885611527194572984507477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83847482036259430646009969 62885611527194572984507477)
                  ·
                    refine ⟨736940760084311402162197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 62885611527194572984507477 736940760084311402162197)
                    ·
                      rfl

theorem cell23_4305561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_4305561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305561 prefixEnd_4305561 := by exact prefixLift 4305561
  have htrace : WordTrace (prefixWord ++ tailWord_4305561) baseStart_4305561 baseEnd_4305561 := by
    simpa [prefixWord, tailWord_4305561, baseEnd_4305561] using wordTrace_append hprefix tailTrace_4305561
  have hstable : (prefixWord ++ tailWord_4305561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305561).length < 2 ^ (prefixWord ++ tailWord_4305561).sum := by decide
  have hdescent : baseEnd_4305561 < baseStart_4305561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305569 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 5]
def baseStart_4305569 : Nat := 118140960795 + 4305569 * 2 ^ 59
def prefixEnd_4305569 : Nat := 4983230072969 + 3 ^ 40 * 4305569 * 2
def baseEnd_4305569 : Nat := 245647376455352241687395

theorem tailTrace_4305569 : CollatzResearch.WordTrace tailWord_4305569 prefixEnd_4305569 245647376455352241687395 := by
  unfold tailWord_4305569
  simp only [CollatzResearch.WordTrace]
  refine ⟨157037002538666320487487761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104691335025777546991658507 157037002538666320487487761)
  ·
    refine ⟨117777751903999740365615821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157037002538666320487487761 117777751903999740365615821)
    ·
      refine ⟨44166656963999902637105933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117777751903999740365615821 44166656963999902637105933)
      ·
        refine ⟨16562496361499963488914725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44166656963999902637105933 16562496361499963488914725)
        ·
          refine ⟨3105468067781243154171511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16562496361499963488914725 3105468067781243154171511)
          ·
            refine ⟨4658202101671864731257267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3105468067781243154171511 4658202101671864731257267)
            ·
              refine ⟨6987303152507797096885901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4658202101671864731257267 6987303152507797096885901)
              ·
                refine ⟨2620238682190423911332213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6987303152507797096885901 2620238682190423911332213)
                ·
                  refine ⟨245647376455352241687395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2620238682190423911332213 245647376455352241687395)
                  ·
                    rfl

theorem cell23_4305569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 5].length) (baseStart_4305569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305569 prefixEnd_4305569 := by exact prefixLift 4305569
  have htrace : WordTrace (prefixWord ++ tailWord_4305569) baseStart_4305569 baseEnd_4305569 := by
    simpa [prefixWord, tailWord_4305569, baseEnd_4305569] using wordTrace_append hprefix tailTrace_4305569
  have hstable : (prefixWord ++ tailWord_4305569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305569).length < 2 ^ (prefixWord ++ tailWord_4305569).sum := by decide
  have hdescent : baseEnd_4305569 < baseStart_4305569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305582 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4305582 : Nat := 118140960795 + 4305582 * 2 ^ 59
def prefixEnd_4305582 : Nat := 4983230072969 + 3 ^ 40 * 4305582 * 2
def baseEnd_4305582 : Nat := 736944354448892874774665

theorem tailTrace_4305582 : CollatzResearch.WordTrace tailWord_4305582 prefixEnd_4305582 736944354448892874774665 := by
  unfold tailWord_4305582
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629684585952402963463875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104691651125079482471807333 19629684585952402963463875)
  ·
    refine ⟨29444526878928604445195813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19629684585952402963463875 29444526878928604445195813)
    ·
      refine ⟨5520848789799113333474215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29444526878928604445195813 5520848789799113333474215)
      ·
        refine ⟨8281273184698670000211323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5520848789799113333474215 8281273184698670000211323)
        ·
          refine ⟨12421909777048005000316985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8281273184698670000211323 12421909777048005000316985)
          ·
            refine ⟨9316432332786003750237739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12421909777048005000316985 9316432332786003750237739)
            ·
              refine ⟨13974648499179005625356609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9316432332786003750237739 13974648499179005625356609)
              ·
                refine ⟨10480986374384254219017457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13974648499179005625356609 10480986374384254219017457)
                ·
                  refine ⟨7860739780788190664263093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10480986374384254219017457 7860739780788190664263093)
                  ·
                    refine ⟨736944354448892874774665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7860739780788190664263093 736944354448892874774665)
                    ·
                      rfl

theorem cell23_4305582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4305582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305582 prefixEnd_4305582 := by exact prefixLift 4305582
  have htrace : WordTrace (prefixWord ++ tailWord_4305582) baseStart_4305582 baseEnd_4305582 := by
    simpa [prefixWord, tailWord_4305582, baseEnd_4305582] using wordTrace_append hprefix tailTrace_4305582
  have hstable : (prefixWord ++ tailWord_4305582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305582).length < 2 ^ (prefixWord ++ tailWord_4305582).sum := by decide
  have hdescent : baseEnd_4305582 < baseStart_4305582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305646 : List Nat := [4, 1, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_4305646 : Nat := 118140960795 + 4305646 * 2 ^ 59
def prefixEnd_4305646 : Nat := 4983230072969 + 3 ^ 40 * 4305646 * 2
def baseEnd_4305646 : Nat := 736955308702855457974567

theorem tailTrace_4305646 : CollatzResearch.WordTrace tailWord_4305646 prefixEnd_4305646 736955308702855457974567 := by
  unfold tailWord_4305646
  simp only [CollatzResearch.WordTrace]
  refine ⟨19629976369923420329755099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104693207306258241758693861 19629976369923420329755099)
  ·
    refine ⟨29444964554885130494632649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19629976369923420329755099 29444964554885130494632649)
    ·
      refine ⟨22083723416163847870974487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29444964554885130494632649 22083723416163847870974487)
      ·
        refine ⟨33125585124245771806461731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22083723416163847870974487 33125585124245771806461731)
        ·
          refine ⟨49688377686368657709692597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33125585124245771806461731 49688377686368657709692597)
          ·
            refine ⟨4658285408097061660283681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49688377686368657709692597 4658285408097061660283681)
            ·
              refine ⟨3493714056072796245212761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4658285408097061660283681 3493714056072796245212761)
              ·
                refine ⟨2620285542054597183909571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3493714056072796245212761 2620285542054597183909571)
                ·
                  refine ⟨3930428313081895775864357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2620285542054597183909571 3930428313081895775864357)
                  ·
                    refine ⟨736955308702855457974567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930428313081895775864357 736955308702855457974567)
                    ·
                      rfl

theorem cell23_4305646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_4305646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305646 prefixEnd_4305646 := by exact prefixLift 4305646
  have htrace : WordTrace (prefixWord ++ tailWord_4305646) baseStart_4305646 baseEnd_4305646 := by
    simpa [prefixWord, tailWord_4305646, baseEnd_4305646] using wordTrace_append hprefix tailTrace_4305646
  have hstable : (prefixWord ++ tailWord_4305646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305646).length < 2 ^ (prefixWord ++ tailWord_4305646).sum := by decide
  have hdescent : baseEnd_4305646 < baseStart_4305646 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305675 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 4]
def baseStart_4305675 : Nat := 118140960795 + 4305675 * 2 ^ 59
def prefixEnd_4305675 : Nat := 4983230072969 + 3 ^ 40 * 4305675 * 2
def baseEnd_4305675 : Nat := 2210880817047546760461067

theorem tailTrace_4305675 : CollatzResearch.WordTrace tailWord_4305675 prefixEnd_4305675 2210880817047546760461067 := by
  unfold tailWord_4305675
  simp only [CollatzResearch.WordTrace]
  refine ⟨157040868676282300590846479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104693912450854867060564319 157040868676282300590846479)
  ·
    refine ⟨235561303014423450886269719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157040868676282300590846479 235561303014423450886269719)
    ·
      refine ⟨353341954521635176329404579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235561303014423450886269719 353341954521635176329404579)
      ·
        refine ⟨530012931782452764494106869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353341954521635176329404579 530012931782452764494106869)
        ·
          refine ⟨49688712354604946671322519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 530012931782452764494106869 49688712354604946671322519)
          ·
            refine ⟨74533068531907420006983779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49688712354604946671322519 74533068531907420006983779)
            ·
              refine ⟨111799602797861130010475669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74533068531907420006983779 111799602797861130010475669)
              ·
                refine ⟨5240606381149740469241047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 111799602797861130010475669 5240606381149740469241047)
                ·
                  refine ⟨7860909571724610703861571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240606381149740469241047 7860909571724610703861571)
                  ·
                    refine ⟨11791364357586916055792357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7860909571724610703861571 11791364357586916055792357)
                    ·
                      refine ⟨2210880817047546760461067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11791364357586916055792357 2210880817047546760461067)
                      ·
                        rfl

theorem cell23_4305675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 1, 4].length) (baseStart_4305675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305675 prefixEnd_4305675 := by exact prefixLift 4305675
  have htrace : WordTrace (prefixWord ++ tailWord_4305675) baseStart_4305675 baseEnd_4305675 := by
    simpa [prefixWord, tailWord_4305675, baseEnd_4305675] using wordTrace_append hprefix tailTrace_4305675
  have hstable : (prefixWord ++ tailWord_4305675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305675).length < 2 ^ (prefixWord ++ tailWord_4305675).sum := by decide
  have hdescent : baseEnd_4305675 < baseStart_4305675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305685 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_4305685 : Nat := 118140960795 + 4305685 * 2 ^ 59
def prefixEnd_4305685 : Nat := 4983230072969 + 3 ^ 40 * 4305685 * 2
def baseEnd_4305685 : Nat := 736961983951363907112007

theorem tailTrace_4305685 : CollatzResearch.WordTrace tailWord_4305685 prefixEnd_4305685 736961983951363907112007 := by
  unfold tailWord_4305685
  simp only [CollatzResearch.WordTrace]
  refine ⟨157041233406246072298710509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104694155604164048199140339 157041233406246072298710509)
  ·
    refine ⟨58890462527342277112016441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157041233406246072298710509 58890462527342277112016441)
    ·
      refine ⟨44167846895506707834012331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58890462527342277112016441 44167846895506707834012331)
      ·
        refine ⟨66251770343260061751018497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44167846895506707834012331 66251770343260061751018497)
        ·
          refine ⟨49688827757445046313263873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66251770343260061751018497 49688827757445046313263873)
          ·
            refine ⟨37266620818083784734947905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49688827757445046313263873 37266620818083784734947905)
            ·
              refine ⟨27949965613562838551210929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37266620818083784734947905 27949965613562838551210929)
              ·
                refine ⟨20962474210172128913408197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27949965613562838551210929 20962474210172128913408197)
                ·
                  refine ⟨3930463914407274171264037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20962474210172128913408197 3930463914407274171264037)
                  ·
                    refine ⟨736961983951363907112007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3930463914407274171264037 736961983951363907112007)
                    ·
                      rfl

theorem cell23_4305685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_4305685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305685 prefixEnd_4305685 := by exact prefixLift 4305685
  have htrace : WordTrace (prefixWord ++ tailWord_4305685) baseStart_4305685 baseEnd_4305685 := by
    simpa [prefixWord, tailWord_4305685, baseEnd_4305685] using wordTrace_append hprefix tailTrace_4305685
  have hstable : (prefixWord ++ tailWord_4305685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305685).length < 2 ^ (prefixWord ++ tailWord_4305685).sum := by decide
  have hdescent : baseEnd_4305685 < baseStart_4305685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305688 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_4305688 : Nat := 118140960795 + 4305688 * 2 ^ 59
def prefixEnd_4305688 : Nat := 4983230072969 + 3 ^ 40 * 4305688 * 2
def baseEnd_4305688 : Nat := 2210887492296055209598507

theorem tailTrace_4305688 : CollatzResearch.WordTrace tailWord_4305688 prefixEnd_4305688 2210887492296055209598507 := by
  unfold tailWord_4305688
  simp only [CollatzResearch.WordTrace]
  refine ⟨78520671412617601905534859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104694228550156802540713145 78520671412617601905534859)
  ·
    refine ⟨117781007118926402858302289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78520671412617601905534859 117781007118926402858302289)
    ·
      refine ⟨88335755339194802143726717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117781007118926402858302289 88335755339194802143726717)
      ·
        refine ⟨33125908252198050803897519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88335755339194802143726717 33125908252198050803897519)
        ·
          refine ⟨49688862378297076205846279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33125908252198050803897519 49688862378297076205846279)
          ·
            refine ⟨74533293567445614308769419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49688862378297076205846279 74533293567445614308769419)
            ·
              refine ⟨111799940351168421463154129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74533293567445614308769419 111799940351168421463154129)
              ·
                refine ⟨83849955263376316097365597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111799940351168421463154129 83849955263376316097365597)
                ·
                  refine ⟨31443733223766118536512099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83849955263376316097365597 31443733223766118536512099)
                  ·
                    refine ⟨47165599835649177804768149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31443733223766118536512099 47165599835649177804768149)
                    ·
                      refine ⟨2210887492296055209598507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47165599835649177804768149 2210887492296055209598507)
                      ·
                        rfl

theorem cell23_4305688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_4305688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305688 prefixEnd_4305688 := by exact prefixLift 4305688
  have htrace : WordTrace (prefixWord ++ tailWord_4305688) baseStart_4305688 baseEnd_4305688 := by
    simpa [prefixWord, tailWord_4305688, baseEnd_4305688] using wordTrace_append hprefix tailTrace_4305688
  have hstable : (prefixWord ++ tailWord_4305688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305688).length < 2 ^ (prefixWord ++ tailWord_4305688).sum := by decide
  have hdescent : baseEnd_4305688 < baseStart_4305688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305692 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_4305692 : Nat := 118140960795 + 4305692 * 2 ^ 59
def prefixEnd_4305692 : Nat := 4983230072969 + 3 ^ 40 * 4305692 * 2
def baseEnd_4305692 : Nat := 2210889546218673193948489

theorem tailTrace_4305692 : CollatzResearch.WordTrace tailWord_4305692 prefixEnd_4305692 2210889546218673193948489 := by
  unfold tailWord_4305692
  simp only [CollatzResearch.WordTrace]
  refine ⟨78520744358610356247107665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104694325811480474996143553 78520744358610356247107665)
  ·
    refine ⟨58890558268957767185330749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78520744358610356247107665 58890558268957767185330749)
    ·
      refine ⟨22083959350859162694499031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58890558268957767185330749 22083959350859162694499031)
      ·
        refine ⟨33125939026288744041748547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22083959350859162694499031 33125939026288744041748547)
        ·
          refine ⟨49688908539433116062622821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33125939026288744041748547 49688908539433116062622821)
          ·
            refine ⟨9316670351143709261741779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49688908539433116062622821 9316670351143709261741779)
            ·
              refine ⟨13975005526715563892612669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9316670351143709261741779 13975005526715563892612669)
              ·
                refine ⟨5240627072518336459729751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13975005526715563892612669 5240627072518336459729751)
                ·
                  refine ⟨7860940608777504689594627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5240627072518336459729751 7860940608777504689594627)
                  ·
                    refine ⟨11791410913166257034391941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7860940608777504689594627 11791410913166257034391941)
                    ·
                      refine ⟨2210889546218673193948489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11791410913166257034391941 2210889546218673193948489)
                      ·
                        rfl

theorem cell23_4305692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_4305692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305692 prefixEnd_4305692 := by exact prefixLift 4305692
  have htrace : WordTrace (prefixWord ++ tailWord_4305692) baseStart_4305692 baseEnd_4305692 := by
    simpa [prefixWord, tailWord_4305692, baseEnd_4305692] using wordTrace_append hprefix tailTrace_4305692
  have hstable : (prefixWord ++ tailWord_4305692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305692).length < 2 ^ (prefixWord ++ tailWord_4305692).sum := by decide
  have hdescent : baseEnd_4305692 < baseStart_4305692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305728 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_4305728 : Nat := 118140960795 + 4305728 * 2 ^ 59
def prefixEnd_4305728 : Nat := 4983230072969 + 3 ^ 40 * 4305728 * 2
def baseEnd_4305728 : Nat := 736969343840745017699441

theorem tailTrace_4305728 : CollatzResearch.WordTrace tailWord_4305728 prefixEnd_4305728 736969343840745017699441 := by
  unfold tailWord_4305728
  simp only [CollatzResearch.WordTrace]
  refine ⟨78521400872545145321262919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104695201163393527095017225 78521400872545145321262919)
  ·
    refine ⟨117782101308817717981894379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78521400872545145321262919 117782101308817717981894379)
    ·
      refine ⟨176673151963226576972841569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117782101308817717981894379 176673151963226576972841569)
      ·
        refine ⟨132504863972419932729631177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176673151963226576972841569 132504863972419932729631177)
        ·
          refine ⟨99378647979314949547223383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132504863972419932729631177 99378647979314949547223383)
          ·
            refine ⟨149067971968972424320835075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99378647979314949547223383 149067971968972424320835075)
            ·
              refine ⟨223601957953458636481252613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149067971968972424320835075 223601957953458636481252613)
              ·
                refine ⟨41925367116273494340234865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 223601957953458636481252613 41925367116273494340234865)
                ·
                  refine ⟨31444025337205120755176149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41925367116273494340234865 31444025337205120755176149)
                  ·
                    refine ⟨736969343840745017699441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31444025337205120755176149 736969343840745017699441)
                    ·
                      rfl

theorem cell23_4305728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_4305728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305728 prefixEnd_4305728 := by exact prefixLift 4305728
  have htrace : WordTrace (prefixWord ++ tailWord_4305728) baseStart_4305728 baseEnd_4305728 := by
    simpa [prefixWord, tailWord_4305728, baseEnd_4305728] using wordTrace_append hprefix tailTrace_4305728
  have hstable : (prefixWord ++ tailWord_4305728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305728).length < 2 ^ (prefixWord ++ tailWord_4305728).sum := by decide
  have hdescent : baseEnd_4305728 < baseStart_4305728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305785 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_4305785 : Nat := 118140960795 + 4305785 * 2 ^ 59
def prefixEnd_4305785 : Nat := 4983230072969 + 3 ^ 40 * 4305785 * 2
def baseEnd_4305785 : Nat := 2210937299919541330085561

theorem tailTrace_4305785 : CollatzResearch.WordTrace tailWord_4305785 prefixEnd_4305785 2210937299919541330085561 := by
  unfold tailWord_4305785
  simp only [CollatzResearch.WordTrace]
  refine ⟨157044880705883789377350809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104696587137255859584900539 157044880705883789377350809)
  ·
    refine ⟨117783660529412842033013107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157044880705883789377350809 117783660529412842033013107)
    ·
      refine ⟨176675490794119263049519661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117783660529412842033013107 176675490794119263049519661)
      ·
        refine ⟨66253309047794723643569873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176675490794119263049519661 66253309047794723643569873)
        ·
          refine ⟨49689981785846042732677405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66253309047794723643569873 49689981785846042732677405)
          ·
            refine ⟨18633743169692266024754027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49689981785846042732677405 18633743169692266024754027)
            ·
              refine ⟨27950614754538399037131041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18633743169692266024754027 27950614754538399037131041)
              ·
                refine ⟨20962961065903799277848281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27950614754538399037131041 20962961065903799277848281)
                ·
                  refine ⟨15722220799427849458386211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20962961065903799277848281 15722220799427849458386211)
                  ·
                    refine ⟨23583331199141774187579317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15722220799427849458386211 23583331199141774187579317)
                    ·
                      refine ⟨2210937299919541330085561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23583331199141774187579317 2210937299919541330085561)
                      ·
                        rfl

theorem cell23_4305785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_4305785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305785 prefixEnd_4305785 := by exact prefixLift 4305785
  have htrace : WordTrace (prefixWord ++ tailWord_4305785) baseStart_4305785 baseEnd_4305785 := by
    simpa [prefixWord, tailWord_4305785, baseEnd_4305785] using wordTrace_append hprefix tailTrace_4305785
  have hstable : (prefixWord ++ tailWord_4305785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305785).length < 2 ^ (prefixWord ++ tailWord_4305785).sum := by decide
  have hdescent : baseEnd_4305785 < baseStart_4305785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305799 : List Nat := [1, 1, 4, 2, 3, 2, 1, 2, 1, 4, 2]
def baseStart_4305799 : Nat := 118140960795 + 4305799 * 2 ^ 59
def prefixEnd_4305799 : Nat := 4983230072969 + 3 ^ 40 * 4305799 * 2
def baseEnd_4305799 : Nat := 2210944488648704275310497

theorem tailTrace_4305799 : CollatzResearch.WordTrace tailWord_4305799 prefixEnd_4305799 2210944488648704275310497 := by
  unfold tailWord_4305799
  simp only [CollatzResearch.WordTrace]
  refine ⟨157045391327833069768360451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104696927551888713178906967 157045391327833069768360451)
  ·
    refine ⟨235568086991749604652540677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157045391327833069768360451 235568086991749604652540677)
    ·
      refine ⟨44169016310953050872351377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235568086991749604652540677 44169016310953050872351377)
      ·
        refine ⟨33126762233214788154263533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44169016310953050872351377 33126762233214788154263533)
        ·
          refine ⟨12422535837455545557848825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33126762233214788154263533 12422535837455545557848825)
          ·
            refine ⟨9316901878091659168386619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12422535837455545557848825 9316901878091659168386619)
            ·
              refine ⟨13975352817137488752579929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9316901878091659168386619 13975352817137488752579929)
              ·
                refine ⟨10481514612853116564434947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13975352817137488752579929 10481514612853116564434947)
                ·
                  refine ⟨15722271919279674846652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10481514612853116564434947 15722271919279674846652421)
                  ·
                    refine ⟨2947925984864939033747329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15722271919279674846652421 2947925984864939033747329)
                    ·
                      refine ⟨2210944488648704275310497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2947925984864939033747329 2210944488648704275310497)
                      ·
                        rfl

theorem cell23_4305799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_4305799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305799 prefixEnd_4305799 := by exact prefixLift 4305799
  have htrace : WordTrace (prefixWord ++ tailWord_4305799) baseStart_4305799 baseEnd_4305799 := by
    simpa [prefixWord, tailWord_4305799, baseEnd_4305799] using wordTrace_append hprefix tailTrace_4305799
  have hstable : (prefixWord ++ tailWord_4305799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305799).length < 2 ^ (prefixWord ++ tailWord_4305799).sum := by decide
  have hdescent : baseEnd_4305799 < baseStart_4305799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305802 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4305802 : Nat := 118140960795 + 4305802 * 2 ^ 59
def prefixEnd_4305802 : Nat := 4983230072969 + 3 ^ 40 * 4305802 * 2
def baseEnd_4305802 : Nat := 2210946029090667763572983

theorem tailTrace_4305802 : CollatzResearch.WordTrace tailWord_4305802 prefixEnd_4305802 2210946029090667763572983 := by
  unfold tailWord_4305802
  simp only [CollatzResearch.WordTrace]
  refine ⟨39261375186705550320179915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104697000497881467520479773 39261375186705550320179915)
  ·
    refine ⟨58892062780058325480269873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39261375186705550320179915 58892062780058325480269873)
    ·
      refine ⟨44169047085043744110202405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58892062780058325480269873 44169047085043744110202405)
      ·
        refine ⟨8281696328445702020662951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44169047085043744110202405 8281696328445702020662951)
        ·
          refine ⟨12422544492668553030994427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8281696328445702020662951 12422544492668553030994427)
          ·
            refine ⟨18633816739002829546491641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12422544492668553030994427 18633816739002829546491641)
            ·
              refine ⟨13975362554252122159868731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18633816739002829546491641 13975362554252122159868731)
              ·
                refine ⟨20963043831378183239803097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13975362554252122159868731 20963043831378183239803097)
                ·
                  refine ⟨15722282873533637429852323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20963043831378183239803097 15722282873533637429852323)
                  ·
                    refine ⟨23583424310300456144778485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15722282873533637429852323 23583424310300456144778485)
                    ·
                      refine ⟨2210946029090667763572983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23583424310300456144778485 2210946029090667763572983)
                      ·
                        rfl

theorem cell23_4305802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4305802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305802 prefixEnd_4305802 := by exact prefixLift 4305802
  have htrace : WordTrace (prefixWord ++ tailWord_4305802) baseStart_4305802 baseEnd_4305802 := by
    simpa [prefixWord, tailWord_4305802, baseEnd_4305802] using wordTrace_append hprefix tailTrace_4305802
  have hstable : (prefixWord ++ tailWord_4305802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305802).length < 2 ^ (prefixWord ++ tailWord_4305802).sum := by decide
  have hdescent : baseEnd_4305802 < baseStart_4305802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4305812 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4305812 : Nat := 118140960795 + 4305812 * 2 ^ 59
def prefixEnd_4305812 : Nat := 4983230072969 + 3 ^ 40 * 4305812 * 2
def baseEnd_4305812 : Nat := 2210951163897212724447937

theorem tailTrace_4305812 : CollatzResearch.WordTrace tailWord_4305812 prefixEnd_4305812 2210951163897212724447937 := by
  unfold tailWord_4305812
  simp only [CollatzResearch.WordTrace]
  refine ⟨78522932738392986494291845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104697243651190648659055793 78522932738392986494291845)
  ·
    refine ⟨14723049888448684967679721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78522932738392986494291845 14723049888448684967679721)
    ·
      refine ⟨11042287416336513725759791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14723049888448684967679721 11042287416336513725759791)
      ·
        refine ⟨16563431124504770588639687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11042287416336513725759791 16563431124504770588639687)
        ·
          refine ⟨24845146686757155882959531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16563431124504770588639687 24845146686757155882959531)
          ·
            refine ⟨37267720030135733824439297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24845146686757155882959531 37267720030135733824439297)
            ·
              refine ⟨27950790022601800368329473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37267720030135733824439297 27950790022601800368329473)
              ·
                refine ⟨20963092516951350276247105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27950790022601800368329473 20963092516951350276247105)
                ·
                  refine ⟨15722319387713512707185329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20963092516951350276247105 15722319387713512707185329)
                  ·
                    refine ⟨11791739540785134530388997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15722319387713512707185329 11791739540785134530388997)
                    ·
                      refine ⟨2210951163897212724447937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11791739540785134530388997 2210951163897212724447937)
                      ·
                        rfl

theorem cell23_4305812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4305812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4305812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4305812 prefixEnd_4305812 := by exact prefixLift 4305812
  have htrace : WordTrace (prefixWord ++ tailWord_4305812) baseStart_4305812 baseEnd_4305812 := by
    simpa [prefixWord, tailWord_4305812, baseEnd_4305812] using wordTrace_append hprefix tailTrace_4305812
  have hstable : (prefixWord ++ tailWord_4305812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4305812).length < 2 ^ (prefixWord ++ tailWord_4305812).sum := by decide
  have hdescent : baseEnd_4305812 < baseStart_4305812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4305812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
